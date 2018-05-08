-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import tidy.congr_struct
import data.fintype

namespace categories

universes u₁ u₂

class small (C : Type (u₁+1)) :=
(model : Type u₁)
(smallness : equiv C model)

instance (α : Type u₁) : small (ulift.{u₁+1 u₁} α) := 
{ model := α, 
  smallness := { to_fun := ulift.down,
                 inv_fun := ulift.up,
                 left_inv := sorry,
                 right_inv := sorry } }

-- PROJECT: seems hard without choice
-- instance (α : Type (u+1)) [fintype α] : small α := 

-- PROJECT: tactics for deriving instances of small, e.g. `small pempty`!

class small_category (C : Type (u₁+1)) extends category C, small C.

def down {C : Type (u₁+1)} [small C] (X : C)             := (small.smallness C).to_fun  X
def up   {C : Type (u₁+1)} [small C] (X : small.model C) := (small.smallness C).inv_fun X

@[simp,ematch] lemma up_down {C : Type (u₁+1)} [small C] (X : C)             : up (down X) = X := (small.smallness C).left_inv X
@[simp,ematch] lemma down_up {C : Type (u₁+1)} [small C] (X : small.model C) : down (up X) = X := (small.smallness C).right_inv X

notation `𝟙ₛ` X := category.identity (up X)   -- type as \b1
notation X ` ⟶ₛ ` Y : 10 := category.Hom (up X) (up Y)    -- type as \h

namespace functor

structure small_Functor (C : Type (u₁+1)) [small_category C] (D : Type (u₂+1)) [category D] : Type ((max u₁ u₂)+1) :=
  (onObjects     : small.model C → D)
  (onMorphisms   : Π {X Y : small.model C}, (X ⟶ₛ Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : small.model C), onMorphisms (𝟙ₛ X) = 𝟙 (onObjects X) . obviously)
  (functoriality : ∀ {X Y Z : small.model C} (f : X ⟶ₛ Y) (g : Y ⟶ₛ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma small_Functor.identities
make_lemma small_Functor.functoriality
attribute [simp,ematch] small_Functor.functoriality_lemma small_Functor.identities_lemma

infixr ` +>ₛ `:70 := small_Functor.onObjects
infixr ` &>ₛ `:70 := small_Functor.onMorphisms -- switch to ▹?
infixr ` ↝ₛ `:70 := small_Functor -- type as \lea 

@[simp] lemma eq.mpr.trans {α β γ: Prop} (p : α = β) (q : β = γ) (g : γ) : eq.mpr (eq.trans p q) g = eq.mpr p (eq.mpr q g) :=
begin
  induction p,
  induction q,
  refl,
end

@[simp] lemma eq.mpr.propext {α : Sort u₁} (a : α) : eq.mpr (propext (eq_self_iff_true a)) trivial = eq.refl a :=
begin
  refl,
end

@[simp] lemma eq.mpr.refl {α : Sort u₁} (a b : α) (p : a = b) : (eq.mpr (congr_fun (congr_arg eq p) b) (eq.refl b)) = p :=
begin
  induction p,
  refl,
end

def h_identity {C : Type (u₁+1)} [category C] {X Y : C} (p : X = Y) : X ⟶ Y :=
begin
  rw p,
  exact 𝟙 Y,
end

@[simp,ematch] lemma h_identity.refl {C : Type (u₁+1)} [category C] (X : C) : h_identity (eq.refl X) = 𝟙 X :=
begin
  refl,
end

@[simp,ematch] lemma h_identity.trans {C : Type (u₁+1)} [category C] {X Y Z : C} (p : X = Y) (q : Y = Z) : h_identity p ≫ h_identity q = h_identity (p.trans q) :=
begin
  induction p,
  induction q,
  tidy,
end

@[reducible] def small_hom {C : Type (u₁+1)} [small_category C] {X Y : C} (f : X ⟶ Y) : up (down X) ⟶ up (down Y) := (h_identity (by simp)) ≫ f ≫ (h_identity (by simp))

def small_Functor.up {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ₛ D) : C ↝ D :=
{ onObjects := λ X, F +>ₛ (down X),
  onMorphisms := λ X Y f, F &>ₛ (small_hom f), }

def Functor.down {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ D) : C ↝ₛ D :=
{ onObjects := λ X, F +> (up X),
  onMorphisms := λ _ _ f, F &> f, }

def Functor.down_up_to_id {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ D) : F.down.up ⟹ F := sorry
def Functor.id_to_down_up {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ D) : F ⟹ F.down.up := sorry

@[applicable] lemma Functors_pointwise_equal (C : Type (u₁+1)) [category C] (D : Type (u₁+1)) [category D] (F G : C ↝ D)
  (ho : ∀ X : C, F +> X = G +> X)
  (hm : ∀ X Y : C, ∀ f : X ⟶ Y, F &> f = h_identity (ho X) ≫ (G &> f) ≫ h_identity (ho Y).symm) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  have h_objects : F_onObjects = G_onObjects, exact funext ho,
  subst h_objects,
  have h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  have p := hm X Y f,
  simp at p,
  exact p,
  subst h_morphisms
end

def small_Functor_equiv (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : equiv (C ↝ D) (C ↝ₛ D) :=
{ to_fun  := λ F, F.down,
  inv_fun := λ F, F.up,
  left_inv := sorry,
  right_inv := sorry, }

end functor
 
namespace natural_transformation

structure small_NaturalTransformation {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D) : Type u₁ :=
  (components: Π X : small.model C, (F +>ₛ X) ⟶ (G +>ₛ X))
  (naturality: ∀ {X Y : small.model C} (f : X ⟶ₛ Y), (F &>ₛ f) ≫ (components Y) = (components X) ≫ (G &>ₛ f) . obviously)

make_lemma small_NaturalTransformation.naturality
attribute [ematch] small_NaturalTransformation.naturality_lemma

infixr ` ⟹ₛ `:50  := small_NaturalTransformation             -- type as \==>

@[applicable] lemma small_NaturalTransformations_componentwise_equal
  {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D)
  (α β : F ⟹ₛ G)
  (w : ∀ X : small.model C, α.components X = β.components X) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components := funext w,
    subst hc
  end


def small_NaturalTransformation.up {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] {F G : C ↝ₛ D} (α : F ⟹ₛ G) : F.up ⟹ G.up :=
{ components := λ X, α.components (down X), }

def NaturalTransformation.down {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] {F G : C ↝ D} (α : F ⟹ G) : F.down ⟹ₛ G.down :=
{ components := λ X, α.components (up X), }

def small_NaturalTransformation_equiv {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D) : equiv (F.up ⟹ G.up) (F ⟹ₛ G) :=
{ to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry, }

def small_NaturalTransformation_equiv' {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ D) : equiv (F ⟹ G) (F.down ⟹ₛ G.down) :=

end natural_transformation


end categories