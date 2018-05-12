-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .heterogeneous_identity
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

@[reducible] def small_hom {C : Type (u₁+1)} [small_category C] {X Y : C} (f : X ⟶ Y) : up (down X) ⟶ up (down Y) := (h_identity (by simp)) ≫ f ≫ (h_identity (by simp))
@[reducible] def large_hom {C : Type (u₁+1)} [small_category C] {X Y : C} (f : up (down X) ⟶ up (down Y)) : X ⟶ Y := (h_identity (by simp)) ≫ f ≫ (h_identity (by simp))

notation `𝟙ₛ` X := category.identity (up X)   -- type as \b1
notation X ` ⟶ₛ ` Y : 10 := category.Hom (up X) (up Y)    -- type as \h

namespace functor

structure small_Functor (C : Type (u₁+1)) [small_category C] (D : Type (u₂+1)) [category D] : Type ((max u₁ u₂)+1) :=
  (onSmallObjects     : small.model C → D)
  (onSmallMorphisms   : Π {X Y : small.model C}, (X ⟶ₛ Y) → ((onSmallObjects X) ⟶ (onSmallObjects Y)))
  (identities'    : ∀ (X : small.model C), onSmallMorphisms (𝟙ₛ X) = 𝟙 (onSmallObjects X) . obviously)
  (functoriality' : ∀ {X Y Z : small.model C} (f : X ⟶ₛ Y) (g : Y ⟶ₛ Z), onSmallMorphisms (f ≫ g) = (onSmallMorphisms f) ≫ (onSmallMorphisms g) . obviously)

infixr ` ↝ₛ `:70 := small_Functor -- type as \lea 

section
variables {C : Type (u₁+1)} [small_category C] {D : Type (u₂+1)} [category D] (F : C ↝ₛ D)
def small_Functor.onObjects   (X : C) := F.onSmallObjects (down X)
def small_Functor.onMorphisms {X Y : C} (f : X ⟶ Y) := F.onSmallMorphisms (small_hom f)

@[simp,ematch] lemma small_Functor.identities (X : C) : F.onMorphisms (𝟙 X) = 𝟙 (F.onObjects X) := sorry
@[simp,ematch] lemma small_Functor.functoriality {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : F.onMorphisms (f ≫ g) = (F.onMorphisms f) ≫ (F.onMorphisms g) := sorry
end

infixr ` +> `:70 := small_Functor.onObjects
infixr ` &> `:70 := small_Functor.onMorphisms -- switch to ▹?

set_option pp.notation false

def small_Functor.up {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ₛ D) : C ↝ D :=
{ onObjects := λ X, F +> X,
  onMorphisms := λ X Y f, F &> f, }

def Functor.down {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F : C ↝ D) : C ↝ₛ D :=
{ onSmallObjects := λ X, F +> (up X),
  onSmallMorphisms := λ _ _ f, F &> f, }

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

section
variables {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D]

structure small_NaturalTransformation (F G : C ↝ₛ D) : Type u₁ :=
  (small_components : Π X : small.model C, (F +> (up X)) ⟶ (G +> (up X)))
  (naturality'      : ∀ {X Y : small.model C} (f : X ⟶ₛ Y), (F &> f) ≫ (small_components Y) = (small_components X) ≫ (G &> f) . obviously)

variables {F G : C ↝ₛ D} 

def small_NaturalTransformation.components (τ : small_NaturalTransformation F G) (X : C) : (F +> X) ⟶ (G +> X) := τ.small_components (down X)

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