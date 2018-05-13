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

instance ulift_small (α : Type u₁) : small (ulift.{u₁+1 u₁} α) := 
{ model := α, 
  smallness := { to_fun    := ulift.down,
                 inv_fun   := ulift.up,
                 left_inv  := sorry,
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

notation `𝟙ₛ` X : 16 := category.identity (up X)   -- type as \b1
notation X ` ⟶ ` Y : 9 := category.Hom (up X) (up Y)    -- type as \h

namespace functor

structure small_Functor (C : Type (u₁+1)) [small_category C] (D : Type (u₂+1)) [category D] : Type ((max u₁ u₂)+1) :=
  (onSmallObjects     : small.model C → D)
  (onSmallMorphisms   : Π {X Y : small.model C}, (X ⟶ Y) → ((onSmallObjects X) ⟶ (onSmallObjects Y)))
  (identities'    : ∀ (X : small.model C), onSmallMorphisms (𝟙ₛ X) = 𝟙 (onSmallObjects X) . obviously)
  (functoriality' : ∀ {X Y Z : small.model C} (f : X ⟶ Y) (g : Y ⟶ Z), onSmallMorphisms (f ≫ g) = (onSmallMorphisms f) ≫ (onSmallMorphisms g) . obviously)

infixr ` ↝ₛ `:70 := small_Functor -- type as \lea 

section
variables {C : Type (u₁+1)} [small_category C] {D : Type (u₂+1)} [category D] (F : C ↝ₛ D)
def small_Functor.onObjects   (X : C) := F.onSmallObjects (down X)
def small_Functor.onMorphisms {X Y : C} (f : X ⟶ Y) : F.onObjects X ⟶ F.onObjects Y := F.onSmallMorphisms (small_hom f)

@[simp,ematch] lemma small_Functor.identities (X : C) : F.onMorphisms (𝟙 X) = 𝟙 (F.onObjects X) := sorry
@[simp,ematch] lemma small_Functor.functoriality {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : F.onMorphisms (f ≫ g) = (F.onMorphisms f) ≫ (F.onMorphisms g) := sorry

@[simp,ematch] lemma small_Functor.h_identities (X Y : C) (p : X = Y) : F.onMorphisms (h_identity p) = h_identity (congr_arg F.onObjects p) :=
begin
  induction p,
  tidy,
end

end

infixr ` +>ₛ `:69 := small_Functor.onObjects
infixr ` &>ₛ `:69 := small_Functor.onMorphisms -- switch to ▹?

variables {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] 

def small_Functor.up (F : C ↝ₛ D) : C ↝ D :=
{ onObjects := λ X, F +>ₛ X,
  onMorphisms := λ X Y f, F &>ₛ f, }

@[simp] lemma small_Functor.up.onObjects   (F : C ↝ₛ D) (X : C) : F.up +> X = F +>ₛ X := by refl
@[simp] lemma small_Functor.up.onMorphisms (F : C ↝ₛ D) {X Y : C} (f : X ⟶ Y) : F.up &> f = F &>ₛ f := by refl

def Functor.down (F : C ↝ D) : C ↝ₛ D :=
{ onSmallObjects := λ X, F +> (up X),
  onSmallMorphisms := λ _ _ f, F &> f, }

@[simp] lemma Functor.down.onObjects   (F : C ↝ D) (X : C) : F.down +>ₛ X = F +> X := sorry
@[simp] lemma Functor.down.onMorphisms (F : C ↝ D) {X Y : C} (f : X ⟶ Y) : F.down &>ₛ f = F &> (small_hom f) := by refl

def Functor.down_up_to_id (F : C ↝ D) : F.down.up ⟹ F := sorry
def Functor.id_to_down_up (F : C ↝ D) : F ⟹ F.down.up := sorry


end functor
 
namespace natural_transformation

section
variables {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D]

structure small_NaturalTransformation (F G : C ↝ₛ D) : Type u₁ :=
  (small_components : Π X : small.model C, (F.onSmallObjects X) ⟶ (G.onSmallObjects X))
  (naturality'      : ∀ {X Y : small.model C} (f : X ⟶ Y), (F.onSmallMorphisms f) ≫ (small_components Y) = (small_components X) ≫ (G.onSmallMorphisms f) . obviously)

infixr ` ⟹ₛ `:50  := small_NaturalTransformation             -- type as \==>

variables {F G : C ↝ₛ D} 

def small_NaturalTransformation.components (τ : F ⟹ₛ G) (X : C) : (F +>ₛ X) ⟶ (G +>ₛ X) := τ.small_components (down X)
@[ematch] def small_NaturalTransformation.naturality (τ : F ⟹ₛ G) {X Y : C} (f : X ⟶ Y) : (F &>ₛ f) ≫ (τ.components Y) = (τ.components X) ≫ (G &>ₛ f) := sorry
end

@[applicable] lemma small_NaturalTransformations_componentwise_equal
  {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D)
  (α β : F ⟹ₛ G)
  (w : ∀ X : C, α.components X = β.components X) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components := sorry,
    subst hc
  end

def small_NaturalTransformation.up {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] {F G : C ↝ₛ D} (α : F ⟹ₛ G) : F.up ⟹ G.up :=
{ components := λ X, α.components X, }

def NaturalTransformation.down {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] {F G : C ↝ D} (α : F ⟹ G) : F.down ⟹ₛ G.down :=
{ small_components := λ X, α.components (up X), }

def small_NaturalTransformation_equiv {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D) : equiv (F.up ⟹ G.up) (F ⟹ₛ G) :=
{ to_fun    := sorry,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry, }

def small_NaturalTransformation_equiv' {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ D) : equiv (F ⟹ G) (F.down ⟹ₛ G.down) := sorry

end natural_transformation


end categories