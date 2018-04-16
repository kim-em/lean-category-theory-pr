-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..category
import ..isomorphism
import ..functor
import ..natural_transformation

namespace categories.types

open categories
open categories.isomorphism
open categories.functor

universes u v w

instance CategoryOfTypes : category (Type u) :=
{ Hom := λ a b, (a → b),
  identity := λ a, id,
  compose  := λ _ _ _ f g, g ∘ f,
  left_identity    := by obviously',
  right_identity   := by obviously',
  associativity    := by obviously' }
  
variables {C : Type (v+1)} [category C] (F G H: Functor C (Type u)) {X Y Z : C} 
variables (σ : F ⟹ G) (τ : G ⟹ H) 

@[simp,ematch] lemma Functor_to_Types.functoriality (f : X ⟶ Y) (g : Y ⟶ Z) (a : F X) : (F &> (f ≫ g)) a = (F &> g) ((F &> f) a) :=
begin 
  -- `obviously'` says:
  simp!,
  refl
end

@[simp,ematch] lemma Functor_to_Types.identities (a : F X) : (F &> (𝟙 X)) a = a := 
begin
  -- `obviously'` says:
  simp!,
  refl
end

@[ematch] lemma Functor_to_Types.naturality (f : X ⟶ Y) (x : F X) : σ.components Y ((F &> f) x) = (G &> f) (σ.components X x) := 
begin 
  have p := σ.naturality_lemma f,
  exact congr_fun p x,
end.

@[simp] lemma Functor_to_Types.vertical_composition (x : F X) : (σ ⊟ τ).components X x = τ.components X (σ.components X x) :=
begin 
  -- `obviously'` says:
  refl
end  
 
variables {D : Type (w+1)} [category D] (I J : D ↝ C) (ρ : I ⟹ J) {W : D}
@[simp] lemma Functor_to_Types.horizontal_composition (x : (I ⋙ F) W) : (ρ ◫ σ).components W x = (G &> ρ.components W) (σ.components (I W) x) := 
begin
  -- `obviously'` says:
  refl
end

definition UniverseLift : Functor (Type u) (Type (u+1)) := 
{ onObjects := λ X, ulift.{u+1} X,
  onMorphisms := λ X Y f, λ x : ulift.{u+1} X, ulift.up (f x.down),
  identities    := by obviously',
  functoriality := by obviously' }

end categories.types