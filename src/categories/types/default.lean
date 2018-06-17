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

instance CategoryOfTypes : large_category (Type u) :=
{ Hom            := λ a b, (a → b),
  identity       := λ a, id,
  compose        := λ _ _ _ f g, g ∘ f,
  left_identity  := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  right_identity := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  associativity  := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

@[simp] lemma Types.Hom {α β : Type u} : (α ⟶ β) = (α → β) := by refl  
@[simp] lemma Types.identity {α : Type u} (a : α) : (𝟙 α : α → α) a = a := by refl
@[simp] lemma Types.compose {α β γ : Type u} (f : α → β) (g : β → γ) (a : α) : (((f : α ⟶ β) ≫ (g : β ⟶ γ)) : α ⟶ γ) a = g (f a) := by refl

variables {C : Type (v+1)} [large_category C] (F G H : C ↝ (Type u)) {X Y Z : C} 
variables (σ : F ⟹ G) (τ : G ⟹ H) 

@[simp,ematch] lemma Functor_to_Types.functoriality (f : X ⟶ Y) (g : Y ⟶ Z) (a : F +> X) : (F &> (f ≫ g)) a = (F &> g) ((F &> f) a) :=
begin 
  -- `obviously'` says:
  simp,
end

@[simp,ematch] lemma Functor_to_Types.identities (a : F +> X) : (F &> (𝟙 X)) a = a := 
begin
  -- `obviously'` says:
  simp,
end

@[ematch] lemma Functor_to_Types.naturality (f : X ⟶ Y) (x : F +> X) : σ.components Y ((F &> f) x) = (G &> f) (σ.components X x) := 
begin 
  have p := σ.naturality_lemma f,
  exact congr_fun p x,
end.

@[simp] lemma Functor_to_Types.vertical_composition (x : F +> X) : (σ ⊟ τ).components X x = τ.components X (σ.components X x) :=
begin 
  -- `obviously'` says:
  refl
end  
 
variables {D : Type (w+1)} [large_category D] (I J : D ↝ C) (ρ : I ⟹ J) {W : D}
@[simp] lemma Functor_to_Types.horizontal_composition (x : (I ⋙ F) +> W) : (ρ ◫ σ).components W x = (G &> ρ.components W) (σ.components (I +> W) x) := 
begin
  -- `obviously'` says:
  refl
end

definition UniverseLift : (Type u) ↝ (Type (max u v)) := 
{ onObjects     := λ X, ulift.{v} X,
  onMorphisms   := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down),
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     apply funext,
                     intros,
                     apply ulift.ext,
                     refl
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

end categories.types