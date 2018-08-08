-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_transformation
import ..isomorphism

open category_theory

namespace category_theory.types

universes u v w

instance CategoryOfTypes : large_category (Type u) :=
{ Hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f,
  id_comp := begin /- `obviously'` says: -/ intros, refl  end,
  comp_id := begin /- `obviously'` says: -/ intros, refl end,
  assoc   := begin /- `obviously'` says: -/ intros, refl end }

@[simp] lemma Types.Hom {α β : Type u} : (α ⟶ β) = (α → β) := rfl  
@[simp] lemma Types.identity {α : Type u} (a : α) : (𝟙 α : α → α) a = a := rfl
@[simp] lemma Types.compose {α β γ : Type u} (f : α → β) (g : β → γ) (a : α) : (((f : α ⟶ β) ≫ (g : β ⟶ γ)) : α ⟶ γ) a = g (f a) := rfl

variables {C : Type (v+1)} [large_category C] (F G H : C ↝ (Type u)) {X Y Z : C} 
variables (σ : F ⟹ G) (τ : G ⟹ H) 

@[simp,ematch] lemma Functor_to_Types.functoriality (f : X ⟶ Y) (g : Y ⟶ Z) (a : F X) : (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
begin 
  -- `obviously'` says:
  simp,
end

@[simp,ematch] lemma Functor_to_Types.identities (a : F X) : (F.map (𝟙 X)) a = a := 
begin
  -- `obviously'` says:
  simp,
end

@[ematch] lemma Functor_to_Types.naturality (f : X ⟶ Y) (x : F X) : σ Y ((F.map f) x) = (G.map f) (σ X x) := 
begin 
  have p := σ.naturality_lemma f,
  exact congr_fun p x,
end.

@[simp] lemma Functor_to_Types.vertical_composition (x : F X) : (σ ⊟ τ) X x = τ X (σ X x) :=
begin 
  -- `obviously'` says:
  refl
end  
 
variables {D : Type (w+1)} [large_category D] (I J : D ↝ C) (ρ : I ⟹ J) {W : D}
@[simp] lemma Functor_to_Types.horizontal_composition (x : (I ⋙ F) W) : (ρ ◫ σ) W x = (G.map (ρ W)) (σ (I W) x) := rfl

def UniverseLift : (Type u) ↝ (Type (max u v)) := 
{ obj      := λ X, ulift.{v} X,
  map      := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down),
  map_id   := begin /- `obviously'` says: -/ intros, apply funext, intros, apply ulift.ext, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, refl end }

end category_theory.types