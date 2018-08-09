-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.natural_transformation
import ..isomorphism

namespace category_theory

universes u v w

instance types : large_category (Type u) :=
{ Hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f,
  id_comp := begin /- `obviously'` says: -/ intros, refl  end,
  comp_id := begin /- `obviously'` says: -/ intros, refl end,
  assoc   := begin /- `obviously'` says: -/ intros, refl end }

@[simp] lemma types_Hom {α β : Type u} : (α ⟶ β) = (α → β) := rfl  
@[simp] lemma types_id {α : Type u} (a : α) : (𝟙 α : α → α) a = a := rfl
@[simp] lemma types_comp {α β γ : Type u} (f : α → β) (g : β → γ) (a : α) : (((f : α ⟶ β) ≫ (g : β ⟶ γ)) : α ⟶ γ) a = g (f a) := rfl

namespace functor_to_types
variables {C : Type (v+1)} [large_category C] (F G H : C ↝ (Type u)) {X Y Z : C} 
variables (σ : F ⟹ G) (τ : G ⟹ H) 

@[simp,ematch] lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : F X) : (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
begin 
  -- `obviously'` says:
  simp,
end

@[simp,ematch] lemma map_id (a : F X) : (F.map (𝟙 X)) a = a := 
begin
  -- `obviously'` says:
  simp,
end

@[ematch] lemma naturality (f : X ⟶ Y) (x : F X) : σ Y ((F.map f) x) = (G.map f) (σ X x) := 
begin 
  have p := σ.naturality_lemma f,
  exact congr_fun p x,
end.

@[simp] lemma vcomp (x : F X) : (σ ⊟ τ) X x = τ X (σ X x) := rfl
 
variables {D : Type (w+1)} [large_category D] (I J : D ↝ C) (ρ : I ⟹ J) {W : D}
@[simp] lemma hcomp (x : (I ⋙ F) W) : (ρ ◫ σ) W x = (G.map (ρ W)) (σ (I W) x) := rfl
end functor_to_types

definition type_lift : (Type u) ↝ (Type (max u v)) := 
{ obj      := λ X, ulift.{v} X,
  map      := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down),
  map_id   := begin /- `obviously'` says: -/ intros, apply funext, intros, apply ulift.ext, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, refl end }

end category_theory