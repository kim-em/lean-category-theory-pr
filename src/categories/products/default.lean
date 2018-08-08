-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..functor_categories

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section
variables (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D]

/--
`product_category C D` gives the cartesian product of two categories.
-/
instance product_category : category.{(max u₁ u₂) (max v₁ v₂)} (C × D) := 
{ Hom     := λ X Y, ((X.1) ⟶ (Y.1)) × ((X.2) ⟶ (Y.2)),
  id      := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
  comp    := λ _ _ _ f g, (f.1 ≫ g.1, f.2 ≫ g.2),
  id_comp := begin  /- `obviously'` says: -/ intros, cases X, cases Y, cases f, dsimp at *, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, cases X, cases Y, cases f, dsimp at *, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, cases W, cases X, cases Y, cases Z, cases f, cases g, cases h, dsimp at *, simp end }     
end 

namespace product_category

section -- rfl lemmas for product_category
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma id (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := rfl
@[simp,ematch] lemma comp {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := rfl
end

section 
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (D : Type u₁) [𝒟 : category.{u₁ v₁} D]
include 𝒞 𝒟

/-- 
`product_category.uniform C D` is an additional instance specialised so both factors have the same universe levels. This helps typeclass resolution.
-/
instance uniform : category.{u₁ v₁} (C × D) := category_theory.product_category C D
end

-- Next we define the natural functors into and out of product categories. For now this doesn't address the universal properties.

/-- `right_injection_at C Z` is the functor `X ↦ (X, Z)`. -/
definition right_injection_at (C : Type u₁) [category.{u₁ v₁} C] {D : Type u₁} [category.{u₁ v₁} D] (Z : D) : C ↝ (C × D) := 
{ obj      := λ X, (X, Z),
  map      := λ X Y f, (f, 𝟙 Z),
  map_id   := begin /- `obviously'` says: -/ intros, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, dsimp, simp end }

/-- `left_injection_at Z D` is the functor `X ↦ (Z, X)`. -/
definition left_injection_at {C : Type u₁} [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : D ↝ (C × D) := 
{ obj      := λ X, (Z, X),
  map      := λ X Y f, (𝟙 Z, f),
  map_id   := begin /- `obviously'` says: -/ intros, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, dsimp, simp end }

/-- `left_projection` is the functor `(X, Y) ↦ X`. -/
definition left_projection (C : Type u₁) [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : (C × D) ↝ C := 
{ obj      := λ X, X.1,
  map      := λ X Y f, f.1,
  map_id   := begin /- `obviously'` says: -/ intros, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, refl end }

/-- `right_projection` is the functor `(X, Y) ↦ Y`. -/
definition right_projection (C : Type u₁) [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : (C × D) ↝ D := 
{ obj      := λ X, X.2,
  map      := λ X Y f, f.2,
  map_id   := begin /- `obviously'` says: -/ intros, refl end,
  map_comp := begin /- `obviously'` says: -/ intros, refl end }

end product_category

variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A] {B : Type u₂} [ℬ : category.{u₂ v₂} B] {C : Type u₃} [𝒞 : category.{u₃ v₃} C] {D : Type u₄} [𝒟 : category.{u₄ v₄} D]
include 𝒜 ℬ 𝒞 𝒟

namespace functor
/-- The cartesion product of two functors. -/
definition product (F : A ↝ B) (G : C ↝ D) : (A × C) ↝ (B × D) :=
{ obj := λ X, (F X.1, G X.2),
  map := λ _ _ f, (F.map f.1, G.map f.2),
  map_id   := begin /- `obviously'` says: -/ intros, cases X, dsimp, rw map_id_lemma, rw map_id_lemma end,
  map_comp := begin /- `obviously'` says: -/ intros, cases Z, cases Y, cases X, cases f, cases g, dsimp at *, rw map_comp_lemma, rw map_comp_lemma end }

notation F `×` G := product F G

@[simp,ematch] lemma product_obj   (F : A ↝ B) (G : C ↝ D) (a : A) (c : C) : (F × G) (a, c) = (F a, G c) := rfl
@[simp,ematch] lemma product_map (F : A ↝ B) (G : C ↝ D) {a a' : A} {c c' : C} (f : (a, c) ⟶ (a', c')) : (F × G).map f = (F.map f.1, G.map f.2) := rfl
end functor

namespace nat_trans

/-- The cartesian product of two natural transformations. -/
definition product {F G : A ↝ B} {H I : C ↝ D} (α : F ⟹ G) (β : H ⟹ I) : (F × H) ⟹ (G × I) :=
{ app        := λ X, (α X.1, β X.2),
  naturality := begin /- `obviously'` says: -/ intros, cases f, cases Y, cases X, dsimp at *, simp, split, rw naturality_lemma, rw naturality_lemma end }

notation α `×` β := product α β

@[simp,ematch] lemma product_app {F G : A ↝ B} {H I : C ↝ D} (α : F ⟹ G) (β : H ⟹ I) (a : A) (c : C) : (α × β) (a, c) = (α a, β c) := rfl
end nat_trans

end category_theory