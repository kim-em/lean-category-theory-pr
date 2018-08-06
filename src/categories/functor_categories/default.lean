-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..natural_transformation

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

instance FunctorCategory (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : category.{(max u₁ v₁ u₂ v₂) (max u₁ v₂)} (C ↝ D) := 
{ Hom            := λ F G, F ⟹ G,
  identity       := λ F, NaturalTransformation.id F,
  compose        := λ _ _ _ α β, α ⊟ β,
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      simp
                    end }

namespace FunctorCategory

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma identity.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F) X = 𝟙 (F +> X) := rfl
@[simp,ematch] lemma compose.components {F G H : C ↝ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟹ H) X = (α : F ⟹ G) X ≫ (β : G ⟹ H) X := rfl
end

section
variables {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D] {E : Type (u₃+1)} [large_category E]
-- TODO Are these used?
@[simp,ematch] lemma large_identity.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F) X = 𝟙 (F +> X) := rfl
@[simp,ematch] lemma large_compose.components {F G H : C ↝ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟹ H) X = (α : F ⟹ G) X ≫ (β : G ⟹ H) X:= rfl

@[ematch] lemma NaturalTransformation_to_FunctorCategory.components_naturality
  {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
    : ((F +> X) &> f) ≫ ((T X) Z) =
    ((T X) Y) ≫ ((G +> X) &> f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma NaturalTransformation_to_FunctorCategory.naturality_components
  {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (Z : D) {X Y : C} (f : X ⟶ Y)
  : ((F &> f) Z) ≫ ((T Y) Z) =
    ((T X) Z) ≫ ((G &> f) Z) :=
begin
  have p := (T.naturality f),
  -- obviously' says:
  injections_and_clear,
  simp only [funext_simp] at *,
  solve_by_elim
end
end

end FunctorCategory
end category_theory
