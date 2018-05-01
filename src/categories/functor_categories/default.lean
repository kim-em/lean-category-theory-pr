-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..natural_transformation

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ v₁ u₂ v₂ u₃ v₃

section
variables (C : Type u₁) [C_cat : uv_category.{u₁ v₁} C] (D : Type u₂) [D_cat : uv_category.{u₂ v₂} D]
include C_cat D_cat

instance FunctorCategory : uv_category (C ↝ D) := 
{ Hom            := λ F G, F ⟹ G,
  identity       := λ F, IdentityNaturalTransformation F,
  compose        := λ _ _ _ α β, α ⊟ β,
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
                      intros,
                      dsimp,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
                      intros,
                      dsimp,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
                      intros,
                      simp
                    end }
end


section
variables {C : Type (u₁+1)} [category C] {D : Type (u₂+1)} [category D] {E : Type (u₃+1)} [category E]

@[simp] lemma FunctorCategory.identity.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F).components X = 𝟙 (F +> X) := by refl
@[simp] lemma FunctorCategory.compose.components {F G H : C ↝ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟹ H).components X = (α : F ⟹ G).components X ≫ (β : G ⟹ H).components X:= by refl

@[ematch] lemma NaturalTransformation_to_FunctorCategory.components_naturality
  {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
    : ((F +> X) &> f) ≫ ((T.components X).components Z) =
    ((T.components X).components Y) ≫ ((G +> X) &> f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma NaturalTransformation_to_FunctorCategory.naturality_components
  {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (Z : D) {X Y : C} (f : X ⟶ Y)
  : ((F &> f).components Z) ≫ ((T.components Y).components Z) =
    ((T.components X).components Z) ≫ ((G &> f).components Z) :=
begin
  have p := (T.naturality f),
  -- obviously', -- says:
  injections_and_clear,
  simp only [funext_simp] at *,
  solve_by_elim `[cc]
end
end

end categories.functor_categories
