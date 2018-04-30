-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..natural_transformation
import ..small_category

open categories
open categories.functor
open categories.natural_transformation

namespace categories.functor_categories

universes u₁ u₂ u₃

section
variables (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] (E : Type (u₃+1)) [category E]

instance FunctorCategory : category.{(max (u₁+1) u₂)} (C ↝ D) := 
{ Hom            := λ F G, F ⟹ G,
  identity       := λ F, 1,
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

structure small_Functor (C : Type (u₁+1)) [small C] [category C] (D : Type (u₂+1)) [category D] : Type ((max (u₁+1) u₂)) :=
  (onObjects     : small.model C → D)
  (onMorphisms   : Π {X Y : small.model C}, ((small.smallness C).inv_fun X ⟶ (small.smallness C).inv_fun Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : small.model C), onMorphisms (𝟙 ((small.smallness C).inv_fun X)) = 𝟙 (onObjects X) . obviously)
  -- (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

instance SmallFunctorCategory [small C] : small.{(max (u₁+1) u₂)} (C ↝ D) := 
{ model := small_Functor C D,
  smallness := sorry
}

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
