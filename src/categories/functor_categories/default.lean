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

instance small_small_FunctorCategory (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [small_category D] : small_category.{u₁} (small_Functor C D) := 
{ 
  Hom            := λ F G, F ⟹ₛ G,
  identity       := λ F, { small_components := λ X, 𝟙 _ },
  compose        := λ _ _ _ α β, { small_components := λ X, (α.small_components X) ≫ (β.small_components X), naturality' := sorry }, }

instance small_FunctorCategory (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : category.{u₁} (small_Functor C D) := 
{ Hom            := λ F G, F ⟹ₛ G,
  identity       := λ F, { small_components := λ X, 𝟙 _ },
  compose        := λ _ _ _ α β, { small_components := λ X, (α.small_components X) ≫ (β.small_components X), naturality' := sorry }, }

instance large_FunctorCategory (C : Type (u₁+1)) [category C] (D : Type (u₁+1)) [category D] : small_category.{u₁+1} (ulift.{u₁+2} (Functor C D)) := 
{ Hom            := λ F G, F.down ⟹ G.down,
  identity       := λ F, sorry,
  compose        := λ _ _ _ α β, sorry, }


section
variables {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [small_category D] {E : Type (u₁+1)} [category E]

@[simp,ematch] lemma FunctorCategory.identity.components (F : C ↝ₛ D) (X : C) : (𝟙 F : F ⟶ F).components X = 𝟙 (F +>ₛ X) := by refl
@[simp,ematch] lemma FunctorCategory.compose.components {F G H : C ↝ₛ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟶ H).components X = (α : F ⟶ G).components X ≫ (β : G ⟶ H).components X:= by refl

@[ematch] lemma NaturalTransformation_to_FunctorCategory.components_naturality
  {F G : C ↝ₛ (D ↝ₛ E)} (T : F ⟹ₛ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
    : ((F +>ₛ X) &>ₛ f) ≫ ((T.components X).components Z) =
    ((T.components X).components Y) ≫ ((G +>ₛ X) &>ₛ f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma NaturalTransformation_to_FunctorCategory.naturality_components
  {F G : C ↝ₛ (D ↝ₛ E)} (T : F ⟹ₛ G) (Z : D) {X Y : C} (f : X ⟶ Y)
  : ((F &>ₛ f).components Z) ≫ ((T.components Y).components Z) =
    ((T.components X).components Z) ≫ ((G &>ₛ f).components Z) :=
begin
  have p := (T.naturality f),
  -- obviously', -- says:
  injections_and_clear,
  simp only [funext_simp] at *,
  solve_by_elim {discharger := `[cc]}
end
end

end categories.functor_categories
