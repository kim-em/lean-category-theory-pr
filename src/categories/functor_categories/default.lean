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
variables (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D]

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
end

section

structure small_Functor (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : Type (u₁+1) :=
  (onObjects     : small.model C → D)
  (onMorphisms   : Π {X Y : small.model C}, (X ⟶ₛ Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : small.model C), onMorphisms (𝟙ₛ X) = 𝟙 (onObjects X) . obviously)
  (functoriality : ∀ {X Y Z : small.model C} (f : X ⟶ₛ Y) (g : Y ⟶ₛ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma small_Functor.identities
make_lemma small_Functor.functoriality
attribute [simp,ematch] small_Functor.functoriality_lemma small_Functor.identities_lemma

infixr ` +>ₛ `:70 := small_Functor.onObjects
infixr ` &>ₛ `:70 := small_Functor.onMorphisms -- switch to ▹?
infixr ` ↝ₛ `:70 := small_Functor -- type as \lea 

def small_Functor_equiv (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : equiv (C ↝ D) (C ↝ₛ D) :=
{ to_fun  := λ F,
    { onObjects := λ X, F +> (small.up X),
      onMorphisms := λ _ _ f, F &> f, },
  inv_fun := λ F,
    { onObjects := λ X, F +>ₛ (small.down X),
      onMorphisms := λ _ _ f, F &>ₛ f, },
  left_inv := sorry,
  right_inv := sorry, }

structure small_NaturalTransformation {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D) : Type u₁ :=
  (components: Π X : small.model C, (F +>ₛ X) ⟶ (G +>ₛ X))
  (naturality: ∀ {X Y : small.model C} (f : X ⟶ₛ Y), (F &>ₛ f) ≫ (components Y) = (components X) ≫ (G &>ₛ f) . obviously)

make_lemma small_NaturalTransformation.naturality
attribute [ematch] small_NaturalTransformation.naturality_lemma

infixr ` ⟹ₛ `:50  := small_NaturalTransformation             -- type as \==>

def small_NaturalTransformation_equiv {C : Type (u₁+1)} [small_category C] {D : Type (u₁+1)} [category D] (F G : C ↝ₛ D) : equiv (((small_Functor_equiv C D).inv_fun F) ⟹ ((small_Functor_equiv C D).inv_fun G)) (F ⟹ₛ G) :=
{ to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry, }

instance small_FunctorCategory (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : category.{u₁} (small_Functor C D) := 
{ Hom            := λ F G, F ⟹ₛ G,
  identity       := λ F, 1,
  compose        := λ _ _ _ α β, α ⊟ β,
}
end


section
variables {C : Type (u₁+1)} [category C] {D : Type (u₂+1)} [category D] {E : Type (u₃+1)} [category E]

@[simp,ematch] lemma FunctorCategory.identity.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F).components X = 𝟙 (F +> X) := by refl
@[simp,ematch] lemma FunctorCategory.compose.components {F G H : C ↝ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟹ H).components X = (α : F ⟹ G).components X ≫ (β : G ⟹ H).components X:= by refl

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
