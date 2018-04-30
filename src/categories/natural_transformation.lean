-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .functor

open categories
open categories.functor

namespace categories.natural_transformation

universes u v w
variable {C : Type (u+1)}
variable [category C]
variable {D : Type (v+1)}
variable [category D]
variable {E : Type (w+1)}
variable [category E]

structure NaturalTransformation (F G : C ↝ D) : Type /- ((max u v)+1) -/ (max (u+1) v) :=
  (components: Π X : C, (F +> X) ⟶ (G +> X))
  (naturality: ∀ {X Y : C} (f : X ⟶ Y), (F &> f) ≫ (components Y) = (components X) ≫ (G &> f) . obviously)

make_lemma NaturalTransformation.naturality
attribute [ematch] NaturalTransformation.naturality_lemma

infixr ` ⟹ `:50  := NaturalTransformation             -- type as \==>

variables {F G H : C ↝ D}

-- Unfortunately this coercion is not reliable enough to be usable.
-- This defines a coercion so we can write `α X` for `components α X`.
-- instance NaturalTransformation_to_components : has_coe_to_fun (NaturalTransformation F G) :=
-- {F   := λ f, Π X : C, (F +> X) ⟶ (G +> X),
--   coe := NaturalTransformation.components}

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[applicable] lemma NaturalTransformations_componentwise_equal
  (α β : F ⟹ G)
  (w : ∀ X : C, α.components X = β.components X) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components := funext w,
    subst hc
  end

definition IdentityNaturalTransformation (F : C ↝ D) : F ⟹ F := 
{ components := λ X, 𝟙 (F +> X),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp
                end }

instance (F : C ↝ D) : has_one (F ⟹ F) := 
{ one := IdentityNaturalTransformation F }

@[simp] lemma Functor.one.components (F : C ↝ D) (X : C) : (1 : F ⟹ F).components X = 𝟙 (F +> X) := by refl

@[reducible] definition vertical_composition_of_NaturalTransformations (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H := 
{ components := λ X, (α.components X) ≫ (β.components X),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp,
                  erw [←category.associativity_lemma, NaturalTransformation.naturality_lemma, category.associativity_lemma, ←NaturalTransformation.naturality_lemma]
                end }

notation α `⊟` β:80 := vertical_composition_of_NaturalTransformations α β

open categories.functor

@[reducible] definition horizontal_composition_of_NaturalTransformations
  {F G : C ↝ D}
  {H I : D ↝ E}
  (α : F ⟹ G)
  (β : H ⟹ I) : (F ⋙ H) ⟹ (G ⋙ I) :=
{ components := λ X : C, (β.components (F +> X)) ≫ (I &> (α.components X)), 
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  simp,
                  -- Actually, obviously doesn't use exactly this sequence of rewrites, but achieves the same result
                  rw [← category.associativity_lemma],
                  rw [NaturalTransformation.naturality_lemma],
                  rw [category.associativity_lemma],
                  conv { to_rhs, rw [← Functor.functoriality_lemma] },
                  rw [← α.naturality_lemma],
                  rw [Functor.functoriality_lemma],
                end }

notation α `◫` β:80 := horizontal_composition_of_NaturalTransformations α β

@[ematch] lemma NaturalTransformation.exchange
  {F G H : C ↝ D}
  {I J K : D ↝ E}
  (α : F ⟹ G) (β : G ⟹ H) (γ : I ⟹ J) (δ : J ⟹ K) : ((α ⊟ β) ◫ (γ ⊟ δ)) = ((α ◫ γ) ⊟ (β ◫ δ)) := 
  begin
  -- obviously',
    -- `obviously'` says:
    apply categories.natural_transformation.NaturalTransformations_componentwise_equal,
    intros,
    dsimp,
    simp,
    -- again, this isn't actually what obviously says, but it achieves the same effect.
    conv {to_lhs, congr, skip, rw [←category.associativity_lemma] },
    rw [←NaturalTransformation.naturality_lemma],
    rw [category.associativity_lemma],
  end

end categories.natural_transformation