-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
import .products
import .types

open categories
open categories.functor
open categories.products
open categories.types

namespace categories.opposites

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]

def op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ` := op C

instance Opposite : category (Cᵒᵖ) := 
{ Hom      := λ X Y : C, Y ⟶ X,
  compose  := λ _ _ _ f g, g ≫ f,
  identity := λ X, 𝟙 X,
  left_identity  := by obviously',
  right_identity := by obviously',
  associativity  := by obviously' }

definition OppositeFunctor (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) := 
{ onObjects     := λ X, F X,
  onMorphisms   := λ X Y f, F &> f,
  identities    := by obviously',
  functoriality := by obviously' }

definition HomPairing (C : Type (u₁+1)) [category C]: Functor.{u₁ u₁} (Cᵒᵖ × C) (Type u₁) := 
{ onObjects     := λ p, @category.Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  identities    := by obviously',
  functoriality := by obviously' }

-- PROJECT prove C^op^op is C
-- definition OppositeOpposite (C : Category) : Equivalence (Opposite (Opposite C)) C := sorry
-- PROJECT opposites preserve products, functors, slices.

@[simp,ematch] lemma ContravariantFunctor.functoriality
  (F : (Cᵒᵖ) ↝ D)
  (X Y Z : (Cᵒᵖ))
  (f : X ⟶ Y) (g : Y ⟶ Z) :
    F &> ((@categories.category.compose C _ _ _ _ g f) : X ⟶ Z) = (F &> f) ≫ (F &> g) := 
    begin
    -- `obviously'` says:
    dsimp_all',
    perform_nth_rewrite_lhs [Functor.functoriality_lemma] 0 -- this breaks if replaced with rw
    end

@[simp,ematch] lemma ContravariantFunctor.identities
  (F : (Cᵒᵖ) ↝ D) (X : (Cᵒᵖ)) : (F &> (@categories.category.identity.{u₁} C _ X)) = 𝟙 (F X) :=
  begin
    -- `obviously'` says:
  dsimp_all',
  perform_nth_rewrite_lhs [Functor.identities_lemma] 0 -- this breaks if replaced with rw
  end

end categories.opposites