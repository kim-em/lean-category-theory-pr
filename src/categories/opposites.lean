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
{ Hom            := λ X Y : C, Y ⟶ X,
  compose        := λ _ _ _ f g, g ≫ f,
  identity       := λ X, 𝟙 X,
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      simp!
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      simp!
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      simp!
                    end }

definition OppositeFunctor (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) := 
{ onObjects     := λ X, F.onObjects X, -- TODO why is notation not allowed here?
  onMorphisms   := λ X Y f, F &> f,
  identities    := begin
                     -- `obviously'` says: FIXME again, the produced tactic script is incorrect
                     intros,
                     erw [Functor.identities_lemma],
                     trivial,
                   end,
  functoriality := begin
                     -- `obviously'` says: FIXME incorrect tactic script
                     intros,
                     erw [Functor.functoriality_lemma],
                     trivial,
                   end }

definition HomPairing (C : Type (u₁+1)) [category C]: Functor.{u₁ u₁} (Cᵒᵖ × C) (Type u₁) := 
{ onObjects     := λ p, @category.Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  identities    := begin
                     -- `obviously'` says: -- FIXME tactic script broken, omits refl
                     intros,
                     fapply funext,
                     intros,
                     cases X,
                     dsimp,
                     dsimp at *,
                     simp!,
                     erw [category.left_identity_lemma],
                     refl,
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     fapply funext,
                     intros,
                     cases Z, cases Y, cases X,
                     dsimp,
                     dsimp at *,
                     simp!,
                     dsimp,
                     -- TODO do this with conv
                     perform_nth_rewrite_lhs [←category.associativity_lemma] 1,
                     perform_nth_rewrite_lhs [category.associativity_lemma] 0,
                     perform_nth_rewrite_lhs [←category.associativity_lemma] 1,
                     perform_nth_rewrite_lhs [category.associativity_lemma] 0,
                     perform_nth_rewrite_rhs [category.associativity_lemma] 0,
                     perform_nth_rewrite_rhs [←category.associativity_lemma] 2,
                     perform_nth_rewrite_rhs [←category.associativity_lemma] 0,
                   end }

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
      erw [Functor.functoriality_lemma]
    end

@[simp,ematch] lemma ContravariantFunctor.identities
  (F : (Cᵒᵖ) ↝ D) (X : (Cᵒᵖ)) : (F &> (@categories.category.identity.{u₁} C _ X)) = 𝟙 (F +> X) :=
  begin
    -- `obviously'` says:
    erw [Functor.identities_lemma],
  end

end categories.opposites