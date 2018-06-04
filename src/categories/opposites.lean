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

universes u₁ v₁ u₂ v₂

def op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ` := op C

section
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

instance Opposite : category.{u₁ v₁} (Cᵒᵖ) := 
{ Hom            := λ X Y : C, Y ⟶ X,
  compose        := λ _ _ _ f g, g ≫ f,
  identity       := λ X, 𝟙 X,
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      simp
                    end }

variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition OppositeFunctor (F : C ↝ D) : (Cᵒᵖ) ↝ (Dᵒᵖ) := 
{ onObjects     := λ X, F.onObjects X, -- notation (F +> X) fails here, because C ≠ Cᵒᵖ
  onMorphisms   := λ X Y f, F &> f,
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     erw [Functor.identities_lemma], refl,
                   end,
  functoriality := begin
                     -- `obviously'` says: 
                     intros,
                     erw [Functor.functoriality_lemma], refl,
                   end }

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
  (F : (Cᵒᵖ) ↝ D) (X : (Cᵒᵖ)) : (F &> (@categories.category.identity C _ X)) = 𝟙 (F +> X) :=
  begin
    -- `obviously'` says:
    erw [Functor.identities_lemma],
  end
                   
end

definition HomPairing (C : Type u₁) [category.{u₁ v₁} C] : Functor (Cᵒᵖ × C) (Type v₁) := 
{ onObjects     := λ p, @category.Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  identities    := begin
                     -- `obviously'` says: 
                     intros,
                     apply funext,
                     intros,
                     cases X,
                     dsimp,
                     dsimp at *,
                     simp,
                     erw [category.left_identity_lemma],
                   end,
  functoriality := begin
                      -- `obviously'` says:
                      intros,
                      apply funext,
                      intros,
                      cases g, cases f, cases Z, cases Y, cases X,
                      dsimp,
                      dsimp at *,
                      simp,
                      dsimp,
                      erw [category.associativity_lemma]
                   end }

end categories.opposites