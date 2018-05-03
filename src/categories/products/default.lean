-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..functor_categories

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.products

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable (C : Type u₁)
variable [uv_category.{u₁ v₁} C]
variable (D : Type u₂)
variable [uv_category.{u₂ v₂} D]

instance ProductCategory : uv_category.{(max u₁ u₂) (max v₁ v₂)} (C × D) := 
{ Hom            := λ X Y, ((X.1) ⟶ (Y.1)) × ((X.2) ⟶ (Y.2)),
  identity       := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
  compose        := λ _ _ _ f g, (f.1 ≫ g.1, f.2 ≫ g.2),
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      automatic_induction,
                      dsimp,
                      dsimp at *,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      automatic_induction,
                      dsimp,
                      dsimp at *,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      automatic_induction,
                      dsimp,
                      dsimp at *,
                      simp
                    end }

@[simp] lemma ProductCategory.identity 
{C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] {X : C} {Y : D} : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := by refl
@[simp] lemma ProductCategory.compose
{C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := by refl

definition RightInjectionAt {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] (Z : D) : C ↝ (C × D) := 
{ onObjects     := λ X, (X, Z),
  onMorphisms   := λ X Y f, (f, 𝟙 Z),
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     dsimp,
                     simp
                   end }

definition LeftInjectionAt {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] (Z : C) : D ↝ (C × D) := 
{ onObjects     := λ X, (Z, X),
  onMorphisms   := λ X Y f, (𝟙 Z, f),
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     dsimp,
                     simp
                   end }

definition LeftProjection {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] : (C × D) ↝ C := 
{ onObjects     := λ X, X.1,
  onMorphisms   := λ X Y f, f.1,
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

definition RightProjection {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] : (C × D) ↝ D := 
{ onObjects     := λ X, X.2,
  onMorphisms   := λ X Y f, f.2,
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

definition ProductFunctor
{A : Type u₁}
 [uv_category.{u₁ v₁} A]
 {B : Type u₂}
 [uv_category.{u₂ v₂} B]
 {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D] (F : A ↝ B) (G : C ↝ D) : (A × C) ↝ (B × D) :=
{ onObjects     := λ X, (F +> X.1, G +> X.2),
  onMorphisms   := λ _ _ f, (F &> f.1, G &> f.2),
  identities    := begin
                     -- `obviously'` says (something equivalent to):
                     intros,
                     cases X,
                     dsimp,
                     erw Functor.identities_lemma, 
                     erw Functor.identities_lemma,
                     refl,
                   end,
  functoriality := begin
                     -- `obviously'` says (something equivalent to):
                     intros,
                     cases Z, cases Y, cases X,
                     dsimp,
                     cases f, cases g,
                     dsimp,
                     dsimp at *,
                     erw Functor.functoriality_lemma,
                     erw Functor.functoriality_lemma,
                     refl
                   end }

notation F `×` G := ProductFunctor F G

definition ProductNaturalTransformation 
{A : Type u₁}
 [uv_category.{u₁ v₁} A]
 {B : Type u₂}
 [uv_category.{u₂ v₂} B]
 {C : Type u₃}
 [uv_category.{u₃ v₃} C]
 {D : Type u₄}
 [uv_category.{u₄ v₄} D]
{F G : A ↝ B} {H I : C ↝ D} (α : F ⟹ G) (β : H ⟹ I) : (F × H) ⟹ (G × I) :=
{ components := λ X, (α.components X.1, β.components X.2),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  cases f, cases Y, cases X,
                  dsimp,
                  dsimp at *,
                  simp,
                  fsplit,
                  dsimp,
                  erw [←NaturalTransformation.naturality_lemma], refl,
                  dsimp,
                  erw [←NaturalTransformation.naturality_lemma], refl,
                end }

notation α `×` β := ProductNaturalTransformation α β

end categories.products