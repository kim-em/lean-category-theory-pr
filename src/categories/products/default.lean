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

section
variable (C : Type u₁)
variable [category.{u₁ v₁} C]
variable (D : Type u₂)
variable [category.{u₂ v₂} D]

instance ProductCategory : category.{(max u₁ u₂) (max v₁ v₂)} (C × D) := 
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
end 

instance ProductCategory'   (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₁) [category.{u₁ v₁} D] : category.{u₁ v₁} (C × D) := products.ProductCategory C D

section
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp] lemma ProductCategory.identity {X : C} {Y : D} : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := by refl
@[simp] lemma ProductCategory.compose {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := by refl
end

definition RightInjectionAt (C : Type u₁) [category.{u₁ v₁} C] {D : Type u₁} [category.{u₁ v₁} D] (Z : D) : C ↝ (C × D) := 
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

definition LeftInjectionAt {C : Type u₁} [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : D ↝ (C × D) := 
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

definition LeftProjection (C : Type u₁) [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : (C × D) ↝ C := 
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

definition RightProjection (C : Type u₁) [category.{u₁ v₁} C] (Z : C) (D : Type u₁) [category.{u₁ v₁} D] : (C × D) ↝ D := 
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

section
variables {A : Type u₁}
 [𝒜 : category.{u₁ v₁} A]
 {B : Type u₂}
 [ℬ : category.{u₂ v₂} B]
 {C : Type u₃}
 [𝒞 : category.{u₃ v₃} C]
 {D : Type u₄}
 [𝒟 : category.{u₄ v₄} D]
include 𝒜 ℬ 𝒞 𝒟

definition ProductFunctor
 (F : A ↝ B) (G : C ↝ D) : (A × C) ↝ (B × D) :=
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

@[simp,ematch] lemma ProductFunctor.onObjects   (F : A ↝ B) (G : C ↝ D) (a : A) (c : C) : (F × G) +> (a, c) = (F +> a, G +> c) := by refl
@[simp,ematch] lemma ProductFunctor.onMorphisms (F : A ↝ B) (G : C ↝ D) {a a' : A} {c c' : C} (f : (a, c) ⟶ (a', c')) : (F × G).onMorphisms f = (F &> f.1, G &> f.2) := by refl

definition ProductNaturalTransformation 
{F G : A ↝ B} {H I : C ↝ D} (α : F ⟹ G) (β : H ⟹ I) : (F × H) ⟹ (G × I) :=
{ components := λ X, (α.components X.1, β.components X.2),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  cases f, cases Y, cases X,
                  dsimp,
                  dsimp at *,
                  simp,
                  dsimp,
                  fsplit,
                  erw [NaturalTransformation.naturality_lemma],
                  erw [NaturalTransformation.naturality_lemma]
                end }

notation α `×` β := ProductNaturalTransformation α β
end

end categories.products