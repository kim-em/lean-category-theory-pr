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

section
variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma ProductCategory.identity (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := by refl
@[simp,ematch] lemma ProductCategory.compose {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := by refl
end

section
variable (C : Type u₁)
variable [𝒞 : category.{u₁ v₁} C]
variable (D : Type u₁)
variable [𝒟 : category.{u₁ v₁} D]
include 𝒞 𝒟

instance ProductCategory_uniform : category.{u₁ v₁} (C × D) := products.ProductCategory C D

-- TOOD these are probably unnecessary
@[simp,ematch] lemma ProductCategory_uniform.identity (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := by refl
@[simp,ematch] lemma ProductCategory_uniform.compose {P Q R : C} {S T U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := by refl
end

section
variables (C : Type u₁) [small_category C] (D : Type u₁) [small_category D] (E : Type u₂) [ℰ : category.{u₂ v₂} E]
include ℰ


lemma test (X : C) (Y : D) (F : C ↝ (D ↝ E)): (F &> (@category.identity (C × D) (products.ProductCategory_uniform C D) (X, Y)).fst) Y = 𝟙 ((F +> X) +> Y) := 
begin
unfold_coes,
-- rewrite ProductCategory_uniform.identity,
let P := @coe_fn (F +> @prod.fst C D (X, Y) ⟶ F +> @prod.fst C D (X, Y))
  (@natural_transformation.has_coe_to_fun D _inst_2 E ℰ (F +> @prod.fst C D (X, Y)) (F +> @prod.fst C D (X, Y))),

let Q := @congr_arg (@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y)) (F +> @prod.fst C D (X, Y) ⟶ F +> @prod.fst C D (X, Y))
  (@prod.fst (@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y)) (@prod.snd C D (X, Y) ⟶ @prod.snd C D (X, Y))
     (𝟙 (X, Y)))
  (@prod.fst (@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y)) (@prod.snd C D (X, Y) ⟶ @prod.snd C D (X, Y))
     (𝟙 X, 𝟙 Y))
  (@Functor.onMorphisms C _inst_1 (D ↝ E) (@functor_categories.FunctorCategory D _inst_2 E ℰ) F
     (@prod.fst C D (X, Y))
     (@prod.fst C D (X, Y)))
  (@congr_arg ((@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y)) × (@prod.snd C D (X, Y) ⟶ @prod.snd C D (X, Y)))
     (@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y))
     (𝟙 (X, Y))
     (𝟙 X, 𝟙 Y)
     (@prod.fst (@prod.fst C D (X, Y) ⟶ @prod.fst C D (X, Y)) (@prod.snd C D (X, Y) ⟶ @prod.snd C D (X, Y)))
     (@eq.rec ((X, Y) ⟶ (X, Y)) (𝟙 (X, Y)) (λ (_a : (X, Y) ⟶ (X, Y)), 𝟙 (X, Y) = _a)
        (@eq.refl ((X, Y) ⟶ (X, Y)) (𝟙 (X, Y)))
        (𝟙 X, 𝟙 Y)
        (@ProductCategory_uniform.identity C _inst_1 D _inst_2 X Y))),

dsimp [has_coe_to_fun.F] at P, 

let Z := congr_arg P Q,
dsimp [P] at Z,
-- rw Z,
perform_nth_rewrite [ProductCategory_uniform.identity] 0,
rewrite ProductCategory_uniform.identity,
end
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
{ components := λ X, (α X.1, β X.2),
  naturality := begin
                  -- `obviously'` says:
                  intros,
                  cases f, cases Y, cases X,
                  dsimp,
                  dsimp at *,
                  simp,
                  dsimp,
                  fsplit,
                  unfold_coes,
                  erw [NaturalTransformation.naturality_lemma],
                  unfold_coes,
                  erw [NaturalTransformation.naturality_lemma],
                end }

notation α `×` β := ProductNaturalTransformation α β
end

end categories.products