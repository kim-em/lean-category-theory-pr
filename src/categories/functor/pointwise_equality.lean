-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..functor
import ..heterogeneous_identity
import ..small_category

open categories
namespace categories.functor

universes u₁ u₂

@[applicable] lemma Functors_pointwise_equal (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] (F G : C ↝ D)
  (ho : ∀ X : C, F +> X = G +> X)
  (hm : ∀ X Y : C, ∀ f : X ⟶ Y, F &> f = h_identity (ho X) ≫ (G &> f) ≫ h_identity (ho Y).symm) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  have h_objects : F_onObjects = G_onObjects, exact funext ho,
  subst h_objects,
  have h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  have p := hm X Y f,
  simp at p,
  exact p,
  subst h_morphisms
end

@[applicable] lemma small_Functors_pointwise_equal (C : Type (u₁+1)) [small_category C] (D : Type (u₂+1)) [category D] (F G : C ↝ₛ D)
  (ho : ∀ X : C, F +>ₛ X = G +>ₛ X)
  (hm : ∀ X Y : C, ∀ f : X ⟶ Y, F &>ₛ f = h_identity (ho X) ≫ (G &>ₛ f) ≫ h_identity (ho Y).symm) : F = G :=
begin
  induction F with F_onSmallObjects F_onSmallMorphisms,
  induction G with G_onSmallObjects G_onSmallMorphisms,
  have h_objects : F_onSmallObjects = G_onSmallObjects, sorry,
  subst h_objects,
  have h_morphisms : @F_onSmallMorphisms = @G_onSmallMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  have p := hm (up X) (up Y) f,
  sorry,
  subst h_morphisms,
end

local attribute [reducible] function.left_inverse function.right_inverse

def small_Functor_equiv (C : Type (u₁+1)) [small_category C] (D : Type (u₁+1)) [category D] : equiv (C ↝ D) (C ↝ₛ D) :=
by refine
{ to_fun    := λ F, F.down,
  inv_fun   := λ F, F.up, 
  .. } ; obviously

end categories.functor