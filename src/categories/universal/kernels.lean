-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances

open category_theory
open category_theory.initial

namespace category_theory.universal

universes u v w

section
variables {C : Type u} [𝒞 : category.{u v} C] [has_ZeroObject.{u v} C]
include 𝒞

variables {X Y : C}

structure Kernel (f : X ⟶ Y) :=
  (kernel        : C)
  (inclusion     : kernel ⟶ X)
  (map           : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = zero_morphism Z Y), Z ⟶ kernel)
  (witness       : inclusion ≫ f = zero_morphism kernel Y . obviously)
  (factorisation : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = zero_morphism Z Y), (map k w) ≫ inclusion = k . obviously)
  (uniqueness    : ∀ {Z : C} (a b : Z ⟶ kernel) (witness : a ≫ inclusion = b ≫ inclusion), a = b . obviously)

def Kernel_to_Equalizer (f : X ⟶ Y) (kernel : Kernel f) : Equalizer f (zero_morphism X Y) :=
{ equalizer := kernel.kernel,
  inclusion := kernel.inclusion,
  map       := λ Z k w, kernel.map k begin simp [zero_morphism_left] at w, exact w, end,  -- TODO why do we need to specify zero_morphism_left explicitly here? Isn't it a simp lemma?
  witness := sorry, -- FIXME
  factorisation := sorry,
  uniqueness := sorry }

structure Cokernel (f : X ⟶ Y) :=
  (cokernel      : C)
  (projection    : Y ⟶ cokernel)
  (map           : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = zero_morphism X Z), cokernel ⟶ Z)
  (witness       : f ≫ projection = zero_morphism X cokernel . obviously)
  (factorisation : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = zero_morphism X Z), projection ≫ (map k w) = k . obviously)
  (uniqueness    : ∀ {Z : C} (a b : cokernel ⟶ Z) (witness : projection ≫ a = projection ≫ b), a = b . obviously)

def Cokernel_to_Coequalizer (f : X ⟶ Y) (cokernel : Cokernel f) : Coequalizer f (zero_morphism X Y) :=
{ coequalizer := cokernel.cokernel,
  projection  := cokernel.projection,
  map         := λ Z k w, cokernel.map k begin simp at w, exact w, end,
  witness     := sorry, -- FIXME
  factorisation := sorry,
  uniqueness  := sorry }


-- TODO Kernels_are_unique, from Equalizers_are_unique

def Kernels_are_Equalizers (f : X ⟶ Y) (equalizer : Equalizer f (zero_morphism X Y)) (kernel : Kernel f) : equalizer.equalizer ≅ kernel.kernel := sorry -- prove this by uniqueness of equalizers and the above

variables (C)

class has_Kernels :=
  (kernel : Π {X Y : C} (f : X ⟶ Y), Kernel f)
class has_Cokernels :=
  (cokernel : Π {X Y : C} (f : X ⟶ Y), Cokernel f)

variables {C}

def kernel [has_Kernels.{u v} C] {X Y : C} (f : X ⟶ Y) := has_Kernels.kernel f
def kernel_object [has_Kernels.{u v} C] {X Y : C} (f : X ⟶ Y) : C := (kernel f).kernel
def cokernel [has_Cokernels.{u v} C] {X Y : C} (f : X ⟶ Y) := has_Cokernels.cokernel f
def cokernel_object [has_Cokernels.{u v} C] {X Y : C} (f : X ⟶ Y) : C := (cokernel f).cokernel

end
end category_theory.universal

