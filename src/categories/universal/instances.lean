-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal

open category_theory
open category_theory.initial

namespace category_theory.universal

universes u v w

section
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

class has_InitialObject :=
  (initial_object : initial_object C)

class has_BinaryProducts :=
  (binary_product : Π X Y : C, BinaryProduct.{u v} X Y)
class has_FiniteProducts :=
  (product : Π {I : Type w} [fintype I] (f : I → C), Product.{u v w} f)

class has_TerminalObject :=
  (terminal_object : terminal_object C)

class has_BinaryCoproducts :=
  (binary_coproduct : Π X Y : C, BinaryCoproduct.{u v} X Y)
class has_FiniteCoproducts :=
  (coproduct : Π {I : Type w} [fintype I] (f : I → C), Coproduct.{u v w} f)

class has_ZeroObject :=
  (zero_object : zero_object C)

class has_Equalizers :=
  (equalizer : Π {X Y : C} (f g : X ⟶ Y), Equalizer f g)
class has_Coequalizers :=
  (coequalizer : Π {X Y : C} (f g : X ⟶ Y), Coequalizer f g)

def zero_object [has_ZeroObject.{u v} C] : C := has_ZeroObject.zero_object.{u v} C
def initial_object [has_InitialObject.{u v} C] : C := has_InitialObject.initial_object.{u v} C
def terminal_object [has_TerminalObject.{u v} C] : C := has_TerminalObject.terminal_object.{u v} C
end

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section
variable [has_ZeroObject.{u v} C]
def zero_morphism (X Y : C) := ZeroObject.zero_morphism (has_ZeroObject.zero_object.{u v} C) X Y -- TODO provide a has_zero instance?

@[simp] lemma zero_morphism_left  {X Y Z : C} (f : Y ⟶ Z) : (zero_morphism X Y) ≫ f = zero_morphism X Z :=
begin
  -- TODO such a yucky proof
  unfold zero_morphism,
  unfold ZeroObject.zero_morphism,
  rw category.assoc,
  congr,
  apply ((has_ZeroObject.zero_object.{u v} C).is_initial).uniqueness,
end
@[simp] lemma zero_morphism_right {X Y Z : C} (f : X ⟶ Y) : f ≫ (zero_morphism Y Z) = zero_morphism X Z :=  
begin
 -- TODO such a yucky proof
  unfold zero_morphism,
  unfold ZeroObject.zero_morphism,
  rw ← category.assoc,
  congr,
  apply ((has_ZeroObject.zero_object.{u v} C).is_terminal).uniqueness,
end
end

def binary_product [has_BinaryProducts.{u v} C] (X Y : C) := has_BinaryProducts.binary_product.{u v} X Y
def finite_product [has_FiniteProducts.{u v w} C] {I : Type w} [fin : fintype I] (f : I → C) := @has_FiniteProducts.product.{u v w} C _ _ I fin f

def binary_coproduct [has_BinaryCoproducts.{u v} C] (X Y : C) := has_BinaryCoproducts.binary_coproduct.{u v} X Y
def finite_coproduct [has_FiniteCoproducts.{u v w} C] {I : Type w} [fin : fintype I] (f : I → C) := @has_FiniteCoproducts.coproduct.{u v w} C _ _ I fin f

def equalizer [has_Equalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) := has_Equalizers.equalizer.{u v} f g
def coequalizer [has_Coequalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) := has_Coequalizers.coequalizer.{u v} f g
end

section

class has_Products (C : Type (u+1)) [large_category C] :=
  (product : Π {I : Type u} (f : I → C), Product.{u+1 u u} f)
class has_Coproducts (C : Type (u+1)) [large_category C] :=
  (coproduct : Π {I : Type u} (f : I → C), Coproduct.{u+1 u u} f)

variables {C : Type (u+1)} [large_category C]

def product [has_Products C] {I : Type u} (F : I → C) := has_Products.product F
def coproduct [has_Coproducts C] {I : Type u} (F : I → C) := has_Coproducts.coproduct F
end

end category_theory.universal

