-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types

namespace categories.universal

universes u v w

section
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

class has_InitialObject :=
  (initial_object : InitialObject C)

class has_BinaryProducts :=
  (binary_product : Π X Y : C, BinaryProduct.{u v} X Y)
class has_FiniteProducts :=
  (product : Π {I : Type w} [fintype I] (f : I → C), Product.{u v w} f)

class has_TerminalObject :=
  (terminal_object : TerminalObject C)

class has_BinaryCoproducts :=
  (binary_coproduct : Π X Y : C, BinaryCoproduct.{u v} X Y)
class has_FiniteCoproducts :=
  (coproduct : Π {I : Type w} [fintype I] (f : I → C), Coproduct.{u v w} f)

class has_Equalizers :=
  (equalizer : Π {X Y : C} (f g : X ⟶ Y), Equalizer f g)
class has_Coequalizers :=
  (coequalizer : Π {X Y : C} (f g : X ⟶ Y), Coequalizer f g)

definition initial_object [has_InitialObject.{u v} C] : C := has_InitialObject.initial_object.{u v} C
definition terminal_object [has_TerminalObject.{u v} C] : C := has_TerminalObject.terminal_object.{u v} C
end

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

definition binary_product [has_BinaryProducts.{u v} C] (X Y : C) := has_BinaryProducts.binary_product.{u v} X Y
definition finite_product [has_FiniteProducts.{u v w} C] {I : Type w} [fin : fintype I] (f : I → C) := @has_FiniteProducts.product.{u v w} C _ _ I fin f

definition binary_coproduct [has_BinaryCoproducts.{u v} C] (X Y : C) := has_BinaryCoproducts.binary_coproduct.{u v} X Y
definition finite_coproduct [has_FiniteCoproducts.{u v w} C] {I : Type w} [fin : fintype I] (f : I → C) := @has_FiniteCoproducts.coproduct.{u v w} C _ _ I fin f

definition equalizer [has_Equalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) := has_Equalizers.equalizer.{u v} f g
definition coequalizer [has_Coequalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) := has_Coequalizers.coequalizer.{u v} f g
end

section

class has_Products (C : Type (u+1)) [large_category C] :=
  (product : Π {I : Type u} (f : I → C), Product.{u+1 u u} f)
class has_Coproducts (C : Type (u+1)) [large_category C] :=
  (coproduct : Π {I : Type u} (f : I → C), Coproduct.{u+1 u u} f)

variables {C : Type (u+1)} [large_category C]

definition product [has_Products C] {I : Type u} (F : I → C) := has_Products.product F
definition coproduct [has_Coproducts C] {I : Type u} (F : I → C) := has_Coproducts.coproduct F
end

end categories.universal

