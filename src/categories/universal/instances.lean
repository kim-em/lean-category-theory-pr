-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal
import categories.util.finite

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types
open categories.util.finite

namespace categories.universal

universes u v w

section
variable (C : Type (u+1))
variable [category C]

class has_InitialObject :=
  (initial_object : InitialObject C)

class has_BinaryProducts :=
  (binary_product : Π X Y : C, BinaryProduct X Y)
class has_FiniteProducts :=
  (product : Π {I : Type (u+1)} [fintype I] (f : I → C), Product f)

class has_TerminalObject :=
  (terminal_object : TerminalObject C)

class has_BinaryCoproducts :=
  (binary_coproduct : Π X Y : C, BinaryCoproduct X Y)
class has_FiniteCoproducts :=
  (coproduct : Π {I : Type (u+1)} [fintype I] (f : I → C), Coproduct f)

class has_Equalizers :=
  (equalizer : Π {X Y : C} (f g : X ⟶ Y), Equalizer f g)
class has_Coequalizers :=
  (coequalizer : Π {X Y : C} (f g : X ⟶ Y), Coequalizer f g)

definition initial_object [has_InitialObject C] : C := has_InitialObject.initial_object C
definition terminal_object [has_TerminalObject C] : C := has_TerminalObject.terminal_object C
end

section
variable {C : Type (u+1)}
variable [category C]

definition binary_product [has_BinaryProducts C] (X Y : C) := has_BinaryProducts.binary_product X Y
definition finite_product [has_FiniteProducts C] {I : Type (u+1)} [fin : fintype I] (f : I → C) := @has_FiniteProducts.product C _ _ I fin f

definition binary_coproduct [has_BinaryCoproducts C] (X Y : C) := has_BinaryCoproducts.binary_coproduct X Y
definition finite_coproduct [has_FiniteCoproducts C] {I : Type (u+1)} [fin : fintype I] (f : I → C) := @has_FiniteCoproducts.coproduct C _ _ I fin f

definition equalizer [has_Equalizers C] {X Y : C} (f g : X ⟶ Y) := has_Equalizers.equalizer f g
definition coequalizer [has_Coequalizers C] {X Y : C} (f g : X ⟶ Y) := has_Coequalizers.coequalizer f g
end

section
variable (C : Type (u+1))
variable [category C]

class has_Products :=
  (product : Π {I : Type u} (f : I → C), Product f)
class has_Coproducts :=
  (coproduct : Π {I : Type u} (f : I → C), Coproduct f)
end

section
variable {C : Type (u+1)}
variable [category C]

definition product [has_Products C] {I : Type u} (F : I → C) := has_Products.product F
definition coproduct [has_Coproducts C] {I : Type u} (F : I → C) := has_Coproducts.coproduct F
end

end categories.universal

