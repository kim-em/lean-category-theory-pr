-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .universal
import ..util.finite

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

instance FiniteProducts_give_a_TerminalObject [has_FiniteProducts C] : has_TerminalObject C := {
  terminal_object :=
  let pempty_product := @has_FiniteProducts.product C _ _ pempty _ pempty_function in {
    terminal_object                            := pempty_product.product,
    morphism_to_terminal_object_from           := λ X, pempty_product.map pempty_dependent_function,
    uniqueness_of_morphisms_to_terminal_object := λ X f g, pempty_product.uniqueness f g pempty_dependent_function
 }
}
instance FiniteCoproducts_give_an_InitialObject [has_FiniteCoproducts C] : has_InitialObject C := {
  initial_object :=
  let pempty_coproduct := @has_FiniteCoproducts.coproduct C _ _ pempty _ pempty_function in {
    initial_object                              := pempty_coproduct.coproduct,
    morphism_from_initial_object_to             := λ X, pempty_coproduct.map pempty_dependent_function,
    uniqueness_of_morphisms_from_initial_object := λ X f g, pempty_coproduct.uniqueness f g pempty_dependent_function
 }
}

definition Two.choice {α : Type u} (a b : α) : Two.{v} → α 
| Two._0 := a
| Two._1 := b

definition Two.dependent_choice {α : Type u} {Z : α → Type v} {a b : α} (f : Z a) (g : Z b) : Π i : Two.{u}, Z (Two.choice a b i) 
| Two._0 := f
| Two._1 := g

instance BinaryProducts_from_FiniteProducts [has_FiniteProducts C] : has_BinaryProducts C := {
  binary_product := λ X Y : C,
    let F := Two.choice.{u+1 u+1} X Y in
    let p := @finite_product.{u} C _ _ Two _ F in {
      product             := p.product,
      left_projection     := p.projection Two._0,
      right_projection    := p.projection Two._1,
      map                 := λ _ f g, p.map (Two.dependent_choice f g),
      left_factorisation  := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._0,
      right_factorisation := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._1,
      uniqueness          := λ _ f g u v, p.uniqueness f g (λ X, begin cases X, exact u, exact v, end) 
   }
}

end

-- PROJECT this has become nontrivial, because we're asserting that finite products can be indexed from the same universe level.
-- This requires us to use the fact that `fin n` is in level 0.
-- section
-- variable (C : Type (max (u+1) v))
-- variable [category C]

-- instance FiniteProducts_from_Products [has_Products C] : has_FiniteProducts C := {
--   product := λ _ _ f, has_Products.product f
-- }
-- instance FiniteCoproducts_from_Coproducts [has_Coproducts C] : has_FiniteCoproducts C := {
--   coproduct := λ _ _ f, has_Coproducts.coproduct f
-- }
-- end

-- PROJECT:
-- open nat

-- definition construct_finite_product (C : Category) [has_TerminalObject C] [has_BinaryProducts C]
--   : Π n : nat, Π (I : Type) (fin : Finite I) (p : fin.cardinality = n) (f : I → C.Obj), Product f
-- | 0        := λ {I : Type} [fin : Finite I] (p : fin.cardinality = 0) (f : I → C.Obj), {
--                 product       := terminal_object,
--                 projection    := begin intros, sorry end,
--                 map           := sorry,
--                 factorisation := sorry,
--                 uniqueness    := sorry
--              }
-- | (succ n) := sorry

-- instance FiniteProducts_from_BinaryProducts (C : Category) [has_TerminalObject C] [has_BinaryProducts C] : has_FiniteProducts C := {
--   product := λ {I : Type} [fin : Finite I] (f : I → C.Obj), construct_finite_product C fin.cardinality I fin by obviously f
--}

end categories.universal

