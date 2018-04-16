-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.universal.instances
import categories.util.Two

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types

universes u v

namespace categories.universal

variable {C : Type (u+1)}
variable [category C]

instance TerminalObject_from_FiniteProducts [has_FiniteProducts C] : has_TerminalObject C := 
{ terminal_object :=
  let pempty_product := @has_FiniteProducts.product C _ _ pempty _ pempty_function in 
  { terminal_object                            := pempty_product.product,
    morphism_to_terminal_object_from           := λ X, pempty_product.map pempty_dependent_function,
    uniqueness_of_morphisms_to_terminal_object := λ X f g, pempty_product.uniqueness f g pempty_dependent_function } }
    
instance InitialObject_from_FiniteCoproducts [has_FiniteCoproducts C] : has_InitialObject C := 
{ initial_object :=
  let pempty_coproduct := @has_FiniteCoproducts.coproduct C _ _ pempty _ pempty_function in 
  { initial_object                              := pempty_coproduct.coproduct,
    morphism_from_initial_object_to             := λ X, pempty_coproduct.map pempty_dependent_function,
    uniqueness_of_morphisms_from_initial_object := λ X f g, pempty_coproduct.uniqueness f g pempty_dependent_function } }

definition Two.choice {α : Type u} (a b : α) : Two.{v} → α 
| Two._0 := a
| Two._1 := b

definition Two.dependent_choice {α : Type u} {Z : α → Type v} {a b : α} (f : Z a) (g : Z b) : Π i : Two.{u}, Z (Two.choice a b i) 
| Two._0 := f
| Two._1 := g

instance BinaryProducts_from_FiniteProducts [has_FiniteProducts C] : has_BinaryProducts C := 
{ binary_product := λ X Y : C,
    let F := Two.choice.{u+1 u+1} X Y in
    let p := @finite_product.{u} C _ _ Two _ F in 
    { product             := p.product,
      left_projection     := p.projection Two._0,
      right_projection    := p.projection Two._1,
      map                 := λ _ f g, p.map (Two.dependent_choice f g),
      left_factorisation  := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._0,
      right_factorisation := λ _ f g, p.factorisation (Two.dependent_choice f g) Two._1,
      uniqueness          := λ _ f g u v, p.uniqueness f g (λ X, begin cases X, exact u, exact v, end) } }

end categories.universal