-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..functor_categories
import ..opposites

open categories
open categories.isomorphism

namespace categories.initial

universes u v

structure InitialObject (C : Type u) [category.{u v} C] :=
  (initial_object                              : C)
  (morphism_from_initial_object_to             : ∀ Y : C, initial_object ⟶ Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C, ∀ f g : initial_object ⟶ Y, f = g . obviously)

attribute [applicable] InitialObject.morphism_from_initial_object_to
make_lemma InitialObject.uniqueness_of_morphisms_from_initial_object
attribute [applicable,ematch] InitialObject.uniqueness_of_morphisms_from_initial_object_lemma

structure TerminalObject (C : Type u) [category.{u v} C]  :=
  (terminal_object                            : C)
  (morphism_to_terminal_object_from           : ∀ Y : C, Y ⟶ terminal_object)
  (uniqueness_of_morphisms_to_terminal_object : ∀ Y : C, ∀ f g : Y ⟶ terminal_object, f = g . obviously)

attribute [applicable] TerminalObject.morphism_to_terminal_object_from
make_lemma TerminalObject.uniqueness_of_morphisms_to_terminal_object
attribute [applicable,ematch] TerminalObject.uniqueness_of_morphisms_to_terminal_object_lemma

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance InitialObject_coercion_to_object : has_coe (InitialObject C) C :=
{ coe := InitialObject.initial_object }

structure is_initial (X : C) :=
  (morphism_from_initial_object_to             : ∀ Y : C, X ⟶ Y)
  (uniqueness_of_morphisms_from_initial_object : ∀ Y : C, ∀ f g : X ⟶ Y, f = g)

-- set_option pp.all true
lemma InitialObjects_are_unique (X Y : InitialObject C) : X.initial_object ≅ Y.initial_object :=
begin
  -- `obviously'` says:
  fsplit,
  apply categories.initial.InitialObject.morphism_from_initial_object_to,
  apply categories.initial.InitialObject.morphism_from_initial_object_to,
  apply categories.initial.InitialObject.uniqueness_of_morphisms_from_initial_object_lemma,
  apply categories.initial.InitialObject.uniqueness_of_morphisms_from_initial_object_lemma
end

instance TerminalObject_coercion_to_object : has_coe (TerminalObject C) C :=
{ coe := TerminalObject.terminal_object }

structure is_terminal (X : C) :=
  (morphism_to_terminal_object_from           : ∀ Y : C, Y ⟶ X)
  (uniqueness_of_morphisms_to_terminal_object : ∀ Y : C, ∀ f g : Y ⟶ X, f = g)

lemma TerminalObjects_are_unique (X Y : TerminalObject C) : X.terminal_object ≅ Y.terminal_object :=
begin
  -- `obviously'` says:
  fsplit,
  apply categories.initial.TerminalObject.morphism_to_terminal_object_from,
  apply categories.initial.TerminalObject.morphism_to_terminal_object_from,
  apply categories.initial.TerminalObject.uniqueness_of_morphisms_to_terminal_object_lemma,
  apply categories.initial.TerminalObject.uniqueness_of_morphisms_to_terminal_object_lemma
end
end

class ZeroObject (C : Type u) [category.{u v} C] :=
  (zero_object : C)
  (is_initial  : is_initial.{u v}  zero_object)
  (is_terminal : is_terminal.{u v} zero_object)

definition ZeroObject.zero_morphism {C : Type u} [category.{u v} C] (Z : ZeroObject C) (X Y : C) : X ⟶ Y := (Z.is_terminal.morphism_to_terminal_object_from X) ≫ (Z.is_initial.morphism_from_initial_object_to Y) 

end categories.initial