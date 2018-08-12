-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism

open category_theory

namespace category_theory.initial

universes u v

structure initial_object (C : Type u) [category.{u v} C] :=
(obj        : C)
(to         : ∀ Y : C, obj ⟶ Y)
(uniqueness : ∀ Y : C, ∀ f g : obj ⟶ Y, f = g . obviously)

attribute [back] initial_object.to
restate_axiom initial_object.uniqueness
attribute [back,ematch] initial_object.uniqueness_lemma

structure terminal_object (C : Type u) [category.{u v} C]  :=
(obj                            : C)
(«from»            : ∀ Y : C, Y ⟶ obj)
(uniqueness : ∀ Y : C, ∀ f g : Y ⟶ obj, f = g . obviously)

attribute [back] terminal_object.«from»
restate_axiom terminal_object.uniqueness
attribute [back,ematch] terminal_object.uniqueness_lemma

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance initial_object_coe : has_coe (initial_object C) C :=
{ coe := initial_object.obj }

structure is_initial (X : C) :=
(to         : ∀ Y : C, X ⟶ Y)
(uniqueness : ∀ Y : C, ∀ f g : X ⟶ Y, f = g)

-- set_option pp.all true
lemma initial_objects_unique (X Y : initial_object C) : X.obj ≅ Y.obj :=
begin
  -- `obviously'` says:
  fsplit,
  apply initial_object.to,
  apply initial_object.to,
  apply initial_object.uniqueness_lemma,
  apply initial_object.uniqueness_lemma
end

instance terminal_object_coe : has_coe (terminal_object C) C :=
{ coe := terminal_object.obj }

structure is_terminal (X : C) :=
(«from»     : ∀ Y : C, Y ⟶ X)
(uniqueness : ∀ Y : C, ∀ f g : Y ⟶ X, f = g)

lemma terminal_objects_unique (X Y : terminal_object C) : X.obj ≅ Y.obj :=
begin
  -- `obviously'` says:
  fsplit,
  apply terminal_object.«from»,
  apply terminal_object.«from»,
  apply terminal_object.uniqueness_lemma,
  apply terminal_object.uniqueness_lemma
end

end 


structure zero_object (C : Type u) [category.{u v} C] :=
(obj         : C)
(is_initial  : is_initial.{u v}  obj)
(is_terminal : is_terminal.{u v} obj)


variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

instance zero_object_coe : has_coe (zero_object C) C :=
{ coe := zero_object.obj }

-- TODO get rid of this
definition ZeroObject.zero_morphism (Z : zero_object C) (X Y : C) : X ⟶ Y := (Z.is_terminal.«from» X) ≫ (Z.is_initial.to Y) 


end category_theory.initial