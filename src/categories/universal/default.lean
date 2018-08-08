-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .cones

open category_theory
open category_theory.initial

namespace category_theory.universal

/-
We give "explicit" definitions of (co)equalizers, and (finite) (co)products. Of course these are special cases of (co)limits,
but they are used so pervasively that they need a convenient interface.

TODO: pullbacks and pushouts should be here too.
-/

universes u v w
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y : C}

structure Equalizer (f g : X ⟶ Y) :=
(equalizer     : C)
(inclusion     : equalizer ⟶ X)
(map           : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), Z ⟶ equalizer)
(witness       : inclusion ≫ f = inclusion ≫ g . obviously')
(factorisation : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), (map k w) ≫ inclusion = k . obviously')
(uniqueness    : ∀ {Z : C} (a b : Z ⟶ equalizer) (witness : a ≫ inclusion = b ≫ inclusion), a = b . obviously')

restate_axiom Equalizer.witness
restate_axiom Equalizer.factorisation
restate_axiom Equalizer.uniqueness
attribute [simp,ematch] Equalizer.factorisation_lemma
attribute [applicable] Equalizer.inclusion Equalizer.map
attribute [applicable] Equalizer.uniqueness_lemma

structure BinaryProduct (X Y : C) :=
(product             : C)
(left_projection     : product ⟶ X)
(right_projection    : product ⟶ Y)
(map                 : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), Z ⟶ product)
(left_factorisation  : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ left_projection  = f . obviously') 
(right_factorisation : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ right_projection = g . obviously') 
(uniqueness          : ∀ {Z : C} (f g : Z ⟶ product)
                          (left_witness  : f ≫ left_projection  = g ≫ left_projection )
                          (right_witness : f ≫ right_projection = g ≫ right_projection), f = g . obviously')

restate_axiom BinaryProduct.left_factorisation
restate_axiom BinaryProduct.right_factorisation
restate_axiom BinaryProduct.uniqueness
attribute [simp,ematch] BinaryProduct.left_factorisation_lemma BinaryProduct.right_factorisation_lemma
attribute [applicable] BinaryProduct.left_projection BinaryProduct.right_projection BinaryProduct.map
attribute [applicable] BinaryProduct.uniqueness_lemma

structure Product {I : Type w} (F : I → C) :=
(product       : C)
(projection    : Π i : I, product ⟶ (F i))
(map           : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)), Z ⟶ product)
(factorisation : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)) (i : I), (map f) ≫ (projection i) = f i . obviously')
(uniqueness    : ∀ {Z : C} (f g : Z ⟶ product) (witness : ∀ i : I, f ≫ (projection i) = g ≫ (projection i)), f = g . obviously')

restate_axiom Product.factorisation
restate_axiom Product.uniqueness
attribute [simp,ematch] Product.factorisation_lemma
attribute [applicable] Product.projection Product.map
attribute [applicable] Product.uniqueness_lemma

structure Coequalizer (f g : X ⟶ Y) :=
(coequalizer   : C)
(projection    : Y ⟶ coequalizer)
(map           : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), coequalizer ⟶ Z)
(witness       : f ≫ projection = g ≫ projection . obviously')
(factorisation : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), projection ≫ (map k w) = k . obviously')
(uniqueness    : ∀ {Z : C} (a b : coequalizer ⟶ Z) (witness : projection ≫ a = projection ≫ b), a = b . obviously')

restate_axiom Coequalizer.witness
restate_axiom Coequalizer.factorisation
restate_axiom Coequalizer.uniqueness
attribute [simp,ematch] Coequalizer.factorisation_lemma
attribute [applicable] Coequalizer.projection Coequalizer.map
attribute [applicable] Coequalizer.uniqueness_lemma

structure BinaryCoproduct (X Y : C) :=
(coproduct           : C)
(left_inclusion      : X ⟶ coproduct)
(right_inclusion     : Y ⟶ coproduct)
(map                 : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), coproduct ⟶ Z)
(left_factorisation  : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), left_inclusion ≫ (map f g)  = f . obviously') 
(right_factorisation : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), right_inclusion ≫ (map f g) = g . obviously') 
(uniqueness          : ∀ {Z : C} (f g : coproduct ⟶ Z)
                          (left_witness  : left_inclusion ≫ f = left_inclusion ≫ g)
                          (right_witness : right_inclusion ≫ f = right_inclusion ≫ g), f = g . obviously')

restate_axiom BinaryCoproduct.left_factorisation
restate_axiom BinaryCoproduct.right_factorisation
restate_axiom BinaryCoproduct.uniqueness
attribute [simp,ematch] BinaryCoproduct.left_factorisation_lemma BinaryCoproduct.right_factorisation_lemma
attribute [applicable] BinaryCoproduct.left_inclusion BinaryCoproduct.right_inclusion BinaryCoproduct.map
attribute [applicable] BinaryCoproduct.uniqueness_lemma

structure Coproduct {I : Type w} (X : I → C) :=
(coproduct     : C)
(inclusion     : Π i : I, (X i) ⟶ coproduct)
(map           : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z), coproduct ⟶ Z)
(factorisation : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z) (i : I), (inclusion i) ≫ (map f) = f i . obviously')
(uniqueness    : ∀ {Z : C} (f g : coproduct ⟶ Z) (witness : ∀ i : I, (inclusion i) ≫ f = (inclusion i) ≫ g), f = g . obviously')

restate_axiom Coproduct.factorisation
restate_axiom Coproduct.uniqueness
attribute [simp,ematch] Coproduct.factorisation_lemma
attribute [applicable] Coproduct.inclusion Coproduct.map
attribute [applicable] Coproduct.uniqueness_lemma

structure Pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
(pullback : C)
(h : pullback ⟶ X)
(k : pullback ⟶ Y)
(commutativity : h ≫ f = k ≫ g)
(map : ∀ {P} {h' : P ⟶ X} {k' : P ⟶ Y} (w : h' ≫ f = k' ≫ g), P ⟶ pullback)
(factorisation : ∀ {P} {h' : P ⟶ X} {k' : P ⟶ Y} (w : h' ≫ f = k' ≫ g), (map w ≫ h) = h' ∧ (map w ≫ k) = k')
(uniqueness : ∀ {P} {h' : P ⟶ X} {k' : P ⟶ Y} (w : h' ≫ f = k' ≫ g) (m n : P ⟶ pullback) (w' : (m ≫ h) = h' ∧ (m ≫ k) = k' ∧ (n ≫ h) = h' ∧ (n ≫ k) = k'), m = n)


-- Coming in later PRs: all these things special cases of (co)limits, and hence are unique up to unique isomorphism.

end category_theory.universal

