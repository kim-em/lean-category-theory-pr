-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

/-
This file demonstrates three different ways to handle 'explicit' limits, e.g. (binary) products, equalizers, and pullbacks.
There will of course also be a development of these as special cases of limits (as initial objects in a category of cones).

All three versions use the notions
  `fork`, `square`, and `span`.
On these, we have predicates
  `is_equalizer`, `is_pullback`, and `is_binary_product`.
Finally there are bundled objects
  `equalizer`, `pullback`, and `binary_product`.

There's just one implementation of the 'shapes', but the three approaches differ in their handling of the `is_X` structures.

0) version_0 is as explicit as possible, writing everything out in terms of fields `lift`, `fac`, and `uniq`,
   which respectively show how to lift a map, the factorisation property it has, and the uniqueness of that factorisation.   
1) version_1 uses two fields, `μ` and `u`. `μ` shows how to construct a map from another shape, and `u` expresses
   the uniqueness of this map using the pattern "for all maps from another shape, it factorises correctly if and only if it is the lift".
   (Thanks for Mario for helping with this one.)
2) version_2, closely following [Reid's work](https://github.com/rwbarton/lean-homotopy-theory/blob/lean-3.4.1/src/categories/colimits.lean)
   expresses the universal property by stating that a certain map between hom sets (or products and subsets of such)
   is a bijection. As an example, we can say that a span `Y <--p-- X --q--> Z` is a binary product exactly if for
   every object `X'`, the map `(X' ⟶ X) → (X' ⟶ Y) × (X' ⟶ Z)` given by post-composition by `p` and `q` is
   a bijection. (We use a constructive version of bijection, of course.)
-/

import ..types

open category_theory


namespace category_theory.universal

universes u v w

section shapes
/--
A `span Y Z`:
`Y <--π₁-- X --π₂--> Z`
-/
structure span {C : Type u} [𝒞 : category.{u v} C] (Y Z : C) :=
(X : C)
(π₁ : X ⟶ Y)
(π₂ : X ⟶ Z)

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

/--
A `fork f g`:
```
             f
 X --ι--> Y ====> Z
             g
```            
-/
structure fork {Y Z : C} (f g : Y ⟶ Z) := 
(X : C)
(ι : X ⟶ Y)
(w : ι ≫ f = ι ≫ g)

/-- 
A `square p q`:
```
X --a--> P
|        |
b        p
↓        ↓
Q --q--> R
```
-/
structure square {P Q R : C} (p : P ⟶ R) (q : Q ⟶ R) :=
(X : C)
(a : X ⟶ P)
(b : X ⟶ Q)
(w : a ≫ p = b ≫ q)

end shapes

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

namespace version_0

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ {X' : C} (f : X' ⟶ Y) (g : X' ⟶ Z), X' ⟶ t.X)
(fac₁ : ∀ {X' : C} (f : X' ⟶ Y) (g : X' ⟶ Z), (lift f g) ≫ t.π₁ = f) 
(fac₂ : ∀ {X' : C} (f : X' ⟶ Y) (g : X' ⟶ Z), (lift f g) ≫ t.π₂ = g) 
(uniq : ∀ {X' : C} (f : X' ⟶ t.X), f = lift (f ≫ t.π₁) (f ≫ t.π₂))

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)
end binary_product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ {X' : C} (k : X' ⟶ Y) (w : k ≫ f = k ≫ g), X' ⟶ t.X)
(fac  : ∀ {X' : C} (k : X' ⟶ Y) (w : k ≫ f = k ≫ g), (lift k w) ≫ t.ι = k)
(uniq : mono t.ι)

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)
end equalizer

section pullback
variables {P Q R : C}
structure is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) :=
(lift : ∀ {X'} {a' : X' ⟶ P} {b' : X' ⟶ Q} (w : a' ≫ p = b' ≫ q), X' ⟶ t.X)
(fac  : ∀ {X'} {a' : X' ⟶ P} {b' : X' ⟶ Q} (w : a' ≫ p = b' ≫ q), (lift w ≫ t.a) = a' ∧ (lift w ≫ t.b) = b')
(uniq : ∀ {X'} {a' : X' ⟶ P} {b' : X' ⟶ Q} (w : a' ≫ p = b' ≫ q) (m : X' ⟶ t.X) (w' : (m ≫ t.a) = a' ∧ (m ≫ t.b) = b'), m = lift w)

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(h : is_pullback t)
end pullback

end version_0

namespace version_1

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(μ : Π (s : span Y Z), s.X ⟶ t.X)
(u : Π (s : span Y Z), ∀ (φ : s.X ⟶ t.X), (s.π₁ = φ ≫ t.π₁ ∧ s.π₁ = φ ≫ t.π₁) ↔ (φ = μ s))

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)
end binary_product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) := 
(μ : Π (s : fork f g), s.X ⟶ t.X)
(u : Π (s : fork f g), ∀ (φ : s.X ⟶ t.X), (s.ι = φ ≫ t.ι) ↔ (φ = μ s)).

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)
end equalizer

section pullback
variables {P Q R : C}
structure is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) :=
(μ : Π (s : square p q), s.X ⟶ t.X)
(u : Π (s : square p q), ∀ (φ : s.X ⟶ t.X), (s.a = φ ≫ t.a ∧ s.b = φ ≫ t.b) ↔ (φ = μ s))

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(h : is_pullback t)
end pullback

end version_1

namespace version_2
section binary_product

def binary_product_comparison {Y Z : C} (t : span Y Z) (X' : C) : (X' ⟶ t.X) → (X' ⟶ Y) × (X' ⟶ Z) :=
λ φ, (φ ≫ t.π₁, φ ≫ t.π₂)

def is_binary_product {Y Z : C} (t : span Y Z) := Π (X' : C), is_equiv (binary_product_comparison t X')

structure binary_product (Y Z : C) extends t : span Y Z :=
(u : is_binary_product t)
end binary_product

section equalizers
variables {Y Z : C} 

def equalizer_comparison {f g : Y ⟶ Z} (t : fork f g) (X' : C) : (X' ⟶ t.X) → { h : X' ⟶ Y // h ≫ f = h ≫ g } :=
λ φ, ⟨ φ ≫ t.ι, begin repeat { rw category.assoc_lemma }, rw t.w, end ⟩ 

def is_equalizer {f g : Y ⟶ Z} (t : fork f g) := Π (X' : C), is_equiv (equalizer_comparison t X')

structure equalizer (f g : Y ⟶ Z) extends t : fork f g :=
(u : is_equalizer t)
end equalizers

section pullbacks
variables {P Q R : C}

def pullback_comparison {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) (X' : C) : (X' ⟶ t.X) → { c : (X' ⟶ P) × (X' ⟶ Q) // c.1 ≫ p = c.2 ≫ q } :=
λ φ, ⟨ (φ ≫ t.a, φ ≫ t.b), begin repeat { rw category.assoc_lemma }, rw t.w end ⟩ 

def is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) := Π (X' : C), is_equiv (pullback_comparison t X')

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(u : is_pullback t)
end pullbacks

end version_2

end category_theory.universal

