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

0) `explicit` is as explicit as possible, writing everything out in terms of fields `lift`, `fac`, and `uniq`,
   which respectively show how to lift a map, the factorisation property it has, and the uniqueness of that factorisation.   
1) `singleton` uses two fields, `μ` and `u`. `μ` shows how to construct a map from another shape, and `u` expresses
   the uniqueness of this map using the pattern "for all maps from another shape, it factorises correctly if and only if it is the lift".
   (Thanks for Mario for helping with this one.)
2) `bijective`, closely following [Reid's work](https://github.com/rwbarton/lean-homotopy-theory/blob/lean-3.4.1/src/categories/colimits.lean)
   expresses the universal property by stating that a certain map between hom sets (or products and subsets of such)
   is a bijection. As an example, we can say that a span `Y <--p-- X --q--> Z` is a binary product exactly if for
   every object `X'`, the map `(X' ⟶ X) → (X' ⟶ Y) × (X' ⟶ Z)` given by post-composition by `p` and `q` is
   a bijection. (We use a constructive version of bijection, of course.)

To try them out, I proved that the category of types has equalizers, pullbacks, and binary products.
Rather beautifully, usually `obviously` you can write exactly the same proof for all three versions:
you just specify the shape, and `obviously` deals with the variations in what's required to check the universal
properties. For what it's worth, `obviously` is slightly (25%) slower on `singleton` than on `explicit` and `bijective`.

My opinion: `bijective` looks good to me. I think it's the most intimidating one first reading, but grows on you
quickly. It also has the potentially very significant advantage that it is easy to generalise to the setting
of enriched categories, which the algebraic geometers are definitely going to want.
-/

import ..types

open category_theory


namespace category_theory.universal

universes u v w
@[forward] lemma foo {α : Type u} {P : α → Prop} {x y : {a : α // P a}} (h : x = y) : x.val = y.val := 
begin obviously, end

section shapes
structure shape (C : Type u) [𝒞 : category.{u v} C] :=
(X : C)

/--
A `span Y Z`:
`Y <--π₁-- X --π₂--> Z`
-/
structure span {C : Type u} [𝒞 : category.{u v} C] (Y Z : C) extends shape C :=
(π₁ : X ⟶ Y)
(π₂ : X ⟶ Z)

/--
A `fork f g`:
```
             f
 X --ι--> Y ====> Z
             g
```            
-/
structure fork {C : Type u} [𝒞 : category.{u v} C] {Y Z : C} (f g : Y ⟶ Z) extends shape C := 
(ι : X ⟶ Y)
(w : ι ≫ f = ι ≫ g . obviously)

attribute [ematch] fork.w

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
structure square {C : Type u} [𝒞 : category.{u v} C] {P Q R : C} (p : P ⟶ R) (q : Q ⟶ R) extends shape C :=
(a : X ⟶ P)
(b : X ⟶ Q)
(w : a ≫ p = b ≫ q . obviously)

attribute [ematch] square.w

end shapes

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

namespace explicit
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞


section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ (s : span Y Z), s.X ⟶ t.X)
(fac₁ : ∀ (s : span Y Z), (lift s) ≫ t.π₁ = s.π₁) 
(fac₂ : ∀ (s : span Y Z), (lift s) ≫ t.π₂ = s.π₂) 
(uniq : ∀ (s : span Y Z) (m : s.X ⟶ t.X) (w₁ : m ≫ t.π₁ = s.π₁) (w₂ : m ≫ t.π₂ = s.π₂), m = lift s)

lemma is_binary_product.uniq' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)
end binary_product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ (s : fork f g), s.X ⟶ t.X)
(fac  : ∀ (s : fork f g), (lift s) ≫ t.ι = s.ι)
(uniq : ∀ (s : fork f g) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s)

lemma is_equalizer.uniq' {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) : mono (t.ι) :=
{ right_cancellation := λ X' k l, begin 
                                    let s : fork f g := { X := X', ι := k ≫ t.ι, w := sorry }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                              end }

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)
end equalizer

section pullback
variables {P Q R : C}
structure is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) :=
(lift : ∀ (s : square p q), s.X ⟶ t.X)
(fac₁ : ∀ (s : square p q), (lift s ≫ t.a) = s.a)
(fac₂ : ∀ (s : square p q), (lift s ≫ t.b) = s.b)
(uniq : ∀ (s : square p q) (m : s.X ⟶ t.X) (w₁ : (m ≫ t.a) = s.a) (w₂ : (m ≫ t.b) = s.b), m = lift s)

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(h : is_pullback t)
end pullback

end explicit

namespace singleton
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞


section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : Π (s : span Y Z), s.X ⟶ t.X)
(univ : Π (s : span Y Z), ∀ (φ : s.X ⟶ t.X), (s.π₁ = φ ≫ t.π₁ ∧ s.π₂ = φ ≫ t.π₂) ↔ (φ = lift s))

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)
end binary_product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) := 
(lift : Π (s : fork f g), s.X ⟶ t.X)
(univ : Π (s : fork f g), ∀ (φ : s.X ⟶ t.X), (s.ι = φ ≫ t.ι) ↔ (φ = lift s)).

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)
end equalizer

section pullback
variables {P Q R : C}
structure is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) :=
(lift : Π (s : square p q), s.X ⟶ t.X)
(univ : Π (s : square p q), ∀ (φ : s.X ⟶ t.X), (s.a = φ ≫ t.a ∧ s.b = φ ≫ t.b) ↔ (φ = lift s))

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(h : is_pullback t)
end pullback

end singleton

namespace bijective

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞


section binary_product

def binary_product_comparison {Y Z : C} (t : span Y Z) (X' : C) : (X' ⟶ t.X) → (X' ⟶ Y) × (X' ⟶ Z) :=
λ φ, (φ ≫ t.π₁, φ ≫ t.π₂)

def is_binary_product {Y Z : C} (t : span Y Z) := Π (X' : C), is_equiv (binary_product_comparison t X')

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)
end binary_product

section equalizers
variables {Y Z : C} 

def equalizer_comparison {f g : Y ⟶ Z} (t : fork f g) (X' : C) : (X' ⟶ t.X) → { h : X' ⟶ Y // h ≫ f = h ≫ g } :=
λ φ, ⟨ φ ≫ t.ι, begin repeat { rw category.assoc_lemma }, rw t.w, end ⟩ 

def is_equalizer {f g : Y ⟶ Z} (t : fork f g) := Π (X' : C), is_equiv (equalizer_comparison t X')

structure equalizer (f g : Y ⟶ Z) extends t : fork f g :=
(h : is_equalizer t)
end equalizers

section pullbacks
variables {P Q R : C}

def pullback_comparison {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) (X' : C) : (X' ⟶ t.X) → { c : (X' ⟶ P) × (X' ⟶ Q) // c.1 ≫ p = c.2 ≫ q } :=
λ φ, ⟨ (φ ≫ t.a, φ ≫ t.b), begin repeat { rw category.assoc_lemma }, rw t.w end ⟩ 

def is_pullback {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) := Π (X' : C), is_equiv (pullback_comparison t X')

structure pullback (p : P ⟶ R) (q : Q ⟶ R) extends t : square p q :=
(h : is_pullback t)
end pullbacks

end bijective

open explicit -- CHANGE THIS LINE TO TRY OUT DIFFERENT VERSIONS

class has_binary_products (C : Type u) [𝒞 : category.{u v} C] :=
(binary_product : Π (Y Z : C), binary_product.{u v} Y Z)

class has_equalizers (C : Type u) [𝒞 : category.{u v} C] :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), equalizer f g)

class has_pullbacks (C : Type u) [𝒞 : category.{u v} C] :=
(pullback : Π {P Q R : C} (p : P ⟶ R) (q: Q ⟶ R), pullback p q)

def binary_product {C : Type u} [𝒞 : category.{u v} C] [has_binary_products C] (Y Z : C) := has_binary_products.binary_product Y Z
def equalizer {C : Type u} [𝒞 : category.{u v} C] [has_equalizers C] {Y Z : C} (f g : Y ⟶ Z) := has_equalizers.equalizer f g
def pullback {C : Type u} [𝒞 : category.{u v} C] [has_pullbacks C] {P Q R : C} (p : P ⟶ R) (q: Q ⟶ R) := has_pullbacks.pullback p q

-- obviously has a bit of trouble with version_1, and benefits from the following help:
-- local attribute [forward] fork.w square.w

instance : has_binary_products (Type u) := 
{ binary_product := λ Y Z, { X := Y × Z, π₁ := prod.fst, π₂ := prod.snd, h := by obviously } }

instance : has_equalizers (Type u) := 
{ equalizer := λ Y Z f g, { X := { y : Y // f y = g y }, ι := subtype.val, w := by obviously, h := by obviously } }

instance : has_pullbacks (Type u) := 
{ pullback := λ P Q R p q, { X := { z : P × Q // p z.1 = q z.2 }, a := λ z, z.val.1, b := λ z, z.val.2, w := by obviously, h := by obviously } }



end category_theory.universal

