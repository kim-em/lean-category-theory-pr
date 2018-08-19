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

import category_theory.types
import categories.isomorphism
import categories.tactics

open category_theory


namespace category_theory.universal

universes u v w
@[forward] lemma foo {α : Type u} {P : α → Prop} {x y : {a : α // P a}} (h : x = y) : x.val = y.val := 
begin obviously, end

section shapes
structure shape (C : Type u) [𝒞 : category.{u v} C] :=
(X : C)

structure point (C : Type u) [𝒞 : category.{u v} C] extends shape C.

/--
A `span Y Z`:
`Y <--π₁-- X --π₂--> Z`
-/
structure span {C : Type u} [𝒞 : category.{u v} C] (Y₁ Y₂ : C) extends shape C :=
(π₁ : X ⟶ Y₁)
(π₂ : X ⟶ Y₂)

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

restate_axiom fork.w
attribute [ematch] fork.w_lemma

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
structure square {C : Type u} [𝒞 : category.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z)extends shape C :=
(π₁ : X ⟶ Y₁)
(π₂ : X ⟶ Y₂)
(w : π₁ ≫ r₁ = π₂ ≫ r₂ . obviously)

restate_axiom square.w
attribute [ematch] square.w_lemma

structure cone {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] (F : J ↝ C) extends shape C :=
(π : ∀ j : J, X ⟶ F j)
(w : ∀ {j j' : J} (f : j ⟶ j'), π j ≫ (F.map f) = π j')

restate_axiom cone.w
attribute [ematch] cone.w_lemma

end shapes

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

namespace explicit
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section initial
structure is_terminal (t : C) :=
(lift : ∀ (s : C), s ⟶ t)
(uniq : ∀ (s : C) (m : s ⟶ t), m = lift s . obviously)

@[extensionality] lemma is_terminal.ext {X : C} (P Q : is_terminal.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

structure terminal_object extends t : point C :=
(h : is_terminal.{u v} t.X)
end initial

section binary_product
structure is_binary_product {Y Z : C} (t : span Y Z) :=
(lift : ∀ (s : span Y Z), s.X ⟶ t.X)
(fac₁ : ∀ (s : span Y Z), (lift s) ≫ t.π₁ = s.π₁ . obviously) 
(fac₂ : ∀ (s : span Y Z), (lift s) ≫ t.π₂ = s.π₂ . obviously) 
(uniq : ∀ (s : span Y Z) (m : s.X ⟶ t.X) (w₁ : m ≫ t.π₁ = s.π₁) (w₂ : m ≫ t.π₂ = s.π₂), m = lift s . obviously)

restate_axiom is_binary_product.fac₁
attribute [simp,ematch] is_binary_product.fac₁_lemma
restate_axiom is_binary_product.fac₂
attribute [simp,ematch] is_binary_product.fac₂_lemma
restate_axiom is_binary_product.uniq
attribute [ematch, back'] is_binary_product.uniq_lemma

@[extensionality] lemma is_binary_product.ext {Y Z : C} {t : span Y Z} (P Q : is_binary_product t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_binary_product.uniq' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)

lemma is_binary_product.univ {Y Z : C} {t : span Y Z} (h : is_binary_product t) (s : span Y Z) (φ : s.X ⟶ t.X) : (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

lemma is_binary_product.of_lift_univ {Y Z : C} {t : span Y Z}
  (lift : Π (s : span Y Z), s.X ⟶ t.X)
  (univ : Π (s : span Y Z) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : is_binary_product t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left, -- PROJECT automation
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin tidy, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate

@[reducible] def binary_product_comparison {Y Z : C} (t : span Y Z) (X' : C) : (X' ⟶ t.X) → (X' ⟶ Y) × (X' ⟶ Z) :=
λ φ, (φ ≫ t.π₁, φ ≫ t.π₂)

def is_binary_product.comparison {Y Z : C} {t : span Y Z} (h : is_binary_product t) (X' : C) : is_equiv (binary_product_comparison t X') :=
{ inv := λ p, h.lift ⟨ ⟨ X' ⟩, p.1, p.2 ⟩,
  hom_inv_id := begin tidy, symmetry, apply h.uniq, end,
}

end binary_product

section equalizer
variables {Y Z : C}
structure is_equalizer {f g : Y ⟶ Z} (t : fork f g) :=
(lift : ∀ (s : fork f g), s.X ⟶ t.X)
(fac  : ∀ (s : fork f g), (lift s) ≫ t.ι = s.ι . obviously)
(uniq : ∀ (s : fork f g) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s . obviously)

restate_axiom is_equalizer.fac
attribute [simp,ematch] is_equalizer.fac_lemma
restate_axiom is_equalizer.uniq
attribute [ematch, back'] is_equalizer.uniq_lemma

@[extensionality] lemma is_equalizer.ext {f g : Y ⟶ Z} {t : fork f g} (P Q : is_equalizer t) : P = Q :=
begin cases P, cases Q, obviously end

lemma is_equalizer.mono {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) : mono (t.ι) :=
{ right_cancellation := λ X' k l w, begin 
                                    let s : fork f g := { X := X', ι := k ≫ t.ι }, 
                                    have uniq_k := h.uniq s k (by obviously),
                                    have uniq_l := h.uniq s l (by obviously),
                                    obviously,
                              end }

-- TODO provide an alternative constructor via mono

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)

lemma is_equalizer.univ {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) (s : fork f g) (φ : s.X ⟶ t.X) : (φ ≫ t.ι = s.ι) ↔ (φ = h.lift s) :=
begin
obviously
end


end equalizer

section pullback
variables {Y₁ Y₂ Z : C}
structure is_pullback {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (t : square r₁ r₂) :=
(lift : ∀ (s : square r₁ r₂), s.X ⟶ t.X)
(fac₁ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₁) = s.π₁ . obviously)
(fac₂ : ∀ (s : square r₁ r₂), (lift s ≫ t.π₂) = s.π₂ . obviously)
(uniq : ∀ (s : square r₁ r₂) (m : s.X ⟶ t.X) (w₁ : (m ≫ t.π₁) = s.π₁) (w₂ : (m ≫ t.π₂) = s.π₂), m = lift s . obviously)

restate_axiom is_pullback.fac₁
attribute [simp,ematch] is_pullback.fac₁_lemma
restate_axiom is_pullback.fac₂
attribute [simp,ematch] is_pullback.fac₂_lemma
restate_axiom is_pullback.uniq
attribute [ematch, back'] is_pullback.uniq_lemma

@[extensionality] lemma is_pullback.ext {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂} (P Q : is_pullback t) : P = Q :=
begin cases P, cases Q, obviously end

structure pullback (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) extends t : square r₁ r₂ :=
(h : is_pullback t)

lemma is_pullback.univ  {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂} (h : is_pullback t) (s : square r₁ r₂) (φ : s.X ⟶ t.X) : (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

end pullback

section limit
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

structure is_limit {F : J ↝ C} (t : cone F) :=
(lift : ∀ (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), (lift s ≫ t.π j) = s.π j . obviously)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, (m ≫ t.π j) = s.π j), m = lift s . obviously)

restate_axiom is_limit.fac
attribute [simp,ematch] is_limit.fac_lemma
restate_axiom is_limit.uniq
attribute [ematch, back'] is_limit.uniq_lemma

@[extensionality] lemma is_limit.ext {F : J ↝ C} {t : cone F} (P Q : is_limit t) : P = Q :=
begin cases P, cases Q, obviously end

structure limit (F : J ↝ C) extends t : cone F :=
(h : is_limit t)

lemma is_limit.univ {F : J ↝ C} {t : cone F} (h : is_limit t) (s : cone F) (φ : s.X ⟶ t.X) : (∀ j, φ ≫ t.π j = s.π j) ↔ (φ = h.lift s) :=
begin
obviously,
end

end limit
end explicit


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
λ φ, ⟨ φ ≫ t.ι, by obviously ⟩ 

def is_equalizer {f g : Y ⟶ Z} (t : fork f g) := Π (X' : C), is_equiv (equalizer_comparison t X')

structure equalizer (f g : Y ⟶ Z) extends t : fork f g :=
(h : is_equalizer t)
end equalizers

section pullbacks
variables {Y₁ Y₂ Z : C}

def pullback_comparison {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (t : square r₁ r₂) (X' : C) : (X' ⟶ t.X) → { c : (X' ⟶ Y₁) × (X' ⟶ Y₂) // c.1 ≫ r₁ = c.2 ≫ r₂ } :=
λ φ, ⟨ (φ ≫ t.π₁, φ ≫ t.π₂), by obviously ⟩ 

def is_pullback {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (t : square r₁ r₂) := Π (X' : C), is_equiv (pullback_comparison t X')

structure pullback (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) extends t : square r₁ r₂ :=
(h : is_pullback t)
end pullbacks

end bijective

open explicit -- CHANGE THIS LINE TO TRY OUT DIFFERENT VERSIONS explict/singleton/bijective

class has_binary_products (C : Type u) [𝒞 : category.{u v} C] :=
(binary_product : Π (Y Z : C), binary_product.{u v} Y Z)

class has_equalizers (C : Type u) [𝒞 : category.{u v} C] :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), equalizer f g)

class has_pullbacks (C : Type u) [𝒞 : category.{u v} C] :=
(pullback : Π {P Q R : C} (p : P ⟶ R) (q: Q ⟶ R), pullback p q)

def binary_product {C : Type u} [𝒞 : category.{u v} C] [has_binary_products C] (Y Z : C) := has_binary_products.binary_product Y Z
def equalizer {C : Type u} [𝒞 : category.{u v} C] [has_equalizers C] {Y Z : C} (f g : Y ⟶ Z) := has_equalizers.equalizer f g
def pullback {C : Type u} [𝒞 : category.{u v} C] [has_pullbacks C] {P Q R : C} (p : P ⟶ R) (q: Q ⟶ R) := has_pullbacks.pullback p q

local attribute [forward] fork.w square.w

instance : has_binary_products (Type u) := 
{ binary_product := λ Y Z, { X := Y × Z, π₁ := prod.fst, π₂ := prod.snd, h := by obviously } }

instance : has_equalizers (Type u) := 
{ equalizer := λ Y Z f g, { X := { y : Y // f y = g y }, ι := subtype.val, w := by obviously, h := by obviously } }

instance : has_pullbacks (Type u) := 
{ pullback := λ Y₁ Y₂ Z r₁ r₂, { X := { z : Y₁ × Y₂ // r₁ z.1 = r₂ z.2 }, π₁ := λ z, z.val.1, π₂ := λ z, z.val.2, w := by obviously, h := by obviously } }



end category_theory.universal

