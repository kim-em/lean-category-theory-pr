-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.types
import categories.isomorphism
import categories.tactics

open category_theory


namespace category_theory.universal

universes u v w

definition is_equiv {α β : Type v} (f : α → β) := @is_iso (Type v) (category_theory.types) _ _ f

@[forward] lemma subtype_val {α : Type u} {P : α → Prop} {x y : {a : α // P a}} (h : x = y) : x.val = y.val := 
begin obviously, end

section

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
X  --π₁--> Y₁
|          |
π₂         r₁
↓          ↓
Y₂ --r₂--> Z
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

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section terminal
structure is_terminal (t : C) :=
(lift : ∀ (s : C), s ⟶ t)
(uniq : ∀ (s : C) (m : s ⟶ t), m = lift s . obviously)

restate_axiom is_terminal.uniq
attribute [ematch, back'] is_terminal.uniq_lemma

@[extensionality] lemma is_terminal.ext {X : C} (P Q : is_terminal.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

variable (C) 

structure terminal_object extends t : point C :=
(h : is_terminal.{u v} t.X)

instance hom_to_terminal_subsingleton (X : C) (B : terminal_object.{u v} C) : subsingleton (X ⟶ B.X) :=
begin
  fsplit, intros f g,
  rw B.h.uniq X f,
  rw B.h.uniq X g,
end

end terminal

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

instance {Y Z : C} {t : span Y Z} : subsingleton (is_binary_product t) := 
begin 
  fsplit, intros,
  apply is_binary_product.ext, -- obviously will do this after https://github.com/leanprover/mathlib/pull/269
end

lemma is_binary_product.uniq' {Y Z : C} {t : span Y Z} (h : is_binary_product t) {X' : C} (m : X' ⟶ t.X) : m = h.lift { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } :=
h.uniq { X := X', π₁ := m ≫ t.π₁, π₂ := m ≫ t.π₂ } m (by obviously) (by obviously)

-- TODO provide alternative constructor using uniq' instead of uniq.

structure binary_product (Y Z : C) extends t : span Y Z :=
(h : is_binary_product t)

lemma is_binary_product.univ {Y Z : C} {t : span Y Z} (h : is_binary_product t) (s : span Y Z) (φ : s.X ⟶ t.X) : (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_binary_product.of_lift_univ {Y Z : C} {t : span Y Z}
  (lift : Π (s : span Y Z), s.X ⟶ t.X)
  (univ : Π (s : span Y Z) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : is_binary_product t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left, -- PROJECT automation
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin tidy, apply univ_s_m.mp, obviously, end } -- TODO should be easy to automate


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

structure equalizer (f g : Y ⟶ Z) extends t : fork f g := 
(h : is_equalizer t)

lemma is_equalizer.univ {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) (s : fork f g) (φ : s.X ⟶ t.X) : (φ ≫ t.ι = s.ι) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_equalizer.of_lift_univ {f g : Y ⟶ Z} {t : fork f g}
  (lift : Π (s : fork f g), s.X ⟶ t.X)
  (univ : Π (s : fork f g) (φ : s.X ⟶ t.X), (φ ≫ t.ι = s.ι) ↔ (φ = lift s)) : is_equalizer t :=
{ lift := lift,
  fac := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))),
  uniq := begin tidy, apply univ_s_m.mp, obviously, end }


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

lemma is_pullback.univ {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂} (h : is_pullback t) (s : square r₁ r₂) (φ : s.X ⟶ t.X) : (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = h.lift s) :=
begin
obviously
end

def is_pullback.of_lift_univ {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂}
  (lift : Π (s : square r₁ r₂), s.X ⟶ t.X)
  (univ : Π (s : square r₁ r₂) (φ : s.X ⟶ t.X), (φ ≫ t.π₁ = s.π₁ ∧ φ ≫ t.π₂ = s.π₂) ↔ (φ = lift s)) : is_pullback t :=
{ lift := lift,
  fac₁ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).left,
  fac₂ := λ s, ((univ s (lift s)).mpr (eq.refl (lift s))).right,
  uniq := begin tidy, apply univ_s_m.mp, obviously, end }


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

def is_limit.of_lift_univ {F : J ↝ C} {t : cone F}
  (lift : Π (s : cone F), s.X ⟶ t.X)
  (univ : Π (s : cone F) (φ : s.X ⟶ t.X), (∀ j : J, (φ ≫ t.π j) = s.π j) ↔ (φ = lift s)) : is_limit t :=
{ lift := lift,
  fac  := λ s j, ((univ s (lift s)).mpr (eq.refl (lift s))) j,
  uniq := begin tidy, apply univ_s_m.mp, obviously, end }

end limit

variable (C)

class has_binary_products :=
(binary_product : Π (Y Z : C), binary_product.{u v} Y Z)

class has_equalizers :=
(equalizer : Π {Y Z : C} (f g : Y ⟶ Z), equalizer f g)

class has_pullbacks :=
(pullback : Π {P Q R : C} (p : P ⟶ R) (q: Q ⟶ R), pullback p q)

variable {C}

-- TODO how to name these?
def binary_product' [has_binary_products.{u v} C] (Y Z : C) := has_binary_products.binary_product.{u v} Y Z
def equalizer' [has_equalizers.{u v} C] {Y Z : C} (f g : Y ⟶ Z) := has_equalizers.equalizer.{u v} f g
def pullback' [has_pullbacks.{u v} C] {Y₁ Y₂ Z : C} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) := has_pullbacks.pullback.{u v} r₁ r₂

end

end category_theory.universal

