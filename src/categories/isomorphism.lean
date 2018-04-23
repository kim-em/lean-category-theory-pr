-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .functor
open categories
open categories.functor

namespace categories.isomorphism
universes u

variable {C : Type (u+1)}
variable [category C]
variables {X Y Z : C}

structure Isomorphism (X Y : C) :=
  (morphism : X ⟶ Y)
  (inverse : Y ⟶ X)
  (witness_1 : morphism ≫ inverse = 𝟙 X . obviously)
  (witness_2 : inverse ≫ morphism = 𝟙 Y . obviously)

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

infixr ` ≅ `:10  := Isomorphism             -- type as \cong

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma Isomorphism.witness_1_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.morphism ≫ I.inverse ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←category.associativity_lemma, Isomorphism.witness_1_lemma, category.left_identity_lemma]
end

@[simp,ematch] lemma Isomorphism.witness_2_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inverse ≫ I.morphism ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←category.associativity_lemma, Isomorphism.witness_2_lemma, category.left_identity_lemma]
end

instance Isomorphism_coercion_to_morphism : has_coe (X ≅ Y) (X ⟶ Y) :=
{ coe := Isomorphism.morphism }

definition Isomorphism.id (X : C) : X ≅ X := 
{ morphism  := 1,
  inverse   := 1, 
  witness_1 := begin
                 -- `obviously'` says:
                 simp!,
                 refl
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!,
                 refl
               end }

@[reducible] definition Isomorphism.comp (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z := 
{ morphism  := α.morphism ≫ β.morphism,
  inverse   := β.inverse ≫ α.inverse,
  witness_1 := begin
                 -- `obviously'` says:
                 simp!
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!
               end }

infixr ` ≫ `:80 := Isomorphism.comp -- type as \gg

@[applicable] lemma Isomorphism_pointwise_equal
  (α β : X ≅ Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        induction w,
        dsimp at *,
        rw [← category.left_identity_lemma C k, ←wα2, category.associativity_lemma, wβ1, category.right_identity_lemma]
      end,
    -- `obviously'` says:
    induction p, induction w,
    refl
  end

definition Isomorphism.reverse (I : X ≅ Y) : Y ≅ X := 
{ morphism  := I.inverse,
  inverse   := I.morphism,
  witness_1 := begin
                 -- `obviously'` says:
                 simp!
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!
               end }

class is_Isomorphism (f : X ⟶ Y) :=
  (inverse : Y ⟶ X)
  (witness_1 : f ≫ inverse = 𝟙 X . obviously)
  (witness_2 : inverse ≫ f = 𝟙 Y . obviously)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance (f : X ≅ Y) : is_Isomorphism f.morphism := by sorry

instance (f : X ⟶ Y): has_coe (is_Isomorphism f) (X ⟶ Y) :=
{ coe := λ _, f }

class Epimorphism  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class Monomorphism (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance Epimorphism_of_Isomorphism  (f : X ⟶ Y) [is_Isomorphism f] : Epimorphism f  := by sorry
instance Monomorphism_of_Isomorphism (f : X ⟶ Y) [is_Isomorphism f] : Monomorphism f := by sorry

@[simp] lemma cancel_Epimorphism  (f : X ⟶ Y) [Epimorphism f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := by sorry
@[simp] lemma cancel_Monomorphism (f : X ⟶ Y) [Monomorphism f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := by sorry

end categories.isomorphism
