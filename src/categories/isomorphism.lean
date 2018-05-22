-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .functor
open categories
open categories.functor

universes u v

namespace categories.isomorphism

structure Isomorphism {C : Type u} [uv_category.{u v} C] (X Y : C) :=
  (morphism : X ⟶ Y)
  (inverse : Y ⟶ X)
  (witness_1 : morphism ≫ inverse = 𝟙 X . obviously)
  (witness_2 : inverse ≫ morphism = 𝟙 Y . obviously)

-- structure Isomorphism_small {C : Type u}     [small_category C] (X Y : C) extends Isomorphism.{u u} X Y.
-- structure Isomorphism_large {C : Type (u+1)} [category C]       (X Y : C) extends Isomorphism.{u+1 u} X Y.

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

infixr ` ≅ `:10  := Isomorphism             -- type as \cong
-- infixr ` ≅ `:11  := Isomorphism_small
-- infixr ` ≅ `:12  := Isomorphism_large

set_option pp.universes true

variable {C : Type u}
variable [C_cat : uv_category.{u v} C]
include C_cat
variables {X Y Z : C}


-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma Isomorphism.witness_1_assoc_lemma (I : Isomorphism.{u v} X Y) (f : X ⟶ Z) : I.morphism ≫ I.inverse ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←uv_category.associativity_lemma, Isomorphism.witness_1_lemma, uv_category.left_identity_lemma]
end

@[simp,ematch] lemma Isomorphism.witness_2_assoc_lemma (I : Isomorphism.{u v} X Y) (f : Y ⟶ Z) : I.inverse ≫ I.morphism ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←uv_category.associativity_lemma, Isomorphism.witness_2_lemma, uv_category.left_identity_lemma]
end

instance Isomorphism_coercion_to_morphism : has_coe (Isomorphism.{u v} X Y) (X ⟶ Y) :=
{ coe := Isomorphism.morphism }

definition Isomorphism.refl (X : C) : Isomorphism.{u v} X X := 
{ morphism  := uv_category.identity X,
  inverse   := uv_category.identity X, 
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }

definition Isomorphism.trans (α : Isomorphism.{u v} X Y) (β : Isomorphism.{u v} Y Z) : Isomorphism.{u v} X Z := 
{ morphism  := α.morphism ≫ β.morphism,
  inverse   := β.inverse ≫ α.inverse,
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }

infixr ` ♢ `:80 := Isomorphism.trans -- type as \diamonds

@[applicable] lemma Isomorphism_pointwise_equal
  (α β : Isomorphism.{u v} X Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        induction w,
        dsimp at *,
        rw [← uv_category.left_identity_lemma C k, ←wα2, uv_category.associativity_lemma, wβ1, uv_category.right_identity_lemma]
      end,
    -- `obviously'` says:
    induction p, induction w,
    refl
  end

definition Isomorphism.symm (I : Isomorphism.{u v} X Y) : Isomorphism.{u v} Y X := 
{ morphism  := I.inverse,
  inverse   := I.morphism,
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }



class is_Isomorphism (f : X ⟶ Y) :=
  (inverse : Y ⟶ X)
  (witness_1 : f ≫ inverse = 𝟙 X . obviously)
  (witness_2 : inverse ≫ f = 𝟙 Y . obviously)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_of_Isomorphism         (f : Isomorphism.{u v} X Y) : is_Isomorphism f.morphism :=
{ inverse   := f.inverse,
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }
instance is_Isomorphism_of_Isomorphism_inverse (f : Isomorphism.{u v} X Y) : is_Isomorphism f.inverse  := 
{ inverse   := f.morphism,
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }

instance (f : X ⟶ Y): has_coe (is_Isomorphism f) (X ⟶ Y) :=
{ coe := λ _, f }

class Epimorphism  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class Monomorphism (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance Epimorphism_of_Isomorphism  (f : X ⟶ Y) [is_Isomorphism f] : Epimorphism f  := 
{ left_cancellation := begin
                         intros,
                         rw [←uv_category.left_identity_lemma C g, ←uv_category.left_identity_lemma C h],
                         rw [← is_Isomorphism.witness_2_lemma f],
                         rewrite_search_using `ematch, -- PROJECT Scott is thinking about completing the automation here.
                       end }
instance Monomorphism_of_Isomorphism (f : X ⟶ Y) [is_Isomorphism f] : Monomorphism f := 
{ right_cancellation := begin
                         intros,
                         rw [←uv_category.right_identity_lemma C g, ←uv_category.right_identity_lemma C h],
                         rw [← is_Isomorphism.witness_1_lemma f],
                         rewrite_search_using `ematch,
                       end }

@[simp] lemma cancel_Epimorphism  (f : X ⟶ Y) [Epimorphism f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := 
⟨ λ p, Epimorphism.left_cancellation g h p, begin
                                              -- `obviously'` says:
                                              intros,
                                              induction a,
                                              refl
                                            end ⟩
@[simp] lemma cancel_Monomorphism (f : X ⟶ Y) [Monomorphism f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := 
⟨ λ p, Monomorphism.right_cancellation g h p, begin
                                                -- `obviously'` says:
                                                intros,
                                                induction a,
                                                refl
                                              end ⟩

end categories.isomorphism

variables {C D : Type u}
variables [C_cat : uv_category.{u v} C]
variables [D_cat : uv_category.{u v} D]
include C_cat D_cat

namespace categories.functor

definition Functor.onIsomorphisms (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F +> X) ≅ (F +> Y) :=
{ morphism := F &> i.morphism,
  inverse  := F &> i.inverse }

end categories.functor