-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .functor

universes u v

namespace category_theory

structure Isomorphism {C : Type u} [category.{u v} C] (X Y : C) :=
(morphism : X ⟶ Y)
(inverse : Y ⟶ X)
(witness_1 : morphism ≫ inverse = 𝟙 X . obviously)
(witness_2 : inverse ≫ morphism = 𝟙 Y . obviously)

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

infixr ` ≅ `:10  := Isomorphism             -- type as \cong

variable {C : Type u}
variable [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

namespace Isomorphism

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma witness_1_assoc_lemma (I : Isomorphism X Y) (f : X ⟶ Z) : I.morphism ≫ I.inverse ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←category.associativity_lemma, Isomorphism.witness_1_lemma, category.left_identity_lemma]
end

@[simp,ematch] lemma witness_2_assoc_lemma (I : Isomorphism X Y) (f : Y ⟶ Z) : I.inverse ≫ I.morphism ≫ f = f := 
begin
  -- `obviously'` says:
  erw [←category.associativity_lemma, Isomorphism.witness_2_lemma, category.left_identity_lemma]
end

instance coercion_to_morphism : has_coe (Isomorphism.{u v} X Y) (X ⟶ Y) :=
{ coe := Isomorphism.morphism }

definition refl (X : C) : Isomorphism X X := 
{ morphism  := category.identity X,
  inverse   := category.identity X, 
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }

-- TODO maybe these can have ematch?
@[simp] lemma refl.morphism (X : C) : (Isomorphism.refl X).morphism = 𝟙 X := by refl
@[simp] lemma refl.inverse  (X : C) : (Isomorphism.refl X).inverse  = 𝟙 X := by refl

definition trans (α : Isomorphism X Y) (β : Isomorphism Y Z) : Isomorphism X Z := 
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

@[simp,ematch] lemma trans.morphism (α : Isomorphism X Y) (β : Isomorphism Y Z) : (α ♢ β).morphism = α.morphism ≫ β.morphism := by refl
@[simp,ematch] lemma trans.inverse  (α : Isomorphism X Y) (β : Isomorphism Y Z) : (α ♢ β).inverse  = β.inverse ≫ α.inverse   := by refl

@[extensionality] lemma pointwise_equal
  (α β : Isomorphism X Y)
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

definition symm (I : Isomorphism X Y) : Isomorphism Y X := 
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

end Isomorphism

class is_Isomorphism (f : X ⟶ Y) :=
  (inverse : Y ⟶ X)
  (witness_1 : f ≫ inverse = 𝟙 X . obviously)
  (witness_2 : inverse ≫ f = 𝟙 Y . obviously)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

namespace is_Isomorphism

instance of_identity (X : C) : is_Isomorphism (𝟙 X) := 
{ inverse := 𝟙 X, }

instance of_Isomorphism         (f : Isomorphism X Y) : is_Isomorphism f.morphism :=
{ inverse   := f.inverse,
  witness_1 := begin
                 -- `obviously'` says:
                 simp
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp
               end }
instance of_Isomorphism_inverse (f : Isomorphism X Y) : is_Isomorphism f.inverse  := 
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

end is_Isomorphism

class Epimorphism  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class Monomorphism (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance Epimorphism_of_Isomorphism  (f : X ⟶ Y) [is_Isomorphism f] : Epimorphism f  := 
{ left_cancellation := begin
                         -- This is an interesting test case for better rewrite automation.
                         intros,
                         rw [←category.left_identity_lemma C g, ←category.left_identity_lemma C h],
                         rw [← is_Isomorphism.witness_2_lemma f],
                         erw [category.associativity_lemma, w, category.associativity_lemma],
                       end }
instance Monomorphism_of_Isomorphism (f : X ⟶ Y) [is_Isomorphism f] : Monomorphism f := 
{ right_cancellation := begin
                         intros,
                         rw [←category.right_identity_lemma C g, ←category.right_identity_lemma C h],
                         rw [← is_Isomorphism.witness_1_lemma f],
                         erw [←category.associativity_lemma, w, ←category.associativity_lemma]
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

namespace Functor

universes u₁ v₁ u₂ v₂ 
variables {D : Type u₂}

variables [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition onIsomorphisms (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F +> X) ≅ (F +> Y) :=
{ morphism := F &> i.morphism,
  inverse  := F &> i.inverse }

@[simp,ematch] lemma onIsomorphisms.morphism (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.onIsomorphisms i).morphism = F &> i.morphism := by refl
@[simp,ematch] lemma onIsomorphisms.inverse  (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.onIsomorphisms i).morphism = F &> i.morphism := by refl

end Functor

end category_theory