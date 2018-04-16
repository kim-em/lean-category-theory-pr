-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..category
import ..tactics

open categories

namespace categories.functor
 
universes u₁ u₂ u₃ 

-- The universe level could be reduced to `((max u₁ u₂)+1)` but this would make life harder later.
structure Functor (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] : Type ((max (u₁+1) u₂)+1) :=
  (onObjects     : C → D)
  (onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (onObjects X) . obviously')
  (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously')

make_lemma Functor.identities
make_lemma Functor.functoriality
attribute [simp,ematch] Functor.identities_lemma
attribute [simp,ematch] Functor.functoriality_lemma

infixr ` &> `:80 := Functor.onMorphisms -- switch to ▹?
infixr ` ↝ `:70 := Functor -- type as \lea 

definition IdentityFunctor (C) [category C] : C ↝ C := 
{ onObjects     := id,
  onMorphisms   := λ _ _ f, f,
<<<<<<< HEAD
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     refl 
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }
=======
  identities    := by obviously',
  functoriality := by obviously' }
>>>>>>> origin/master

instance (C) [category C] : has_one (C ↝ C) := 
{ one := IdentityFunctor C }

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]
variable {E : Type (u₃+1)}
variable [category E]

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects : has_coe_to_fun (C ↝ D) :=
{ F   := λ f, C → D,
  coe := Functor.onObjects }

definition FunctorComposition (F : C ↝ D) (G : D ↝ E) : C ↝ E := 
{ onObjects     := λ X, G (F X),
  onMorphisms   := λ _ _ f, G &> (F &> f),
<<<<<<< HEAD
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     simp!,
                     dsimp_all',
                     simp!
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     simp!
                   end }
=======
  identities    := by obviously',
  functoriality := by obviously' }
>>>>>>> origin/master

infixr ` ⋙ `:80 := FunctorComposition

end categories.functor
