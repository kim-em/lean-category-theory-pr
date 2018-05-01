-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..category
import ..tactics

open categories

namespace categories.functor
 
universes u₁ v₁ u₂ v₂ u₃ v₃

-- The universe level could be reduced to `((max u₁ u₂)+1)` but this would make life harder later.
structure Functor (C : Type u₁) [uv_category.{u₁ v₁} C] (D : Type u₂) [uv_category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
  (onObjects     : C → D)
  (onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((onObjects X) ⟶ (onObjects Y)))
  (identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (onObjects X) . obviously)
  (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma Functor.identities
make_lemma Functor.functoriality
attribute [simp,ematch] Functor.functoriality_lemma Functor.identities_lemma

infixr ` +> `:70 := Functor.onObjects
infixr ` &> `:70 := Functor.onMorphisms -- switch to ▹?
infixr ` ↝ `:70 := Functor -- type as \lea 

definition IdentityFunctor (C) [category C] : C ↝ C := 
{ onObjects     := id,
  onMorphisms   := λ _ _ f, f,
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

instance (C) [category C] : has_one (C ↝ C) := 
{ one := IdentityFunctor C }

variable {C : Type (u₁+1)}
variable [category C]
variable {D : Type (u₂+1)}
variable [category D]
variable {E : Type (u₃+1)}
variable [category E]

@[simp] lemma IdentityFunctor.onObjects (X : C) : 1 +> X = X := by refl
@[simp] lemma IdentityFunctor.onMorphisms {X Y : C} (f : X ⟶ Y) : 1 &> f = f := by refl

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
-- instance Functor_to_onObjects : has_coe_to_fun (C ↝ D) :=
-- { F   := λ f, C → D,
--   coe := Functor.onObjects }

definition FunctorComposition (F : C ↝ D) (G : D ↝ E) : C ↝ E := 
{ onObjects     := λ X, G +> (F +> X),
  onMorphisms   := λ _ _ f, G &> (F &> f),
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     simp,
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     simp
                   end }

infixr ` ⋙ `:80 := FunctorComposition

@[simp] lemma FunctorComposition.onObjects (F : C ↝ D) (G : D ↝ E) (X : C) : (F ⋙ G) +> X = G +> (F +> X) := 
begin
  -- `obviously'` says:
  refl
end

@[simp] lemma FunctorComposition.onMorphisms (F : C ↝ D) (G : D ↝ E) (X Y: C) (f : X ⟶ Y) : (F ⋙ G) &> f = G.onMorphisms (F &> f) := 
begin
  -- `obviously'` says:
  refl
end

class Functorial (f : C → D) :=
  (onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((f X) ⟶ (f Y)))
  (identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (f X) . obviously)
  (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma Functorial.identities
make_lemma Functorial.functoriality
attribute [simp,ematch] Functorial.functoriality_lemma Functorial.identities_lemma

instance (F : C ↝ D) : Functorial (F.onObjects) := 
{ onMorphisms := F.onMorphisms }

-- TODO notations?

end categories.functor
