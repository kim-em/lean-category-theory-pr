-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import .products
import .types

namespace category_theory

universes u₁ v₁ u₂ v₂

def Opposite.op (C : Type u₁) : Type u₁ := C

notation C `ᵒᵖ` := Opposite.op C

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

instance opposite : category.{u₁ v₁} (Cᵒᵖ) := 
{ Hom     := λ X Y : C, Y ⟶ X,
  comp    := λ _ _ _ f g, g ≫ f,
  id      := λ X, 𝟙 X,
  id_comp := begin /- `obviously'` says: -/ intros, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, simp end }

namespace functor

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition opposite (F : C ↝ D) : (Cᵒᵖ) ↝ (Dᵒᵖ) := 
{ obj     := λ X, F X,
  map   := λ X Y f, F.map f,
  map_id    := begin /- `obviously'` says: -/ intros, erw [map_id], refl, end,
  map_comp := begin /- `obviously'` says: -/ intros, erw [map_comp], refl end }

@[simp,ematch] lemma contravariant_map_comp
  (F : (Cᵒᵖ) ↝ D)
  (X Y Z : (Cᵒᵖ))
  (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((@category_theory.category.comp C _ _ _ _ g f) : X ⟶ Z) = (F.map f) ≫ (F.map g) := 
    begin /- `obviously'` says: -/ erw [map_comp] end

@[simp,ematch] lemma contravariant_map_id
  (F : (Cᵒᵖ) ↝ D) (X : (Cᵒᵖ)) : (F.map (@category_theory.category.id C _ X)) = 𝟙 (F X) :=
  begin /- `obviously'` says: -/ erw [map_id], refl, end
                   
end functor

variable (C)

definition hom_pairing : (Cᵒᵖ × C) ↝ (Type v₁) := 
{ obj      := λ p, @category.Hom C _ p.1 p.2,
  map      := λ X Y f, λ h, f.1 ≫ h ≫ f.2,
  map_id   := begin /- `obviously'` says: -/ intros, apply funext, intros, cases X, dsimp at *, simp, erw [category.id_comp_lemma] end,
  map_comp := begin /- `obviously'` says: -/ intros, apply funext, intros, cases g, cases f, cases Z, cases Y, cases X, dsimp at *, simp, erw [category.assoc] end }

end category_theory