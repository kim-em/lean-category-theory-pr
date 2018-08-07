-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .functor

universes u v

namespace category_theory

structure iso {C : Type u} [category.{u v} C] (X Y : C) :=
(map : X ⟶ Y)
(inv : Y ⟶ X)
(map_inv_id : map ≫ inv = 𝟙 X . obviously)
(inv_map_id : inv ≫ map = 𝟙 Y . obviously)

make_lemma iso.map_inv_id
make_lemma iso.inv_map_id
attribute [simp,ematch] iso.map_inv_id_lemma iso.inv_map_id_lemma

infixr ` ≅ `:10  := iso             -- type as \cong

variable {C : Type u}
variable [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

namespace iso

instance : has_coe (iso.{u v} X Y) (X ⟶ Y) :=
{ coe := iso.map }

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma witness_1_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.map ≫ I.inv ≫ f = f := 
begin
  -- `obviously'` says:
  rw [←category.associativity_lemma, iso.map_inv_id_lemma, category.left_identity_lemma]
end

@[simp,ematch] lemma witness_2_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inv ≫ I.map ≫ f = f := 
begin
  -- `obviously'` says:
  rw [←category.associativity_lemma, iso.inv_map_id_lemma, category.left_identity_lemma]
end

definition refl (X : C) : X ≅ X := 
{ map := 𝟙 X,
  inv := 𝟙 X, 
  map_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_map_id := begin /- `obviously'` says: -/ simp end }

-- TODO maybe these can have ematch?
@[simp] lemma refl_map (X : C) : (iso.refl X).map = 𝟙 X := rfl
@[simp] lemma refl_inv  (X : C) : (iso.refl X).inv  = 𝟙 X := rfl

definition trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z := 
{ map := α.map ≫ β.map,
  inv := β.inv ≫ α.inv,
  map_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_map_id := begin /- `obviously'` says: -/ simp end }

infixr ` ♢ `:80 := iso.trans -- type as \diamonds

@[simp,ematch] lemma trans_morphism (α : X ≅ Y) (β : Y ≅ Z) : (α ♢ β).map = α.map ≫ β.map := rfl
@[simp,ematch] lemma trans_inverse  (α : X ≅ Y) (β : Y ≅ Z) : (α ♢ β).inv  = β.inv ≫ α.inv   := rfl

@[extensionality] lemma ext
  (α β : X ≅ Y)
  (w : α.map = β.map) : α = β :=
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

definition symm (I : X ≅ Y) : Y ≅ X := 
{ map := I.inv,
  inv := I.map,
  map_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_map_id := begin /- `obviously'` says: -/ simp end }

end iso

class is_iso (f : X ⟶ Y) :=
  (inv : Y ⟶ X)
  (map_inv_id : f ≫ inv = 𝟙 X . obviously)
  (inv_map_id : inv ≫ f = 𝟙 Y . obviously)

make_lemma is_iso.map_inv_id
make_lemma is_iso.inv_map_id
attribute [simp,ematch] is_iso.map_inv_id_lemma is_iso.inv_map_id_lemma

namespace is_iso

instance (X : C) : is_iso (𝟙 X) := 
{ inv := 𝟙 X, }

instance of_iso         (f : X ≅ Y) : is_iso f.map :=
{ inv   := f.inv,
  map_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_map_id := begin /- `obviously'` says: -/ simp end }
instance of_Isomorphism_inverse (f : X ≅ Y) : is_iso f.inv  := 
{ inv   := f.map,
  map_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_map_id := begin /- `obviously'` says: -/ simp end }

end is_iso

class epi  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance epi_of_iso  (f : X ⟶ Y) [is_iso f] : epi f  := 
{ left_cancellation := begin
                         -- This is an interesting test case for better rewrite automation.
                         intros,
                         rw [←category.left_identity_lemma C g, ←category.left_identity_lemma C h],
                         rw [← is_iso.inv_map_id_lemma f],
                         erw [category.associativity_lemma, w, category.associativity_lemma],
                       end }
instance mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f := 
{ right_cancellation := begin
                         intros,
                         rw [←category.right_identity_lemma C g, ←category.right_identity_lemma C h],
                         rw [← is_iso.map_inv_id_lemma f],
                         erw [←category.associativity_lemma, w, ←category.associativity_lemma]
                       end }

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := 
⟨ λ p, epi.left_cancellation g h p, begin /- `obviously'` says: -/ intros, cases a, refl end ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := 
⟨ λ p, mono.right_cancellation g h p, begin /- `obviously'` says: -/ intros, cases a, refl end ⟩

namespace Functor

universes u₁ v₁ u₂ v₂ 
variables {D : Type u₂}

variables [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition on_isos (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F +> X) ≅ (F +> Y) :=
{ map := F &> i.map,
  inv := F &> i.inv }

@[simp,ematch] lemma on_isos_map (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).map = F &> i.map := rfl
@[simp,ematch] lemma on_isos_inv (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).inv = F &> i.inv := rfl

end Functor

end category_theory