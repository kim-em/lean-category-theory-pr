-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.category
import category_theory.functor

import .tactics

universes u v

namespace category_theory

structure iso {C : Type u} [category.{u v} C] (X Y : C) :=
(hom : X ⟶ Y)
(inv : Y ⟶ X)
(hom_inv_id : hom ≫ inv = 𝟙 X . obviously)
(inv_hom_id : inv ≫ hom = 𝟙 Y . obviously)

restate_axiom iso.hom_inv_id
restate_axiom iso.inv_hom_id
attribute [simp,ematch] iso.hom_inv_id_lemma iso.inv_hom_id_lemma

infixr ` ≅ `:10  := iso             -- type as \cong

variable {C : Type u}
variable [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

namespace iso

instance : has_coe (iso.{u v} X Y) (X ⟶ Y) :=
{ coe := iso.hom }

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma hom_inv_id_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.hom ≫ I.inv ≫ f = f := 
begin
  -- `obviously'` says:
  rw [←category.assoc_lemma, iso.hom_inv_id_lemma, category.id_comp_lemma]
end

@[simp,ematch] lemma inv_hom_id_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inv ≫ I.hom ≫ f = f := 
begin
  -- `obviously'` says:
  rw [←category.assoc_lemma, iso.inv_hom_id_lemma, category.id_comp_lemma]
end

@[extensionality] lemma ext
  (α β : X ≅ Y)
  (w : α.hom = β.hom) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        induction w,
        dsimp at *,
        rw [← category.id_comp_lemma C k, ←wα2, category.assoc_lemma, wβ1, category.comp_id_lemma]
      end,
    -- `obviously'` says:
    induction p, induction w,
    refl
  end

def refl (X : C) : X ≅ X := 
{ hom := 𝟙 X,
  inv := 𝟙 X, 
  hom_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_hom_id := begin /- `obviously'` says: -/ simp end }

-- TODO maybe these can have ematch?
@[simp] lemma refl_map (X : C) : (iso.refl X).hom = 𝟙 X := rfl
@[simp] lemma refl_inv  (X : C) : (iso.refl X).inv  = 𝟙 X := rfl

def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z := 
{ hom := α.hom ≫ β.hom,
  inv := β.inv ≫ α.inv,
  hom_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_hom_id := begin /- `obviously'` says: -/ simp end }

infixr ` ♢ `:80 := iso.trans -- type as \diamonds

@[simp,ematch] lemma trans_hom (α : X ≅ Y) (β : Y ≅ Z) : (α ♢ β).hom = α.hom ≫ β.hom := rfl
@[simp,ematch] lemma trans_inv (α : X ≅ Y) (β : Y ≅ Z) : (α ♢ β).inv  = β.inv ≫ α.inv   := rfl

def symm (I : X ≅ Y) : Y ≅ X := 
{ hom := I.inv,
  inv := I.hom,
  hom_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_hom_id := begin /- `obviously'` says: -/ simp end }

end iso

class is_iso (f : X ⟶ Y) :=
(inv : Y ⟶ X)
(hom_inv_id : f ≫ inv = 𝟙 X . obviously)
(inv_hom_id : inv ≫ f = 𝟙 Y . obviously)

restate_axiom is_iso.hom_inv_id
restate_axiom is_iso.inv_hom_id
attribute [simp,ematch] is_iso.hom_inv_id_lemma is_iso.inv_hom_id_lemma

namespace is_iso

instance (X : C) : is_iso (𝟙 X) := 
{ inv := 𝟙 X, 
  hom_inv_id := by obviously',
  inv_hom_id := by obviously' }

instance of_iso         (f : X ≅ Y) : is_iso f.hom :=
{ inv   := f.inv,
  hom_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_hom_id := begin /- `obviously'` says: -/ simp end }
instance of_iso_inverse (f : X ≅ Y) : is_iso f.inv  := 
{ inv   := f.hom,
  hom_inv_id := begin /- `obviously'` says: -/ simp end,
  inv_hom_id := begin /- `obviously'` says: -/ simp end }

end is_iso

class epi  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance epi_of_iso  (f : X ⟶ Y) [is_iso f] : epi f  := 
{ left_cancellation := begin
                         -- This is an interesting test case for better rewrite automation.
                         intros,
                         rw [←category.id_comp_lemma C g, ←category.id_comp_lemma C h],
                         rw [← is_iso.inv_hom_id_lemma f],
                         erw [category.assoc_lemma, w, category.assoc_lemma],
                       end }
instance mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f := 
{ right_cancellation := begin
                         intros,
                         rw [←category.comp_id_lemma C g, ←category.comp_id_lemma C h],
                         rw [← is_iso.hom_inv_id_lemma f],
                         erw [←category.assoc_lemma, w, ←category.assoc_lemma]
                       end }

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := 
⟨ λ p, epi.left_cancellation g h p, begin /- `obviously'` says: -/ intros, cases a, refl end ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := 
⟨ λ p, mono.right_cancellation g h p, begin /- `obviously'` says: -/ intros, cases a, refl end ⟩

namespace functor

universes u₁ v₁ u₂ v₂ 
variables {D : Type u₂}

variables [𝒟 : category.{u₂ v₂} D]
include 𝒟

def on_isos (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F X) ≅ (F Y) :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id := by obviously',
  inv_hom_id := by obviously' }

@[simp,ematch] lemma on_isos_hom (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).hom = F.map i.hom := rfl
@[simp,ematch] lemma on_isos_inv (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).inv = F.map i.inv := rfl

end functor

end category_theory