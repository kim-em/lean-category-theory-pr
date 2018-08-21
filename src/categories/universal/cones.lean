-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import .initial

open category_theory
open category_theory.initial

namespace category_theory.universal

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

structure Cone (F : J ↝ C) : Type (max u v) :=
(cone_point    : C)
(cone_maps     : Π j : J, cone_point ⟶ (F j))
(commutativity : Π {j k : J}, Π f : j ⟶ k, (cone_maps j) ≫ (F.map f) = cone_maps k . obviously)

restate_axiom Cone.commutativity
attribute [simp,ematch] Cone.commutativity_lemma

variable {F : J ↝ C}

structure ConeMorphism (X Y : Cone F) : Type v :=
(cone_morphism : X.cone_point ⟶ Y.cone_point)
(commutativity : Π j : J, cone_morphism ≫ (Y.cone_maps j) = (X.cone_maps j) . obviously)

restate_axiom ConeMorphism.commutativity
attribute [simp,ematch] ConeMorphism.commutativity_lemma

namespace ConeMorphism

@[simp,ematch] def commutativity_lemma_assoc {X Y : Cone F} (c : ConeMorphism X Y) (j : J) {Z : C} (z : (F j) ⟶ Z): c.cone_morphism ≫ Y.cone_maps j ≫ z = X.cone_maps j ≫ z :=
begin
  /- obviously' say: -/
  rw ← category.assoc,
  simp,
end

@[extensionality] lemma ext {X Y : Cone F} {f g : ConeMorphism X Y} (w : f.cone_morphism = g.cone_morphism) : f = g :=
begin
  /- obviously' say: -/
  induction f,
  induction g,
  dsimp at w,
  induction w,
  refl,
end

end ConeMorphism

instance Cones (F : J ↝ C) : category.{(max u v) v} (Cone F) :=
{ hom      := λ X Y, ConeMorphism X Y,
  comp    := λ X Y Z f g, { cone_morphism := f.cone_morphism ≫ g.cone_morphism,
                            commutativity := begin /- `obviously'` says: -/ intros, simp end },
  id      := λ X, { cone_morphism := 𝟙 X.cone_point, 
                    commutativity := begin /- `obviously'` says: -/ intros, simp end },
  id_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }

-- TODO rename or namespace?
@[simp] lemma Cones.identity.cone_morphism {F : J ↝ C} (c : Cone F) : (𝟙 c : ConeMorphism c c).cone_morphism = 𝟙 (c.cone_point) := rfl
@[simp] lemma Cones.compose.cone_morphism {F : J ↝ C} {c d e : Cone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : ConeMorphism c e).cone_morphism = (f : ConeMorphism c d).cone_morphism ≫ (g : ConeMorphism d e).cone_morphism := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def Cones_functoriality (F : J ↝ C) (G : C ↝ D) : (Cone F) ↝ (Cone (F ⋙ G)) := 
{ obj      := λ X, { cone_point    := G X.cone_point,
                     cone_maps     := λ j, G.map (X.cone_maps j), 
                     commutativity := begin /- `obviously'` says: -/ intros, simp, erw [←functor.map_comp_lemma, Cone.commutativity_lemma] end },
  map'     := λ X Y f, { cone_morphism := G.map f.cone_morphism,
                         commutativity := begin /- `obviously'` says: -/ intros, dsimp, erw [←functor.map_comp_lemma, ConeMorphism.commutativity_lemma] end },
  map_id   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  map_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }
end

structure Cocone (F : J ↝ C) :=
(cocone_point  : C)
(cocone_maps   : Π j : J, (F j) ⟶ cocone_point)
(commutativity : Π {j k : J}, Π f : j ⟶ k, (F.map f) ≫ (cocone_maps k) = cocone_maps j . obviously)

restate_axiom Cocone.commutativity
attribute [simp,ematch] Cocone.commutativity_lemma

structure CoconeMorphism (X Y : Cocone F) :=
(cocone_morphism : X.cocone_point ⟶ Y.cocone_point)
(commutativity   : Π j : J, (X.cocone_maps j) ≫ cocone_morphism = (Y.cocone_maps j) . obviously)

restate_axiom CoconeMorphism.commutativity
attribute [simp,ematch] CoconeMorphism.commutativity_lemma

namespace CoconeMorphism
@[simp,ematch] def commutativity_lemma_assoc {X Y : Cocone F} (c : CoconeMorphism X Y) (j : J) {Z : C} (z : Y.cocone_point ⟶ Z): (X.cocone_maps j) ≫ c.cocone_morphism ≫ z = (Y.cocone_maps j) ≫ z :=
begin
  -- `obviously'` says:
  erw [←category.assoc_lemma, CoconeMorphism.commutativity_lemma]
end

@[extensionality] lemma ext {X Y : Cocone F} {f g : CoconeMorphism X Y} (w : f.cocone_morphism = g.cocone_morphism) : f = g :=
begin 
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at *,
  induction w,
  refl,
end
end CoconeMorphism

instance Cocones (F : J ↝ C) : category.{(max u v) v} (Cocone F) := 
{ hom     := λ X Y, CoconeMorphism X Y,
  comp    := λ X Y Z f g, { cocone_morphism := f.cocone_morphism ≫ g.cocone_morphism,
                            commutativity   := begin /- `obviously'` says: -/ intros, simp end },
  id      := λ X,         { cocone_morphism := 𝟙 X.cocone_point,
                            commutativity   := begin /- `obviously'` says: -/ intros, simp end },
  id_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }

-- TODO rename or namespace?
@[simp] lemma Cocones.identity.cone_morphism {F : J ↝ C} (c : Cocone F) : (𝟙 c : CoconeMorphism c c).cocone_morphism = 𝟙 (c.cocone_point) := rfl
@[simp] lemma Cocones.compose.cone_morphism {F : J ↝ C} {c d e : Cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : CoconeMorphism c e).cocone_morphism = (f : CoconeMorphism c d).cocone_morphism ≫ (g : CoconeMorphism d e).cocone_morphism := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def Cocones_functoriality (F : J ↝ C) (G : C ↝ D) : (Cocone F) ↝ (Cocone (F ⋙ G)) := 
{ obj      := λ X,     { cocone_point    := G X.cocone_point,
                         cocone_maps     := λ j, G.map (X.cocone_maps j),
                         commutativity   := begin /- `obviously'` says: -/ intros, simp, erw [←functor.map_comp_lemma, Cocone.commutativity_lemma] end },
  map'     := λ X Y f, { cocone_morphism := G.map f.cocone_morphism,
                         commutativity   := begin /- `obviously'` says: -/ intros, dsimp, erw [←functor.map_comp_lemma, CoconeMorphism.commutativity_lemma] end },
  map_id   := begin /- `obviously'` says -/ intros, ext, dsimp, simp end,
  map_comp := begin /- `obviously'` says -/ intros, ext, dsimp, simp end }
end

def LimitCone     (F : J ↝ C) := terminal_object (Cone F)
def ColimitCocone (F : J ↝ C) := initial_object (Cocone F)

end category_theory.universal

namespace category_theory.functor

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [category.{u v} C] {D : Type u} [category.{u v} D]
variable {F : J ↝ C}

open category_theory.universal

def on_cone   (G : C ↝ D) (c : Cone F)   : Cone (F ⋙ G)   := (Cones_functoriality F G) c
def on_cocone (G : C ↝ D) (c : Cocone F) : Cocone (F ⋙ G) := (Cocones_functoriality F G) c

end category_theory.functor