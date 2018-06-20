-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..functor

open categories
open categories.functor
open categories.initial

namespace categories.universal

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

structure Cone (F : J ↝ C) : Type (max u v) :=
  (cone_point    : C)
  (cone_maps     : Π j : J, cone_point ⟶ (F +> j))
  (commutativity : Π {j k : J}, Π f : j ⟶ k, (cone_maps j) ≫ (F &> f) = cone_maps k . obviously)

make_lemma Cone.commutativity
attribute [simp,ematch] Cone.commutativity_lemma

variable {F : J ↝ C}

structure ConeMorphism (X Y : Cone F) : Type v :=
  (cone_morphism : X.cone_point ⟶ Y.cone_point)
  (commutativity : Π j : J, cone_morphism ≫ (Y.cone_maps j) = (X.cone_maps j) . obviously)

make_lemma ConeMorphism.commutativity
attribute [simp,ematch] ConeMorphism.commutativity_lemma

@[simp,ematch] def ConeMorphism.commutativity_lemma_assoc {X Y : Cone F} (c : ConeMorphism X Y) (j : J) {Z : C} (z : (F +> j) ⟶ Z): c.cone_morphism ≫ Y.cone_maps j ≫ z = X.cone_maps j ≫ z :=
begin
  rw ← category.associativity,
  simp,
end

@[extensionality] lemma ConeMorphism_componentwise_equal {X Y : Cone F} {f g : ConeMorphism X Y} (w : f.cone_morphism = g.cone_morphism) : f = g :=
begin
  induction f,
  induction g,
  dsimp at w,
  induction w,
  refl,
end

instance Cones (F : J ↝ C) : category.{(max u v) v} (Cone F) :=
{ Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, { cone_morphism := f.cone_morphism ≫ g.cone_morphism,
                                   commutativity := begin
                                                      -- `obviously'` says:
                                                      intros,
                                                      simp
                                                    end },
  identity       := λ X,         { cone_morphism := 𝟙 X.cone_point, 
                                   commutativity := begin
                                                      -- `obviously'` says:
                                                      intros,
                                                      simp
                                                    end },
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.ConeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.ConeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.ConeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end }

@[simp] lemma Cones.identity.cone_morphism {F : J ↝ C} (c : Cone F) : (𝟙 c : ConeMorphism c c).cone_morphism = 𝟙 (c.cone_point) := by refl
@[simp] lemma Cones.compose.cone_morphism {F : J ↝ C} {c d e : Cone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : ConeMorphism c e).cone_morphism = (f : ConeMorphism c d).cone_morphism ≫ (g : ConeMorphism d e).cone_morphism := by refl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

definition Cones_functoriality (F : J ↝ C) (G : C ↝ D) : (Cone F) ↝ (Cone (F ⋙ G)) := 
{ onObjects     := λ X,     { cone_point    := G +> X.cone_point,
                              cone_maps     := λ j, G &> (X.cone_maps j), 
                              commutativity := begin
                                                 -- `obviously'` says:
                                                 intros,
                                                 simp,
                                                 erw [←Functor.functoriality_lemma, Cone.commutativity_lemma]
                                               end },
  onMorphisms   := λ X Y f, { cone_morphism := G &> f.cone_morphism,
                              commutativity := begin
                                                 -- `obviously'` says:
                                                 intros,
                                                 dsimp,
                                                 erw [←Functor.functoriality_lemma, ConeMorphism.commutativity_lemma]
                                               end },
  identities    := begin
                     -- `obviously'` says:
                     intros,
                     apply categories.universal.ConeMorphism_componentwise_equal,
                     dsimp,
                     simp
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     apply categories.universal.ConeMorphism_componentwise_equal,
                     dsimp,
                     simp
                   end }
end

structure Cocone (F : J ↝ C) :=
  (cocone_point  : C)
  (cocone_maps   : Π j : J, (F +> j) ⟶ cocone_point)
  (commutativity : Π {j k : J}, Π f : j ⟶ k, (F &> f) ≫ (cocone_maps k) = cocone_maps j . obviously)

make_lemma Cocone.commutativity
attribute [simp,ematch] Cocone.commutativity_lemma

structure CoconeMorphism (X Y : Cocone F) :=
  (cocone_morphism : X.cocone_point ⟶ Y.cocone_point)
  (commutativity   : Π j : J, (X.cocone_maps j) ≫ cocone_morphism = (Y.cocone_maps j) . obviously)

make_lemma CoconeMorphism.commutativity
attribute [simp,ematch] CoconeMorphism.commutativity_lemma

@[simp,ematch] def CoconeMorphism.commutativity_lemma_assoc {X Y : Cocone F} (c : CoconeMorphism X Y) (j : J) {Z : C} (z : Y.cocone_point ⟶ Z): (X.cocone_maps j) ≫ c.cocone_morphism ≫ z = (Y.cocone_maps j) ≫ z :=
begin
  -- `obviously'` says:
  erw [←category.associativity_lemma, CoconeMorphism.commutativity_lemma]
end

@[extensionality] lemma CoconeMorphism_componentwise_equal {X Y : Cocone F} {f g : CoconeMorphism X Y} (w : f.cocone_morphism = g.cocone_morphism) : f = g :=
begin
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at *,
  induction w,
  refl,
end

instance Cocones (F : J ↝ C) : category.{(max u v) v} (Cocone F) := 
{ Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, { cocone_morphism := f.cocone_morphism ≫ g.cocone_morphism,
                                   commutativity   := begin
                                                        -- `obviously'` says:
                                                        intros,
                                                        simp
                                                      end },
  identity       := λ X,         { cocone_morphism := 𝟙 X.cocone_point,
                                   commutativity   := begin
                                                        -- `obviously'` says:
                                                        intros,
                                                        simp
                                                      end },
  left_identity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.CoconeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end,
  right_identity := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.CoconeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end,
  associativity  := begin
                      -- `obviously'` says:
                      intros,
                      apply categories.universal.CoconeMorphism_componentwise_equal,
                      dsimp,
                      simp
                    end }

@[simp] lemma Cocones.identity.cone_morphism {F : J ↝ C} (c : Cocone F) : (𝟙 c : CoconeMorphism c c).cocone_morphism = 𝟙 (c.cocone_point) := by refl
@[simp] lemma Cocones.compose.cone_morphism {F : J ↝ C} {c d e : Cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : CoconeMorphism c e).cocone_morphism = (f : CoconeMorphism c d).cocone_morphism ≫ (g : CoconeMorphism d e).cocone_morphism := by refl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

definition Cocones_functoriality (F : J ↝ C) (G : C ↝ D) : (Cocone F) ↝ (Cocone (F ⋙ G)) := 
{ onObjects     := λ X,     { cocone_point    := G +> X.cocone_point,
                              cocone_maps     := λ j, G &> (X.cocone_maps j),
                              commutativity   := begin
                                                   -- `obviously'` says:
                                                   intros,
                                                   simp,
                                                   erw [←Functor.functoriality_lemma, Cocone.commutativity_lemma]
                                                 end },
  onMorphisms   := λ X Y f, { cocone_morphism := G &> f.cocone_morphism,
                              commutativity   := begin
                                                   -- `obviously'` says:
                                                   intros,
                                                   dsimp,
                                                   erw [←Functor.functoriality_lemma, CoconeMorphism.commutativity_lemma]
                                                 end },
  identities    := begin
                     -- `obviously'` says
                     intros,
                     apply categories.universal.CoconeMorphism_componentwise_equal,
                     dsimp,
                     simp
                   end,
  functoriality := begin
                     -- `obviously'` says
                     intros,
                     apply categories.universal.CoconeMorphism_componentwise_equal,
                     dsimp,
                     simp
                   end }
end

definition LimitCone     (F : J ↝ C) := TerminalObject (Cone F)
definition ColimitCocone (F : J ↝ C) := InitialObject (Cocone F)

end categories.universal

namespace categories.functor

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [category.{u v} C] {D : Type u} [category.{u v} D]
variable {F : J ↝ C}

open categories.universal

definition Functor.onCones   (G : C ↝ D) (c : Cone F)   : Cone (F ⋙ G)   := (Cones_functoriality F G) +> c
definition Functor.onCocones (G : C ↝ D) (c : Cocone F) : Cocone (F ⋙ G) := (Cocones_functoriality F G) +> c

end categories.functor