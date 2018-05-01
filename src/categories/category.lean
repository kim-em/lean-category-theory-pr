-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .tactics

namespace categories

universes u v

/-
The universe annotations may be suprising here!
Note that we ask the Obj : Type (u+1), while Hom X Y : Type u.
This is motivated by:
1. As `category` is a class, we want all universe levels to be determined by its parameters.
   (Thus we want to avoid independent universe levels for Obj and Hom.)
2. The basic example of category is the category of types and functions.
   This example matches the definition here.
3. It so far doesn't seem to cause any problems!
-/

/- 
The propositional fields of `category` are annotated with the auto_param `obviously_stub`, which is just a synonym for `skip`.
Actually, there is a tactic called `obviously` which is not part of this pull request, which should be used here. It successfully
discharges a great many of these goals. For now, proofs which could be provided entirely by `obviously` (and hence omitted entirely
and discharged by an auto_param), are all marked with a comment "-- obviously says:".
-/

class uv_category (Obj : Type u) : Type (max u (v+1)) :=
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f . obviously)
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f . obviously)
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), compose (compose f g) h = compose f (compose g h) . obviously)

notation `𝟙` := uv_category.identity    -- type as \b1
infixr ` ≫ `:80 := uv_category.compose -- type as \gg
infixr ` ⟶ `:10  := uv_category.Hom     -- type as \h

-- make_lemma is a command that creates a lemma from a structure field, discarding all auto_param wrappers from the type.
-- FIXME these three need better names.
make_lemma uv_category.left_identity
make_lemma uv_category.right_identity
make_lemma uv_category.associativity
-- We tag some lemmas with the attribute @[ematch], for later automation.
attribute [simp,ematch] uv_category.left_identity_lemma uv_category.right_identity_lemma uv_category.associativity_lemma 
attribute [ematch] uv_category.associativity_lemma 

class category (C : Type (u+1)) extends uv_category.{u+1 u} C.
class small_category (C : Type u) extends uv_category.{u u} C.

section
variable {C : Type (u+1)}
variables {X Y : C}
variable [category C]

instance category.has_one : has_one (X ⟶ X) := 
{ one := 𝟙 X }

@[simp] def category.left_identity_lemma' (f : X ⟶ Y) : 1 ≫ f = f := begin unfold has_one.one, simp end
@[simp] def category.right_identity_lemma' (f : X ⟶ Y) : f ≫ 1 = f := begin unfold has_one.one, simp end
end

section
variable {C : Type u}
variables {X Y : C}
variable [small_category C]

instance small_category.has_one : has_one (X ⟶ X) := 
{ one := 𝟙 X }

@[simp] def small_category.left_identity_lemma' (f : X ⟶ Y) : 1 ≫ f = f := begin unfold has_one.one, simp end
@[simp] def small_category.right_identity_lemma' (f : X ⟶ Y) : f ≫ 1 = f := begin unfold has_one.one, simp end
end

end categories
