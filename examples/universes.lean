universes u₁ v₁ u₂ v₂

structure Category : Type (max (u₁+1) (v₁+1)) :=
  (Obj : Type u₁)
  (Hom : Obj → Obj → Type v₁)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f)
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), compose (compose f g) h = compose f (compose g h))

structure Functor (C : Category.{u₁ v₁}) (D : Category.{u₂ v₂}) :=
  (onObjects     : C.Obj → D.Obj)
  (onMorphisms   : Π {X Y : C.Obj}, (C.Hom X Y) → (D.Hom (onObjects X) (onObjects Y)))
  (identities    : ∀ (X : C.Obj), onMorphisms (C.identity X) = D.identity (onObjects X))
  (functoriality : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z), onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))

structure NaturalTransformation {C : Category.{u₁ v₁}} {D : Category.{u₂ v₂}} (F G : Functor C D) :=
  (components: Π X : C.Obj, D.Hom (F.onObjects X) (G.onObjects X))
  (naturality: ∀ {X Y : C.Obj} (f : C.Hom X Y), D.compose (F.onMorphisms f) (components Y) = D.compose (components X) (G.onMorphisms f))

#print Category -- Type (max (u₁+1) (v₁+1))
#print Functor  -- Type (max u₁ u₂ v₁ v₂)
#print NaturalTransformation -- Type (max u₁ v₂)

definition FunctorCategory (C : Category.{u₁ v₁}) (D : Category.{u₂ v₂}) : Category :=
by refine { Obj := Functor C D,
            Hom := λ F G, NaturalTransformation F G, .. } ; sorry

set_option pp.universes true
#print FunctorCategory -- Category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}

/-
Summarising this, we have:

Category.{u₁ v₁} : Type (max (u₁+1) (v₁+1))
C : Category.{u₁ v₁}
D : Category.{u₂ v₂}
Functor C D : Type (max u₁ u₂ v₁ v₂)
F G : Functor C D
NaturalTransformation F G : Type (max u₁ v₂)
FunctorCategory C D : Category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}

Let's now experiment with the definitions
`SmallCategory.{u} := Category.{u u}` and `LargeCategory.{u} := Category.{u+1 u}`.

If `C : SmallCategory.{u}, D : SmallCategory.{v}`, then `FunctorCategory C D : Category.{(max u v) (max u v)}`,
that is, we can arrange for `FunctorCategory C D` to be a `SmallCategory.{(max u v)}`.

If `C : SmallCategory.{u}, D : LargeCategory.{v}`, then `FunctorCategory C D : Category.{(max u (v+1)) (max u v)}`,
which is a bit awkward. However if we further specialise to `u = v`, then we can
arrange for `FunctorCategory C D` to be a `LargeCategory.{u}`.

If `C : LargeCategory.{u}, D : LargeCategory.{v}`, then `FunctorCategory C D : Category.{((max u v)+1) (max (u+1) v)}`,
which is again awkward, although when `u = v` we can arrange `FunctorCategory C D` to be a `SmallCategory.{u+1}`.
-/