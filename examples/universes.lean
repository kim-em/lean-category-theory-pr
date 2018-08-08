universes u₁ v₁ u₂ v₂

structure Category :=
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

def FunctorCategory (C : Category.{u₁ v₁}) (D : Category.{u₂ v₂}) : Category :=
by refine { Obj := Functor C D,
            Hom := λ F G, NaturalTransformation F G, .. } ; sorry

set_option pp.universes true
#print FunctorCategory -- Category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}

/-
Summarising, we have:
  Category : Type (max (u₁+1) (v₁+1))
  C : Category.{u₁ v₁}
  D : Category.{u₂ v₂}
  Functor C D : Type (max u₁ u₂ v₁ v₂)
  NaturalTransformation : Type (max u₁ v₂)
  FunctorCategory : Category.{(max u₁ u₂ v₁ v₂) (max u₁ v₂)}

If uᵢ=vᵢ+1, we then have:
  Category : Type (v₁+2)
  C : Category.{v₁+1 v₁}
  D : Category.{v₂+1 v₂}
  Functor C D : Type (max v₁+1 v₂+1)
  NaturalTransformation : Type (max (v₁+1) v₂)
  FunctorCategory C D : Category.{(max (v₁+1) (v₂+1)) (max (v₁+1) v₂)}

If moreover v₂=v₁, then
  FunctorCategory C D : Category.{(v₁+1) (v₁+1)}
That is, the FunctorCategory is a whole level up (but small...)

If C is a small category, so u₁=v₁, and D has u₂=v₂+1, we then have:
  Functor C D : Type (max v₁ v₂+1)
  FunctorCategory C D : Category.{(mav v₁ (v₂+1)) (max v₁ v₂)}

If moreover v₂=v₁, then
  FunctorCategory C D : Category.{(v₁+1) v₁}
That is, FunctorCategory is a large category at the same level as we started.

-/