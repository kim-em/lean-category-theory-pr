import tactic.interactive

universe u

class category (Obj : Type u) : Type (u+1) :=
(Hom : Obj → Obj → Type u)
(identity : Π X : Obj, Hom X X)

notation `𝟙` := category.identity     -- type as \b1
infixr ` ⟶ `:10  := category.Hom     -- type as \h

variable (C : Type u)
variable [𝒞 : category C]
variable (D : Type u)
variable [𝒟 : category D]
include 𝒞 𝒟

instance ProductCategory : category (C × D) := 
{ Hom            := λ X Y, ((X.1) ⟶ (Y.1)) × ((X.2) ⟶ (Y.2)),
  identity       := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩ }    

@[simp] lemma ProductCategory.identity (X : C) (Y : D) : 𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := rfl

structure Functor  :=
(onObjects     : C → D)
(onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((onObjects X) ⟶ (onObjects Y)))
(identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (onObjects X))

attribute [simp] Functor.identities

infixr ` +> `:70 := Functor.onObjects
infixr ` &> `:70 := Functor.onMorphisms 
infixr ` ↝ `:70 := Functor -- type as \lea 

variables {C} {D}

structure NaturalTransformation (F G : C ↝ D) : Type u :=
(components: Π X : C, (F +> X) ⟶ (G +> X))

infixr ` ⟹ `:50  := NaturalTransformation

instance {F G : C ↝ D} : has_coe_to_fun (F ⟹ G) :=
{ F   := λ α, Π X : C, (F +> X) ⟶ (G +> X),
  coe := λ α, α.components }

def IdentityNaturalTransformation (F : C ↝ D) : F ⟹ F := 
{ components := λ X, 𝟙 (F +> X) }

instance FunctorCategory : category (C ↝ D) := 
{ Hom            := λ F G, F ⟹ G,
  identity       := λ F, IdentityNaturalTransformation F }

@[simp] lemma FunctorCategory.identity.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F) X = 𝟙 (F +> X) := rfl

lemma test (E : Type u) [ℰ : category E] (X : C) (Y : D) (F : C ↝ (D ↝ E)) : (F &> (prod.fst (𝟙 (X, Y)))) Y = 𝟙 ((F +> X) +> Y) :=
begin
  -- Really, `simp` should just work, finishing the goal.
  -- However this doesn't work:
  success_if_fail {simp},
  -- Notice that rewriting with that simp lemma succeeds:
  rw ProductCategory.identity,
  dsimp,
  -- Again, this `simp` fails:
  success_if_fail {simp},
  rw Functor.identities,
  -- Finally, at this stage `simp` manages to apply FunctorCategory.identity.components
  simp,
end

lemma test' (E : Type u) [ℰ : category E] (X : C) (Y : D) (F : C ↝ (D ↝ E)) : (F &> (prod.fst (𝟙 (X, Y)))) Y = 𝟙 ((F +> X) +> Y) :=
begin
  -- If we unfold all the coercions first, at least `simp` gets started
  unfold_coes,
  simp, 
  -- But doesn't finish, because with the coercions gone, FunctorCategory.identity.components doesn't apply anymore!
  admit
end

-- We can define an alternative version of that @[simp] lemma, with the coercion removed. 
@[simp] lemma FunctorCategory.identity.components' (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F).components X = 𝟙 (F +> X) := rfl

lemma test'' (E : Type u) [ℰ : category E] (X : C) (Y : D) (F : C ↝ (D ↝ E)) : (F &> (prod.fst (𝟙 (X, Y)))) Y = 𝟙 ((F +> X) +> Y) :=
begin
  unfold_coes,
  simp,
  -- At this stage, we've recovered reasonable automation, at the expense of having to
  -- state lemmas twice, once with the coercions (for the humans) and once without (for the simplifier).
end
