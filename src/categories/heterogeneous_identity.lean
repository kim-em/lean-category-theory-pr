import .functor
import .isomorphism

universes u v

namespace categories

open categories.isomorphism
open categories.functor

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y :=
begin
  rw p,
  exact (Isomorphism.refl Y),
end

@[simp,ematch] lemma eq_to_iso.refl (X : C) : eq_to_iso (eq.refl X) = (Isomorphism.refl X) :=
begin
  refl,
end

@[simp,ematch] lemma eq_to_iso.trans {X Y Z : C} (p : X = Y) (q : Y = Z) : (eq_to_iso p) ♢ (eq_to_iso q) = eq_to_iso (p.trans q) :=
begin
  induction p,
  induction q,
  tidy,
end

end categories

open categories
namespace categories.functor

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma Functor.eq_to_iso (F : C ↝ D) {X Y : C} (p : X = Y) : F.onIsomorphisms (eq_to_iso p) = eq_to_iso (congr_arg F.onObjects p) :=
begin
  induction p,
  tidy,
end
end categories.functor

