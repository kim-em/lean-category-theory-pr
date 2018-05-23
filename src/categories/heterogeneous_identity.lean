import .functor
import .isomorphism

universe u₁

-- @[simp] lemma eq.mpr.trans {α β γ: Prop} (p : α = β) (q : β = γ) (g : γ) : eq.mpr (eq.trans p q) g = eq.mpr p (eq.mpr q g) :=
-- begin
--   induction p,
--   induction q,
--   refl,
-- end

-- @[simp] lemma eq.mpr.propext {α : Sort u₁} (a : α) : eq.mpr (propext (eq_self_iff_true a)) trivial = eq.refl a :=
-- begin
--   refl,
-- end

-- @[simp] lemma eq.mpr.refl {α : Sort u₁} (a b : α) (p : a = b) : (eq.mpr (congr_fun (congr_arg eq p) b) (eq.refl b)) = p :=
-- begin
--   induction p,
--   refl,
-- end

namespace categories

open categories.isomorphism
open categories.functor

def eq_to_iso {C : Type (u₁+1)} [category C] {X Y : C} (p : X = Y) : X ≅ Y :=
begin
  rw p,
  exact (Isomorphism.refl Y),
end

@[simp,ematch] lemma eq_to_iso.refl {C : Type (u₁+1)} [category C] (X : C) : eq_to_iso (eq.refl X) = (Isomorphism.refl X) :=
begin
  refl,
end

@[simp,ematch] lemma eq_to_iso.trans {C : Type (u₁+1)} [category C] {X Y Z : C} (p : X = Y) (q : Y = Z) : (eq_to_iso p) ♢ (eq_to_iso q) = eq_to_iso (p.trans q) :=
begin
  induction p,
  induction q,
  tidy,
end
end categories

open categories
namespace categories.functor

@[simp,ematch] lemma Functor.eq_to_iso {C : Type (u₁+1)} [category C] {D : Type (u₁+1)} [category D] (F : C ↝ D) (X Y : C) (p : X = Y) : F.onIsomorphisms (eq_to_iso p) = eq_to_iso (congr_arg F.onObjects p) :=
begin
  induction p,
  tidy,
end
end categories.functor

