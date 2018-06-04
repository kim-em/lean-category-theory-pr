import ...types
import ..instances

open categories.universal
open categories.isomorphism
namespace categories.types

universe u

instance Types_has_Products : has_Products (Type u) := 
{ product := λ I φ, { product       := Π i : I, φ i,
                      projection    := λ i x, x i,
                      map           := λ Z f z i, f i z } }

instance Types_has_Coproducts : has_Coproducts (Type u) := 
{ coproduct := λ I φ, { coproduct     := Σ i : I, φ i,
                        inclusion     := λ i x, ⟨ i, x ⟩,
                        map           := λ Z f p, f p.1 p.2 } }

-- Even though this can be automatically generated from `Types_has_Products`, this is a cleaner version.
instance Types_has_BinaryProducts : has_BinaryProducts.{u+1 u} (Type u) := 
{ binary_product := λ X Y, { product             := X × Y,
                             left_projection     := prod.fst,
                             right_projection    := prod.snd,
                             map                 := λ _ f g z, (f z, g z) } }

instance Types_has_BinaryCoproducts : has_BinaryCoproducts.{u+1 u} (Type u) := 
{ binary_coproduct := λ X Y, { coproduct           := X ⊕ Y,
                               left_inclusion      := sum.inl,
                               right_inclusion     := sum.inr,
                               map                 := λ _ f g z, sum.cases_on z f g,
                               uniqueness          := λ Z f g lw rw, begin tidy, cases x, tidy end } }

instance Types_has_Equalizers : has_Equalizers.{u+1 u} (Type u) := 
{ equalizer := λ α β f g, { equalizer     := {x : α // f x = g x},
                            inclusion     := λ x, x.val,
                            map           := λ γ k h g, ⟨ k g, by obviously ⟩ } }

@[semiapplicable] lemma constant_on_quotient {α β : Type u} (f g : α → β) {Z : Type u} (k : β → Z) (x y : β) (h : eqv_gen (λ (x y : β), ∃ (a : α), f a = x ∧ g a = y) x y) (w : ∀ (a : α), k (f a) = k (g a)) : k x = k y :=
begin
  induction h,
  obviously
end

instance Types_has_Coequalizers : has_Coequalizers.{u+1 u} (Type u) := 
{ coequalizer := λ α β f g, by letI s := eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y);
                            exact 
                            { coequalizer   := quotient s,
                              projection    := by obviously,
                              map           := λ Z k w, quotient.lift k (by obviously),
                              witness       := begin tidy, apply eqv_gen.rel, tidy, end } }
end categories.types