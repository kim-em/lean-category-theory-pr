import ...types
import ..instances

open categories.universal
open categories.isomorphism
namespace categories.types

universe u

instance Types_has_Products : has_Products (Type u) := 
{ product := λ I φ, { product       := Π i : I, φ i,
                      projection    := λ i x, x i,
                      map           := λ Z f z i, f i z, 
                      factorisation := begin
                                         -- `obviously'` says:
                                         intros,
                                         refl
                                       end,
                      uniqueness    := begin
                                         -- `obviously'` says:
                                         intros,
                                         apply funext,
                                         intros,
                                         apply funext,
                                         intros,
                                         simp only [funext_simp] at *,
                                         solve_by_elim `[cc],
                                       end } }

instance Types_has_Coproducts : has_Coproducts (Type u) := 
{ coproduct := λ I φ, { coproduct     := Σ i : I, φ i,
                        inclusion     := λ i x, ⟨ i, x ⟩,
                        map           := λ Z f p, f p.1 p.2,
                        factorisation := begin
                                           -- `obviously'` says:
                                           intros,
                                           refl
                                         end,
                        uniqueness    := begin
                                           -- `obviously'` says:
                                           intros,
                                           apply funext,
                                           intros,
                                           automatic_induction,
                                           dsimp,
                                           dsimp at *,
                                           simp only [funext_simp] at *,
                                           solve_by_elim `[cc],
                                         end } }

-- Even though this can be automatically generated from `Types_has_Products`, this is a cleaner version.
instance Types_has_BinaryProducts : has_BinaryProducts (Type u) := 
{ binary_product := λ X Y, { product             := X × Y,
                             left_projection     := prod.fst,
                             right_projection    := prod.snd,
                             map                 := λ _ f g z, (f z, g z),
                             left_factorisation  := begin
                                                      -- `obviously'` says:
                                                      intros,
                                                      refl
                                                    end,
                             right_factorisation := begin
                                                      -- `obviously'` says:
                                                      intros,
                                                      refl
                                                    end,
                             uniqueness          := begin
                                                      -- `obviously'` says:
                                                      intros,
                                                      apply funext,
                                                      intros,
                                                      apply pairs_equal,
                                                      simp only [funext_simp] at *,
                                                      solve_by_elim `[cc],
                                                      simp only [funext_simp] at *,
                                                      solve_by_elim `[cc],
                                                    end } }

instance Types_has_BinaryCoproducts : has_BinaryCoproducts (Type u) := 
{ binary_coproduct := λ X Y, { coproduct           := X ⊕ Y,
                               left_inclusion      := sum.inl,
                               right_inclusion     := sum.inr,
                               map                 := λ _ f g z, sum.cases_on z f g,
                               left_factorisation  := begin
                                                        -- `obviously'` says:
                                                        intros,
                                                        refl
                                                      end,
                               right_factorisation := begin
                                                        -- `obviously'` says:
                                                        intros,
                                                        refl
                                                      end,
                               uniqueness          := λ Z f g lw rw, begin 
                               -- TODO what is happening here?
                                                                       apply funext,
                                                                       intros,
                                                                       simp only [funext_simp] at *,
                                                                       cases x;
                                                                       solve_by_elim `[cc],
                                                                     end } }

instance Types_has_Equalizers : has_Equalizers (Type u) := 
{ equalizer := λ α β f g, { equalizer     := {x : α // f x = g x},
                            inclusion     := λ x, x.val,
                            map           := λ γ k h g, ⟨ k g, begin
                                                                 -- `obviously'` says:
                                                                 simp only [funext_simp] at *,
                                                                 solve_by_elim `[cc],
                                                               end ⟩,
                            factorisation := begin
                                               -- `obviously'` says:
                                               intros,
                                               refl
                                             end,
                            witness       := begin
                                               -- `obviously'` says:
                                               apply funext,
                                               intros,
                                               automatic_induction,
                                               dsimp,
                                               solve_by_elim `[cc],
                                             end,
                            uniqueness    := begin
                                               -- `obviously'` says:
                                               intros,
                                               apply funext,
                                               intros,
                                               apply subtype.eq,
                                               dsimp at *,
                                               simp only [funext_simp] at *,
                                               solve_by_elim `[cc],
                                             end } }


@[applicable] lemma constant_on_quotient {α β : Type u} (f g : α → β) {Z : Type u} (k : β → Z) (x y : β) (h : eqv_gen (λ (x y : β), ∃ (a : α), f a = x ∧ g a = y) x y) (w : ∀ (a : α), k (f a) = k (g a)) : k x = k y :=
begin
  induction h,
  -- obviously' says:
  { cases h_a,
    cases h_a_h,
    induction h_a_h_right, induction h_a_h_left,
    solve_by_elim `[cc] },
  { refl },
  { solve_by_elim `[cc] },
  { solve_by_elim `[cc] },
end

instance Types_has_Coequalizers : has_Coequalizers (Type u) := 
{ coequalizer := λ α β f g, { coequalizer   := quotient (eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y)),
                              projection    := begin
                                                 -- `obviously'` says:
                                                 apply quotient.mk
                                               end,
                              map           := begin 
                                                 -- `obviously'` says:
                                                  ---
                                                  intros,
                                                  simp,
                                                  intros,
                                                  induction a,
                                                  simp only [funext_simp] at *,
                                                  solve_by_elim `[cc], -- FIXME surely this isn't a terminal goal
                                                  dsimp,
                                                  simp,
                                                  simp only [funext_simp] at *,
                                                  apply constant_on_quotient ; apply_assumption, -- FIXME                                                
                                                  ---
                                               end,                     
                              factorisation := begin
                                                 -- `obviously'` says:
                                                 intros,
                                                 refl
                                               end,
                              witness       := begin
                                                 -- `obviously'` says:
                                                 apply funext,
                                                 intros,
                                                 apply quotient.sound,
                                                 apply eqv_gen.rel,
                                                 fsplit,
                                                 solve_by_elim `[cc],
                                                 fsplit,
                                                 refl,
                                                 refl
                                               end,
                              uniqueness    := begin
                                                 -- `obviously'` says:
                                                  ---
                                                  intros,
                                                  apply funext,
                                                  intros,
                                                  induction x,
                                                  simp only [funext_simp] at *,
                                                  solve_by_elim `[cc],
                                                  refl
                                                  ---
                                               end } }
end categories.types