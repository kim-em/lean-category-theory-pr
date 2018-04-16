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
                                         fapply funext,
                                         intros,
                                         fapply funext,
                                         intros,
                                         simp! at *,
                                         solve_by_elim
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
                                           fapply funext,
                                           intros,
                                           automatic_induction,
                                           dsimp,
                                           dsimp at *,
                                           simp! at *,
                                           solve_by_elim
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
                                                      fapply funext,
                                                      intros,
                                                      fapply pairs_equal,
                                                      simp! at *,
                                                      solve_by_elim,
                                                      simp! at *,
                                                      solve_by_elim
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
                                                                       tidy,
                                                                       cases x; 
                                                                       -- `obviously'` says:
                                                                       solve_by_elim
                                                                     end } }

instance Types_has_Equalizers : has_Equalizers (Type u) := 
{ equalizer := λ α β f g, { equalizer     := {x : α // f x = g x},
                            inclusion     := λ x, x.val,
                            map           := λ γ k h g, ⟨ k g, begin
                                                                 -- `obviously'` says:
                                                                 simp! at *,
                                                                 solve_by_elim
                                                               end ⟩,
                            factorisation := begin
                                               -- `obviously'` says:
                                               intros,
                                               refl
                                             end,
                            witness       := begin
                                               -- `obviously'` says:
                                               fapply funext,
                                               intros,
                                               automatic_induction,
                                               dsimp,
                                               solve_by_elim
                                             end,
                            uniqueness    := begin
                                               -- `obviously'` says:
                                               intros,
                                               fapply funext,
                                               intros,
                                               fapply subtype.eq,
                                               dsimp at *,
                                               simp! at *,
                                               solve_by_elim
                                             end } }

open tactic
@[tidy] meta def quotient_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(quotient _) := induction h >> skip | `(eqv_gen _ _ _) := induction h >> skip | _ := failed end))

instance Types_has_Coequalizers : has_Coequalizers (Type u) := 
{ coequalizer := λ α β f g, { coequalizer   := quotient (eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y)),
                              projection    := begin
                                                 -- `obviously'` says:
                                                 fapply quotient.mk
                                               end,
                              map           := by obviously', -- TODO breaks when removed                           
                              factorisation := begin
                                                 -- `obviously'` says:
                                                 intros,
                                                 refl
                                               end,
                              witness       := by obviously', -- TODO breaks when removed
                              uniqueness    := by obviously' } } -- TODO breaks when removed
end categories.types