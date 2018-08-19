import category_theory.types
import ..instances
import tidy.its
import tactic.interactive

open category_theory.universal

namespace category_theory.types

universe u

local attribute [forward] congr_fun

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
                                        /- obviously says: -/ 
                                        intros Z f g witness, 
                                        ext, 
                                        have f_x_x_1 := f x x_1, 
                                        have witness_x_1 := witness x_1, 
                                        have congr_fun_witness_x_1_x := congr_fun witness_x_1 x, 
                                        dsimp at *, 
                                        solve_by_elim
                                       end } }

instance Types_has_Coproducts : has_Coproducts (Type u) := 
{ coproduct := λ I φ, 
  { coproduct     := Σ i : I, φ i,
    inclusion     := λ i x, ⟨ i, x ⟩,
    map           := λ Z f p, f p.1 p.2,
    factorisation := begin /- `obviously'` says: -/ intros, refl end,
    uniqueness    := begin
                        /- obviously says: -/ 
                        intros Z f g witness, 
                        ext, 
                        cases x, 
                        have witness_x_fst := witness x_fst, 
                        have congr_fun_witness_x_fst_x_snd := congr_fun witness_x_fst x_snd, 
                        dsimp at *, 
                        solve_by_elim
                      end } }

-- Even though this can be automatically generated from `Types_has_Products`, this is a cleaner version.
instance Types_has_BinaryProducts : has_BinaryProducts.{u+1 u} (Type u) := 
{ binary_product := λ X Y,
  { product := X × Y,
    left_projection     := prod.fst,
    right_projection    := prod.snd,
    map                 := λ _ f g z, (f z, g z),
    left_factorisation  := begin /- `obviously'` says: -/ intros, refl end,
    right_factorisation := begin /- `obviously'` says: -/ intros, refl end,
    uniqueness          := begin
                            /- obviously says: -/ 
                            intros Z f g left_witness right_witness, 
                            ext, 
                            have congr_fun_left_witness_x := congr_fun left_witness x, 
                            have congr_fun_right_witness_x := congr_fun right_witness x, -- superfluous!
                            dsimp at *, 
                            solve_by_elim, 
                            have congr_fun_left_witness_x := congr_fun left_witness x, 
                            have congr_fun_right_witness_x := congr_fun right_witness x, -- superfluous!
                            dsimp at *, 
                            solve_by_elim
                          end } }

instance Types_has_BinaryCoproducts : has_BinaryCoproducts.{u+1 u} (Type u) := 
{ binary_coproduct := λ X Y, 
  { coproduct           := X ⊕ Y,
    left_inclusion      := sum.inl,
    right_inclusion     := sum.inr,
    map                 := λ _ f g z, sum.cases_on z f g,
    left_factorisation  := begin /- `obviously'` says: -/ intros, refl end,
    right_factorisation := begin /- `obviously'` says: -/ intros, refl end,
    uniqueness          := begin 
                              /- obviously says: -/ 
                              intros Z f g left_witness right_witness,
                              ext, 
                              cases x, 
                              have congr_fun_lw_x := congr_fun left_witness x, 
                              dsimp at *, 
                              solve_by_elim, 
                              have congr_fun_rw_x := congr_fun right_witness x, 
                              dsimp at *, 
                              solve_by_elim
                            end } }

instance Types_has_Equalizers : has_Equalizers.{u+1 u} (Type u) := 
{ equalizer := λ α β f g, { equalizer     := {x : α // f x = g x},
                            inclusion     := λ x, x.val,
                            map           := λ γ k h g, ⟨ k g, begin
                                                                 /- obviously says: -/ 
                                                                 have congr_fun_h_g := congr_fun h g, 
                                                                 dsimp at *, 
                                                                 solve_by_elim
                                                               end ⟩,
                            factorisation := begin /- `obviously'` says: -/ intros, refl end,
                            witness       := begin
                                               -- `obviously'` says:
                                               ext,
                                               automatic_induction,
                                               dsimp,
                                               solve_by_elim,
                                             end,
                            uniqueness    := begin
                                               /- obviously says: -/ 
                                               intros Z a b witness, 
                                               ext, 
                                               have congr_fun_witness_x := congr_fun witness x, 
                                               dsimp at *, 
                                               solve_by_elim
                                             end } }


@[back'] lemma constant_on_quotient {α β : Type u} (f g : α → β) {Z : Type u} (k : β → Z) (x y : β) (h : eqv_gen (λ (x y : β), ∃ (a : α), f a = x ∧ g a = y) x y) (w : k ∘ f = k ∘ g) : k x = k y :=
begin
  induction h,
  /- obviously says: -/ 
  cases h_a, 
  have congr_fun_w_h_a_w := congr_fun w h_a_w, 
  cases h_a_h, 
  induction h_a_h_right, 
  induction h_a_h_left, 
  solve_by_elim, 
  refl, 
  solve_by_elim, 
  erw [h_ih_a, h_ih_a_1]
end

instance Types_has_Coequalizers : has_Coequalizers.{u+1 u} (Type u) := 
{ coequalizer := λ α β f g, by 
    letI s := eqv_gen.setoid (λ x y, ∃ a : α, f a = x ∧ g a = y);
    exact { coequalizer   := quotient s,
            projection    := begin /- `obviously'` says: -/ apply quotient.mk end,
            map           := λ Z k w, quotient.lift k begin
                                                        /- obviously says: -/ 
                                                        intros a b a_1, 
                                                        apply category_theory.types.constant_on_quotient ; solve_by_elim
                                                      end,
            factorisation := begin /- `obviously'` says: -/ intros, refl end,
            witness       := begin
                                -- `obviously'` says:
                                ext, 
                                apply quotient.sound, 
                                dsimp at *,
                                apply eqv_gen.rel, 
                                fsplit, 
                                solve_by_elim, 
                                simp at *                                                 
                              end,
            uniqueness    := begin
                                /- obviously says: -/ 
                                intros Z a b witness, 
                                ext, 
                                induction x, 
                                have congr_fun_witness_x := congr_fun witness x, 
                                dsimp at *, 
                                solve_by_elim, 
                                refl                                                
                              end } }
end category_theory.types