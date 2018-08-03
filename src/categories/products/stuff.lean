def F : Π n : ℕ, Type := λ n, ℕ 
def G : Π n : ℕ, F n := λ n, begin dunfold F, exact 0 end

lemma test (m n : ℕ) (w : m = n) : G n == G m :=
begin
  -- This doesn't work, because `G` looks like a dependent function
  success_if_fail { 
    have h := congr_arg G w
  },
  -- In fact it isn't really, and we can discover this with `dsimp`.
  let g := G,
  dsimp [F] at g,
  -- Now we can use congr_arg.
  let h := congr_arg g w,
  dsimp [g] at h,
  rw h,
end

-- Now I want to do this via `expr` munging:

open tactic

meta def mk_congr_arg_using_dsimp (G W : expr) (F : name) : tactic unit := 
-- I have no idea how to achieve this: this doesn't work, but is my best guess.
do
  s ← simp_lemmas.mk_default,
  t ← infer_type G,
  t' ← s.dsimplify [F] t {fail_if_unchanged := ff},

  tactic.definev `g t' G,

  ca ← to_expr ```(congr_arg (g : %%t') %%W),
  cat ← infer_type ca,
  he ← tactic.definev `h cat ca,
  `[dsimp [g] at h]
  
lemma test2 (m n : ℕ) (w : m = n) : G n == G m :=
begin
  -- tactic.get_local `w >>= λ W, mk_congr_arg_using_dsimp `(G) W `F >>= tactic.trace,
  ((tactic.get_local `w) >>= λ W, mk_congr_arg_using_dsimp `(G) W `F),
  rw h,
end
