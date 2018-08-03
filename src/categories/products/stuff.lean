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

meta def local_def_value (e : expr) : tactic expr := do
do (v,_) ← solve_aux `(true) (do
         lc ← local_context,
         let e := lc.reverse.head,
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

-- Sometimes `mk_congr_arg` fails, when the function is 'superficially dependent'.
-- This hack first dsimplifies the function before building the `congr_arg` expression.
-- Unfortunately it creates a dummy hypothesis that I can't work out how to avoid or dispose of cleanly.
meta def mk_congr_arg_using_dsimp (G W : expr) (u : list name) : tactic expr := 
do
  s ← simp_lemmas.mk_default,
  t ← infer_type G,
  t' ← s.dsimplify u t {fail_if_unchanged := ff},
  aux ← tactic.definev `_mk_congr_arg_aux t' G,
  ca ← to_expr ```(congr_arg _mk_congr_arg_aux %%W),
  ca_t ← infer_type ca,
  s.dsimplify [`_mk_congr_arg_aux] ca {fail_if_unchanged := ff}
  
lemma test2 (m n : ℕ) (w : m = n) : G n == G m :=
begin
  -- tactic.get_local `w >>= λ W, mk_congr_arg_using_dsimp `(G) W `F >>= tactic.trace,
  let h := by ((tactic.get_local `w) >>= λ W, mk_congr_arg_using_dsimp `(G) W [`F]) >>= exact,
  rw h,
end
