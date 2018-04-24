-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..tactics
import data.fintype

universes u v

inductive Two : Type u
| _0 : Two
| _1 : Two

open Two

section
open tactic
@[tidy] meta def induction_Two : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.map (λ h, do t ← infer_type h, match t with | `(Two) := cases h >> skip | _ := failed end)),
   skip
end

local attribute [tidy] dsimp_all'

instance Two_decidable : decidable_eq Two := 
begin
  -- `obviously'` says:
  dsimp_all',
  intros,
  induction_Two,
  simp!,
  fapply decidable_true,
  simp!,
  fapply decidable_false,
  induction_Two,
  simp!,
  fapply decidable_false,
  simp!,
  fapply decidable_true
end

instance Two_fintype : fintype Two := 
{ elems       := [_0, _1].to_finset,
  complete    := begin
                   -- `obviously'` says:
                   intros,
                   dsimp,
                   simp!,
                   induction_Two,
                   simp!,
                   simp! 
                 end }
