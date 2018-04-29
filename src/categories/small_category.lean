-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .category
import data.fintype

namespace categories

universe u

class small (C : Type (u+1)) :=
(model : Type u)
(smallness : equiv C model)

instance (α : Type u) : small (ulift.{u+1 u} α) := 
{ model := α, 
  smallness := { to_fun := ulift.down,
                 inv_fun := ulift.up,
                 left_inv := sorry,
                 right_inv := sorry } }

-- PROJECT: seems hard without choice
-- instance (α : Type (u+1)) [fintype α] : small α := 


class small_category (C : Type (u+1)) extends category C, small C.

-- structure small (α : Type u) : Type (u + 1) :=
-- up :: (down : α)

-- namespace small
-- /- Bijection between α and ulift.{v} α -/
-- @[simp] lemma up_down {α : Type u} : ∀ (b : small.{u} α), up (down b) = b
-- | (up a) := rfl

-- @[simp] lemma down_up {α : Type u} (a : α) : down (up.{u} a) = a := rfl
-- end small

-- notation a `⟶ₛ` b := category.Hom (small.up a) (small.up b)


end categories