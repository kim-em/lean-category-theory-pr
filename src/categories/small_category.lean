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

-- PROJECT: tactics for deriving instances of small, e.g. `small pempty`!

class small_category (C : Type (u+1)) extends category C, small C.

def small.down {C : Type (u+1)} [small C] (X : C)             := (small.smallness C).to_fun  X
def small.up   {C : Type (u+1)} [small C] (X : small.model C) := (small.smallness C).inv_fun X

notation `𝟙ₛ` X := category.identity (small.up X)   -- type as \b1
notation X ` ⟶ₛ ` Y : 10 := category.Hom (small.up X) (small.up Y)    -- type as \h

end categories