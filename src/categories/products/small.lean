-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import ..products

open categories
open categories.functor
open categories.natural_transformation
open categories.functor_categories

namespace categories.products

universes u₁ u₂ u₃ u₄

instance prod_small (C : Type (u₁+1)) (D : Type (u₂+1)) [small C] [small D] : small (C × D) := 
{ model := small.model C × small.model D,
  smallness := sorry }

variable {C : Type (u₁+1)}
variable [small_category C]
variable {D : Type (u₂+1)}
variable [small_category D]

instance small_ProductCategory : small_category (C × D) := 
{ .. products.ProductCategory C D, .. products.prod_small C D }

end categories.products