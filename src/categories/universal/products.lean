-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import .limits

open category_theory

universes u v

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C] [has_binary_products.{u v} C]
include 𝒞

def from_components {P Q R : C} (f : P ⟶ Q) (g : P ⟶ R) : P ⟶ (binary_product' Q R).X

def binary_product.associativity (P Q R : C) : (binary_product' (binary_product' P Q).X R).X ≅ (binary_product' P (binary_product' Q R).X).X :=
sorry

end category_theory.universal