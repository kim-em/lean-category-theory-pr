import ..universal

open category_theory
open category_theory.universal

namespace category_theory.universal

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def is_binary_product_explicit_to_singleton {Y Z : C} {t : span Y Z} (P : explicit.is_binary_product.{u v} t) : singleton.is_binary_product.{u v} t :=
{ lift := P.lift,
  univ := sorry, }

def binary_product_explicit_to_singleton {Y Z : C} (P : explicit.binary_product.{u v} Y Z) : singleton.binary_product.{u v} Y Z :=
{ P with h := is_binary_product_explicit_to_singleton P.h }


end category_theory.universal