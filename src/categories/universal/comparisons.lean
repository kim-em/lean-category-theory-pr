import ..universal

open category_theory
open category_theory.universal
namespace category_theory.universal.singleton

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞


def binary_product_subsingleton (Y Z : C) (P Q : binary_product.{u v} Y Z) : P.X ≅ Q.X := 
{ hom := Q.h.lift P.t,
  inv := P.h.lift Q.t,
}

end category_theory.universal.singleton