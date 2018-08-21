import .limits

universes u v

open category_theory

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def terminals_iso (A B : terminal_object.{u v} C) : A.X ≅ B.X :=
{ hom := B.h.lift A.X,
  inv := A.h.lift B.X }

def binary_products_iso {Y Z : C} (A B : binary_product.{u v} Y Z) : A.X ≅ B.X :=
{ hom := B.h.lift A.t,
  inv := A.h.lift B.t }

end category_theory.universal
