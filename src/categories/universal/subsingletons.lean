import ..universal

universes u v

open category_theory
open category_theory.universal

namespace category_theory.universal.singleton

local attribute [back] subsingleton.intro

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

instance is_binary_product_subsingleton  {Y Z : C} (t : span Y Z) : subsingleton (is_binary_product t) :=
begin
  obviously,
  -- TODO some slightly more aggressive forwards reasoning could do this
  have ba := (b.univ x (a.lift x)),
  have aa := (a.univ x (a.lift x)),
  dsimp at *,
  simp at *,
  cc,
end

def binary_product_subsingleton {Y Z : C} (P Q : binary_product.{u v} Y Z) : P.X ≅ Q.X := 
{ hom := Q.h.lift P.t,
  inv := P.h.lift Q.t,
  hom_inv_id := sorry,
  inv_hom_id := sorry }

instance is_equalizer_subsingleton {C : Type u} [𝒞 : category.{u v} C] {Y Z : C} {f g : Y ⟶ Z} (t : fork f g) : subsingleton (is_equalizer t) :=
begin
  obviously,
  -- TODO some slightly more aggressive forwards reasoning could do this
  have ba := (b.univ x (a.lift x)),
  have aa := (a.univ x (a.lift x)),
  dsimp at *,
  simp at *,
  cc,
end

instance is_pullback_subsingleton {C : Type u} [𝒞 : category.{u v} C] {P Q R : C}  {p : P ⟶ R} {q : Q ⟶ R} (t : square p q) : subsingleton (is_pullback t) :=
begin
  obviously,
  -- TODO some slightly more aggressive forwards reasoning could do thiss
  have ba := (b.univ x (a.lift x)),
  have aa := (a.univ x (a.lift x)),
  dsimp at *,
  simp at *,
  cc,
end

end category_theory.universal.singleton
