import ..universal.limits

open category_theory
open category_theory.universal

namespace category_theory.universal

universes u v

variables {C : Type u} [𝒞 : category.{u v} C] {Y Y₁ Y₂ Z : C}
include 𝒞

@[reducible] def binary_product_comparison (t : span Y Z) (X' : C) : (X' ⟶ t.X) → (X' ⟶ Y) × (X' ⟶ Z) :=
λ φ, (φ ≫ t.π₁, φ ≫ t.π₂)

def is_binary_product.comparison {t : span Y Z} (h : is_binary_product t) (X' : C) : is_equiv (binary_product_comparison t X') :=
{ inv := λ p, h.lift ⟨ ⟨ X' ⟩, p.1, p.2 ⟩,
  hom_inv_id := begin 
                 tidy, 
                 symmetry, 
                 have := h.uniq {to_shape := {X := X'}, π₁ := x ≫ t.π₁, π₂ := x ≫ t.π₂} x,
                 apply this, -- TODO why can't we just `apply h.uniq`?
                 tidy,
                end }

def is_binary_product.of_comparison {t : span Y Z} (w : Π X' : C, is_equiv (binary_product_comparison t X')) : is_binary_product t :=
{ lift := λ s, inv' (w s.X) (s.π₁, s.π₂),
  fac₁ := λ s, begin
            have p := inv_hom_id' (w s.X), 
            have q := congr_fun p (s.π₁, s.π₂),
            tidy,
          end,
  fac₂ := λ s, begin
            have p := inv_hom_id' (w s.X), 
            have q := congr_fun p (s.π₁, s.π₂),
            tidy,
          end,
  uniq := λ s m w₁ w₂, begin
            have p := hom_inv_id' (w s.X), 
            have q := congr_fun p m,
            obviously,
          end } 

@[reducible] def equalizer_comparison {f g : Y ⟶ Z} (t : fork f g) (X' : C) : (X' ⟶ t.X) → { h : X' ⟶ Y // h ≫ f = h ≫ g } :=
λ φ, ⟨ φ ≫ t.ι, by obviously ⟩ 

def is_equalizer.comparison {f g : Y ⟶ Z} {t : fork f g} (h : is_equalizer t) (X' : C) : is_equiv (equalizer_comparison t X') :=
{ inv := λ p, h.lift ⟨ ⟨ X' ⟩, p.1, p.2 ⟩,
  hom_inv_id := begin 
                 tidy, 
                 symmetry, 
                 apply h.uniq {to_shape := {X := X'}, ι := x ≫ t.ι} x,
                 tidy,
                end }

def is_equalizer.of_comparison {f g : Y ⟶ Z} {t : fork f g} (w : Π X' : C, is_equiv (equalizer_comparison t X')) : is_equalizer t :=
{ lift := λ s, inv' (w s.X) ⟨ s.ι, s.w ⟩,
  fac  := λ s, begin
            have p := inv_hom_id' (w s.X), 
            have q := congr_fun p ⟨ s.ι, s.w ⟩,
            tidy,
          end,
  uniq := λ s m w', begin
            have p := hom_inv_id' (w s.X), 
            have q := congr_fun p m,
            tidy,
            unfold equalizer_comparison at q,
            rw ← q,
            congr,
            exact w',
          end } 

@[reducible] def pullback_comparison {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} (t : square r₁ r₂) (X' : C) : (X' ⟶ t.X) → { c : (X' ⟶ Y₁) × (X' ⟶ Y₂) // c.1 ≫ r₁ = c.2 ≫ r₂ } :=
λ φ, ⟨ (φ ≫ t.π₁, φ ≫ t.π₂), by obviously ⟩ 

def is_pullback.comparison {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂} (h : is_pullback t) (X' : C) : is_equiv (pullback_comparison t X') :=
{ inv := λ p, h.lift ⟨ ⟨ X' ⟩, p.val.1, p.val.2 ⟩,
  hom_inv_id := begin 
                 tidy, 
                 symmetry, 
                 apply h.uniq {to_shape := {X := X'}, π₁ := x ≫ t.π₁, π₂ := x ≫ t.π₂} x,
                 tidy,
                end }

def is_pullback.of_comparison {r₁ : Y₁ ⟶ Z} {r₂ : Y₂ ⟶ Z} {t : square r₁ r₂} (w : Π X' : C, is_equiv (pullback_comparison t X')) : is_pullback t :=
{ lift := λ s, inv' (w s.X) ⟨ (s.π₁, s.π₂), s.w ⟩,
  fac₁ := λ s, begin
            have p := inv_hom_id' (w s.X), 
            have q := congr_fun p ⟨ (s.π₁, s.π₂), s.w ⟩,
            tidy,
          end,
  fac₂ := λ s, begin
            have p := inv_hom_id' (w s.X), 
            have q := congr_fun p ⟨ (s.π₁, s.π₂), s.w ⟩,
            tidy,
          end,
  uniq := λ s m w₁ w₂, begin
            have p := hom_inv_id' (w s.X), 
            have q := congr_fun p m,
            tidy,
            unfold pullback_comparison at q,
            rw ← q,
            congr,
            tidy,
          end } 

variables {J : Type v} [𝒥 : small_category J]
include 𝒥

@[reducible] def limit_comparison {F : J ↝ C} (t : cone F) (X' : C) : (X' ⟶ t.X) → { c : Π j : J, (X' ⟶ F j) // ∀ {j j' : J} (f : j ⟶ j'), c j ≫ F.map f = c j' } :=
λ φ, ⟨ λ j, φ ≫ t.π j, by obviously ⟩ 

def is_limit.comparison {F : J ↝ C} {t : cone F} (h : is_limit t) (X' : C) : is_equiv (limit_comparison t X') :=
{ inv := λ p, h.lift ⟨ ⟨ X' ⟩, p.val, p.property ⟩,
  hom_inv_id := begin 
                 tidy, 
                 symmetry, 
                 apply h.uniq {to_shape := {X := X'}, π := λ j, x ≫ t.π j, w := by obviously } x,
                 tidy,
                end }

def is_limit.of_comparison {F : J ↝ C} {t : cone F} (w : Π X' : C, is_equiv (limit_comparison t X')) : is_limit t :=
{ lift := λ s, inv' (w s.X) ⟨ s.π, s.w ⟩,
  fac :=  λ s, begin
              have p := inv_hom_id' (w s.X), 
              have q := congr_fun p ⟨ s.π, s.w ⟩,
              tidy,
            end,
  uniq := λ s m w', begin
            have p := hom_inv_id' (w s.X), 
            have q := congr_fun p m,
            tidy,
            unfold limit_comparison at q,
            rw ← q,
            congr,
            tidy,
          end } 


end category_theory.universal