import Mathlib

/- Calculation for mod 71-/
example (p : ℕ) [Fact <| Nat.Prime p] (a : ZMod p) (h : a ≠ 0) :
    a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h

instance : Fact (Nat.Prime 71) where
  out := by decide

lemma pow_mod_order {p : ℕ} [Fact <| Nat.Prime p] {a : ZMod p} (ha : a ≠ 0) (n : ℕ) :
    a ^ n = a ^ (n % (p - 1)) := by
  have h : n = (p - 1) * (n / (p - 1)) + (n % (p - 1)) := (Nat.div_add_mod n (p - 1)).symm
  rw [h, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one ha]
  simp

example : 1234 ^ 123456 ≡ 10^17 [MOD 71] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow]
  exact calc (1234 : ZMod 71) ^ 123456
    _ = 27 ^ 123456 := by congr -- 1234 ≡ 27 mod 71
    _ = 3 ^(3*123456) := by rw[show (27 : ZMod 71) = 3 ^ 3 by norm_num, pow_mul]
    _ = 3 ^ 68 := by  --FLT
        have h : 3 * 123456 % 70 = 68 := by norm_num
        rw [← h, pow_mod_order]
        decide  -- 3 ≠ 0
    _ = 81 ^17 := by ring_nf
    _ = 10 ^17 := by congr


/- Calculation for tensor-/
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TensorProduct

-- noncomputable def huarongdao' {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
--     (A B C D : ℱ) :
--     (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D) ≅
--     (A ⊗ D) ⊗ (C ⊗ B) :=
--     calc (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D)
--     _ ≅ (A ⊗ B) ⊗ (C ⊗ D) := (Iso.refl _ ⊗ᵢ ρ_ _) ⊗ᵢ (λ_ _ )
--     _ ≅ (A ⊗ B) ⊗ (D ⊗ C) := (Iso.refl _ ) ⊗ᵢ β_ _ _
--     _ ≅ A ⊗ B ⊗ (D ⊗ C) := α_ _ _ _
--     _ ≅ A ⊗ ((D ⊗ C) ⊗ B) := (Iso.refl _ ) ⊗ᵢ β_ _ _
--     _ ≅ A ⊗ (D ⊗ (C ⊗ B)) := Iso.refl _ ⊗ᵢ α_ _ _ _
--     _ ≅ (A ⊗ D) ⊗ (C ⊗ B) := (α_ _ _ _).symm

noncomputable def huarongdao' {ℱ : Type*} [Category ℱ] [MonoidalCategory ℱ] [SymmetricCategory ℱ]
    (A B C D : ℱ) :
    (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D) ≅
    (A ⊗ D) ⊗ (C ⊗ B) :=  /-迎合下面例子,其实是 _ ≅ (𝟙_ℱ ⊗ A ⊗ D) ⊗ (𝟙_ℱ ⊗ C ⊗ B)-/
    calc (A ⊗ B ⊗ 𝟙_ℱ) ⊗ (𝟙_ℱ ⊗ C ⊗ D)
    _ ≅ (A ⊗ 𝟙_ℱ ⊗ B) ⊗ ((𝟙_ℱ ⊗ C) ⊗ D) := (Iso.refl _ ⊗ᵢβ_ _ _) ⊗ᵢ (α_ _ _ _).symm
    _ ≅ ((A ⊗ 𝟙_ℱ) ⊗ B) ⊗ (D ⊗ (𝟙_ℱ ⊗ C)) := (α_ _ _ _).symm ⊗ᵢ β_ _ _
    _ ≅ (((A ⊗ 𝟙_ℱ) ⊗ B )⊗ D) ⊗ (𝟙_ℱ ⊗ C) := (α_ _ _ _).symm
    _ ≅ ((A ⊗ 𝟙_ℱ) ⊗ (B ⊗ D)) ⊗ (𝟙_ℱ ⊗ C) := (α_ _ _ _) ⊗ᵢ Iso.refl _
    _ ≅ ((𝟙_ℱ ⊗ A) ⊗ (D ⊗ B)) ⊗ (𝟙_ℱ ⊗ C) := (β_ _ _ ⊗ᵢ β_ _ _) ⊗ᵢ Iso.refl _
    _ ≅ (((𝟙_ℱ ⊗ A) ⊗ D) ⊗ B) ⊗ (𝟙_ℱ ⊗ C) := (α_ _ _ _).symm ⊗ᵢ Iso.refl _
    _ ≅ ((𝟙_ℱ ⊗ A ⊗ D) ⊗ B) ⊗ (𝟙_ℱ ⊗ C) := (α_ _ _ _ ⊗ᵢ Iso.refl _) ⊗ᵢ Iso.refl _
    _ ≅ (𝟙_ℱ ⊗ A ⊗ D) ⊗ (B ⊗ (𝟙_ℱ ⊗ C)) := α_ _ _ _
    _ ≅ (𝟙_ℱ ⊗ A ⊗ D) ⊗ ((𝟙_ℱ ⊗ C) ⊗ B) := Iso.refl _ ⊗ᵢ β_ _ _
    _ ≅ (𝟙_ℱ ⊗ A ⊗ D) ⊗ (𝟙_ℱ ⊗ C ⊗ B) := Iso.refl _ ⊗ᵢ α_ _ _ _
    _ ≅ (A ⊗ D) ⊗ (C ⊗ B) := (λ_ _) ⊗ᵢ (λ_ _)

-- #check CommRingCat.monoidAlgebra
example (R : Type) [CommRing R] (r₁ r₂ : R)
    (A B C D : ModuleCat.{0} R) (a : A) (b : B) (c : C) (d : D) :
    (huarongdao' A B C D).hom ((a ⊗ₜ (b ⊗ₜ r₁)) ⊗ₜ (r₂ ⊗ₜ (c ⊗ₜ d))) =
    (r₁ • a ⊗ₜ d) ⊗ₜ (r₂ • c ⊗ₜ b) := rfl
