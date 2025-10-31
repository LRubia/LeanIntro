import Mathlib

/-不存在域 F 使得 F 的加法群结构和 F 的乘法群结构同构。-/
variable (F : Type) [Field F]

example : IsEmpty (Units F ≃* Multiplicative F) := by
  by_contra r
  simp only [not_isEmpty_iff] at r
  obtain ⟨g⟩ := r
  have h1 : g 1 = Multiplicative.ofAdd 0 := by simp
  let a := (g (-1)).toAdd
  have eq1 := calc 2 • a
    _ = 2 • (g (-1)).toAdd := rfl
    _ = (g (-1)).toAdd + (g (-1)).toAdd := by rw [two_nsmul]
    _ = (g (-1) * g (-1)).toAdd := by simp
    _ = (g ((-1) * (-1))).toAdd := by rw [g.map_mul]
    _ = (g 1).toAdd := by simp
    _ = Multiplicative.toAdd 1 := by simp
    _ = 0 := by simp
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero] at eq1
  /-char F = 2-/
  have char2 : CharP F 2 := by
    refine CharTwo.of_one_ne_zero_of_two_eq_zero (one_ne_zero) ?_
    · cases eq1 with
      | inl h => exact h
      | inr h =>
        simp [a] at h
        apply congrArg Units.val at h
        apply congrArg (fun (x:F) => x+1) at h
        simp_all  [one_add_one_eq_two]
   /-For g b =1, b = 1 -/
  obtain ⟨b, hb⟩ := g.surjective <| Multiplicative.ofAdd 1
  have eq2 := calc g (b ^ 2)
    _ = g b * g b := by simp [pow_two]
    _ = (g b).toAdd + (g b).toAdd := rfl
    _ = 1 + 1 := by rw[hb, toAdd_ofAdd]
    _ = 2 := by ring
    _ = 0 := by simp [CharTwo.two_eq_zero]
    _ = g 1 :=by rw[h1]; rfl
  have bsq : (b : F) ^ 2 = 1 := congrArg (fun x : Fˣ => (x : F)) <| g.injective eq2
  have beq1 : b = 1 := by  /- -/
    have := ExpChar.pow_prime_pow_mul_eq_one_iff 2 1 1 (b: F)
    simp_all only [pow_one, mul_one, Units.val_eq_one]
    tauto
  /-contradiction-/
  have gb_0 : g b = Multiplicative.ofAdd 0 :=by rw[beq1, h1]
  rw [hb] at gb_0
  apply_fun Multiplicative.toAdd at gb_0
  rw [toAdd_ofAdd, toAdd_ofAdd] at gb_0
  have : (1 : F) ≠ 0 := one_ne_zero
  contradiction

-- #check FiniteField.even_card_of_char_two
-- #check Function.Surjective
-- #check Units
