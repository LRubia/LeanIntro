import Mathlib

#check Int.floor_eq_iff
#check Int.natCast_floor_eq_floor
#check NNRat.coe_floor
#check Rat.floor_intCast
#check Rat.floor_cast
#check Int.floor_intCast
#check Int.cast_natCast
namespace Int
namespace Rat

lemma floor_monotone {a b : ℝ} (h : a ≤ b) : floor a ≤ floor b := by sorry

lemma exercise_1_1 (n : ℕ) (hn : n > 0) (α : ℝ) :
    ⌊ (⌊ n * α ⌋ : ℝ) / (n : ℝ) ⌋ = ⌊ α ⌋ := by
  let q := ⌊ α ⌋
  let r := α - ⌊ α ⌋
  have hr : 0 ≤ r ∧ r < 1 := by
    constructor
    · calc 0
        _ ≤ α - q := sub_nonneg_of_le (Int.floor_le _)
        _ = r := by rfl
    · calc r
        _ = α - q := by rfl
        _ < 1 := by
          rw [sub_lt_iff_lt_add']
          exact Int.lt_floor_add_one _
  conv_lhs => rw [show α = q + r by exact Eq.symm (add_sub_cancel (↑q) α)]
  rw [left_distrib, Int.floor_eq_iff]
  constructor
  -- · have := calc (⌊ α ⌋ : ℝ)
  --     _ = (n * q) / n := by
  --       rw [mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (by aesop)]
  --     _ = ⌊ n * q ⌋ / n := by
  --       norm_cast
  --     _ ≤ ⌊ n * q + n * r ⌋ / n := by
  --       gcongr
  --       rw [show ⌊↑n * q⌋ = ⌊(n * q : ℝ)⌋ by
  --         change _ = ⌊((n : ℤ) : ℝ) * _⌋
  --         simp only [floor_int, id_eq, ← cast_mul, Int.floor_intCast]]
  --       apply Int.floor_mono
  --       simp [hn, hr.1]
  --   exact this

  · calc (⌊ α ⌋ : ℝ)
    _ = (n * q) / n := by
        rw [mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (by aesop)]
    _ = ⌊((n : ℤ) * q : ℝ)⌋ / n := by
      simp only [← cast_mul, Int.floor_intCast]
      simp?
    _ ≤ ⌊ n * q + n * r ⌋ / n := by
      gcongr
      simp [hn, hr.1]
  · sorry
