import Mathlib

#check Int.floor_eq_iff

namespace Int
namespace Rat

lemma exercise_1_1_1 (n : ℕ) (hn : n > 0) (α : ℝ) :
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
  · have := calc (⌊ α ⌋ : ℝ)
      _ = (n * q) / n := by
        rw [mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (by aesop)]
      _ = ⌊((n : ℤ) * q : ℝ)⌋ / n := by
        simp only [← cast_mul, Int.floor_intCast]
        simp only [cast_mul, cast_natCast]
      _ ≤ ⌊ n * q + n * r ⌋ / n := by
        gcongr
        simp [hn, hr.1]
    exact this
  · have := calc (⌊n * q + n * r⌋ / n : ℝ)
      _ < (⌊(n * q + n : ℝ)⌋ / n : ℝ) := by
        rw [← Ne.le_iff_lt (by
          by_contra!
          rw [← cast_natCast, ← cast_mul, floor_intCast_add,
            floor_intCast_add, div_eq_mul_inv, div_eq_mul_inv,
            mul_inv_eq_iff_eq_mul₀ (by aesop), mul_assoc, mul_comm (b := ((n : ℤ) : ℝ)),
            ← mul_assoc, mul_inv_cancel_right₀ (by aesop)] at this
          simp only [cast_natCast, cast_add, cast_mul, floor_natCast, add_right_inj] at this
          norm_cast at this
          rw [Int.floor_eq_iff] at this
          have h1 : r ≥ 1 := by aesop
          have h2 : ¬r ≥ 1 := by simpa using hr.2
          contradiction)]
        gcongr
        simp [hn, le_of_lt hr.2]
      _ = (⌊ α ⌋ + 1 : ℝ) := by
        simp only [floor_add_natCast, cast_add, cast_natCast]
        ring_nf
        rw [mul_inv_cancel₀ (by aesop)]
        congr
        rw [← cast_natCast, ← cast_mul, Int.floor_intCast]
        simp? [mul_comm]
        rw [mul_inv_cancel_right₀ (by aesop)]
    exact this

#check fract_lt_one
#check fract_nonneg
#check floor_le

lemma exercise_1_1_2 (n : ℕ) (hn : n > 0) (α : ℝ) :
  ∑ i ∈ Finset.range n, ⌊(α + i / n : ℝ)⌋ = ⌊ n * α ⌋ := by
  let k := ⌊ α ⌋
  let r := fract α
  have ha : α = k + r := by
    rw [show α = (⌊ α ⌋ : ℝ) + fract α by exact Eq.symm (add_sub_cancel (↑k) α)]
  have eq1 :  ∑ i ∈ Finset.range n, ⌊(α + i / n : ℝ)⌋ =
      ∑ i ∈ Finset.range n, (k + ⌊(r + i / n : ℝ)⌋) := by
    congr
    ext i
    rw [show α = k + r by exact Eq.symm (add_sub_cancel (↑k) α), add_assoc,
      floor_intCast_add]
  have eq2 : ∑ i ∈ Finset.range n, (k + ⌊(r + i / n : ℝ)⌋) =
      n * k + ∑ i ∈ Finset.range n, ⌊(r + i / n : ℝ)⌋ := by
    rw [Finset.sum_add_distrib]
    congr
    simp only [Finset.sum_const, Finset.card_range, Int.nsmul_eq_mul]
  have eq3 : ∑ i ∈ Finset.range n, ⌊(r + i / n : ℝ)⌋ =
      ∑ i ∈ {i : Finset.range n | r + (i : ℝ) / n ≥ 1}, ⌊(r + i / n : ℝ)⌋:= by
    apply Finset.sum_subset (by sorry) (by sorry)
    sorry
  have eq4 : ∑ i ∈ {i : Finset.range n | r + (i : ℝ) / n ≥ 1}, ⌊(r + i / n : ℝ)⌋ =
      ∑ i ∈ {i : Finset.range n | r + (i : ℝ) / n ≥ 1}, 1 := by
    refine Finset.sum_congr rfl ?_
    intro ⟨h1, h2⟩ hi
    simp? at h1 h2 hi ⊢
    have : r + h1 / n < 1 + 1 := by
      gcongr
      · exact fract_lt_one α
      · calc (h1 / n : ℝ)
          _ < (n / n) := by
            gcongr
          _ = 1 := by rw [div_eq_mul_inv, mul_inv_cancel₀ (by aesop)]
    rw [Int.floor_eq_iff]
    constructor
    · simpa using hi
    · simpa using this
  have eq5 : ∑ i ∈ {i : Finset.range n | r + (i : ℝ) / n ≥ 1}, 1 =
      ⌊ n * r ⌋ := by
    simp only [ge_iff_le, Finset.sum_const, Int.nsmul_eq_mul, mul_one]
    have : ⌊(n * r : ℝ)⌋ = (Finset.filter (fun i => i ≥ n - ⌊(n * r : ℝ)⌋) (Finset.range n)).card := by

      sorry

    sorry
  rw [eq1, eq2, eq3, eq4, eq5, ha, left_distrib]
  rw [show (n : ℝ) * ↑k + ↑n * r = ((n : ℤ) : ℝ) * ↑k + ↑n * r by rw [cast_natCast]]
  rw [← cast_mul, Int.floor_intCast_add]



end Rat
end Int
