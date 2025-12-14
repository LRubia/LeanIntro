import Mathlib

open Real
open Filter Topology
#check negMulLog
example (x : ℝ) (hx : 0 < x) : deriv (fun x : ℝ => x ^ x) x = x ^ x + x ^ x * log x := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun x : ℝ => exp (x * log x))]
  swap
  · apply eventually_of_mem (U := Set.Ioo (x /2) (x * 2))
    · simp only [mem_nhds_iff]
      refine ⟨Set.Ioo (x / 2) (x * 2), ?_, ?_, ?_⟩
      · rfl
      · exact isOpen_Ioo
      · simp only [Set.mem_Ioo, half_lt_self_iff]
        refine ⟨hx, ?_⟩
        linarith
    · intro y hy1
      simp only [Set.mem_Ioo] at hy1
      simp only
      rw [← exp_log (x := y ^ y)]
      · simp only [exp_eq_exp]
        rw [log_rpow]
        linarith
      · have hy : 0 < y := by
          linarith
        apply rpow_pos_of_pos hy
  change deriv (rexp ∘ fun x => x * log x) x = _
  rw [deriv_comp]
  swap
  · exact differentiableAt_exp
  swap
  · apply differentiableAt_fun_neg_iff.1
    rw [← negMulLog_eq_neg]
    apply differentiableAt_negMulLog (ne_of_gt hx)
  rw [Real.deriv_exp]
  change _ * deriv (id * log) x = _
  rw [deriv_mul]
  swap
  · exact differentiableAt_fun_id
  swap
  · have hx2 : x ≠ 0 := by linarith
    exact differentiableAt_log hx2
  rw [deriv_id, deriv_log, ← log_rpow]
  simp only [one_mul, id_eq]
  ring_nf
  rw [exp_log (x := x ^ x)]
  · rw [add_comm]
    simp only [add_left_inj]

    sorry
  · simp only [rpow_pos_of_pos hx]
  · exact hx
