import Mathlib

open Filter Topology Finset

-- #check Filter
-- #check ne_comm
-- #check nhdsWithin
-- #check 𝓝[≠] 0
-- #check eventually_nhdsWithin_iff
-- #check Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero
-- #check Filter.tendsto_pow_atTop
-- #check Real.le_sqrt_of_sq_le
-- #check abs_lt
-- #check nhdsLT_le_nhdsNE
-- #check Tendsto.inf
-- #check Tendsto.mono_left
-- #check tendsto_nhds_unique'
-- #check Set.Ioi
-- #check IsOpen.mem_nhds
-- #check mem_nhds_iff
-- #check Finset.sum_range_tsub
-- #check Nat.geomSum_eq
-- #check summable_geometric_iff_norm_lt_one
-- #check deriv
-- #check EventuallyEq
-- #check Filter.EventuallyEq.deriv_eq
-- #check deriv_exp
-- #check geom_sum_of_lt_one

-- theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
--   | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl --归纳？

/- exercise for serieslimit -/
example : Tendsto (fun n : ℕ => n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun n ↦ ⟨n, by simp⟩

example : ¬ Tendsto (fun n : ℕ => ((-1)^n * n : ℤ)) atTop atTop := by
  by_contra h
  rw [tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h 0
  have hmk (BigN : ℕ) (hBigN : N < BigN): 0 ≤ (-1) ^ BigN := by
    have h := mul_le_mul_iff_left₀ (b := 0) (c := (-1 : ℤ)^ BigN)
      (show (0 : ℤ) < BigN by exact_mod_cast Nat.zero_lt_of_lt hBigN)
    have hh := hN BigN (le_of_lt hBigN)
    simp at *
    exact h.1 hh
  have h1 := lt_of_le_of_ne (hmk (N + 1) (by omega)) (
    show 0 ≠ (-1) ^ (N + 1) from ne_comm.1 Int.neg_one_pow_ne_zero)
  have h2 := lt_of_le_of_ne (hmk (N + 2) (by omega)) (
    show 0 ≠ (-1) ^ (N + 2) from ne_comm.1 Int.neg_one_pow_ne_zero)
  rw [pow_succ] at h2
  linarith

example : ¬ Tendsto (fun n : ℕ => ((-1)^n * n : ℤ)) atTop atBot := by
  by_contra h
  rw [tendsto_atTop_atBot] at h
  obtain ⟨N, hN⟩ := h 0
  have hmk (BigN : ℕ) (hBigN : N < BigN):  (-1) ^ BigN ≤ 0:= by
    have h := mul_le_mul_iff_left₀ (b := (-1 : ℤ)^ BigN) (c := 0)
      (show (0 : ℤ) < BigN by exact_mod_cast Nat.zero_lt_of_lt hBigN)
    have hh := hN BigN (le_of_lt hBigN)
    simp at *
    exact h.1 hh
  have h1 := lt_of_le_of_ne (hmk (N + 1) (by omega)) (
    show (-1) ^ (N + 1) ≠ 0 from Int.neg_one_pow_ne_zero)
  have h2 := lt_of_le_of_ne (hmk (N + 2) (by omega)) (
    show (-1) ^ (N + 2) ≠ 0 from Int.neg_one_pow_ne_zero)
  rw [pow_succ] at h2
  linarith

/- exercise for function limit -/
example : Tendsto (fun x : ℝ => 1 / x) (𝓝[<] 0) atBot := by
  rintro s hs
  simp only [one_div, Filter.map_inv, inv_nhdsLT_zero, hs]

example : Tendsto (fun x : ℝ => 1 / x ^ 2) (𝓝[≠] 0) atTop := by
  rw [(show (fun x : ℝ ↦ 1/ x ^ 2) = (fun x : ℝ ↦ x⁻¹) ∘ (fun x : ℝ ↦ x ^ 2) by aesop)]
  refine Tendsto.comp (y := 𝓝[>] 0) tendsto_inv_nhdsGT_zero ?_
  apply Tendsto.inf
  · nth_rewrite 2 [(show (0 : ℝ) = 0 ^ 2 by simp)]
    exact ((continuous_pow (M := ℝ) 2).tendsto 0)
  · intro s hs x (hx : x ≠ 0)
    rw [Set.mem_preimage]
    exact hs (pow_two_pos_of_ne_zero hx)

example : ¬ ∀ (f : ℝ → ℝ), (∃ a : ℝ, Tendsto f (𝓝[>] 0) (𝓝 a) ∧ Tendsto f (𝓝[<] 0) (𝓝 a)) →
  ∃ b : ℝ, Tendsto f (𝓝 0) (𝓝 b) := by
  by_contra h
  let f := fun x : ℝ => if x = 0 then (1 : ℝ) else 0
  have hfl : Tendsto f (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_congr
    (f := fun x : ℝ => 0) (by aesop) (tendsto_const_nhds_iff.2 (by aesop))
  have hfr : Tendsto f (𝓝[<] 0) (𝓝 0) := tendsto_nhdsWithin_congr
    (f := fun x : ℝ => 0) (by aesop) (tendsto_const_nhds_iff.2 (by aesop))
  obtain ⟨b, h⟩ := h f ⟨0, ⟨hfl ,hfr⟩⟩
  rw [← show 0 = b from tendsto_nhds_unique hfl (Tendsto.mono_left h nhdsWithin_le_nhds),
    tendsto_def] at h
  let s := Set.Ioo (-0.5 : ℝ) 0.5
  specialize h s (IsOpen.mem_nhds isOpen_Ioo (by simp [s]; norm_num))
  have : 0 ∉ Set.preimage f s := by
    simp [Set.mem_preimage, f, s]; norm_num
  have : 0 ∈ Set.preimage f s := mem_of_mem_nhds h
  contradiction

/- series summation -/
lemma series_summable : Summable (fun n : ℕ => 1 / ((n + 1) * (n + 2) : ℝ)) := by
  fapply Summable.of_nonneg_of_le
  · exact  fun n => 1 / (n + 1 : ℝ)^2
  · intro n; positivity
  · intro n;
    norm_num
    rw [pow_two, mul_inv, mul_le_mul_iff_left₀, inv_le_inv₀]
    · norm_num
    · positivity -- why 4 goals
    · positivity
    · positivity
  · simpa using Real.summable_one_div_nat_add_rpow 1 2

example : ∑' n : ℕ, 1 / ((n + 1) * (n + 2) : ℝ) = 1 := by
  suffices : Tendsto (fun n => ∑ i ∈ range n, 1 / ((i + 1) * (i + 2): ℝ)) atTop (𝓝 1)
  · exact tendsto_nhds_unique series_summable.tendsto_sum_tsum_nat this
  have := calc fun n => ∑ i ∈ range n, 1 / ((i + 1) * (i + 2): ℝ)
    _ = fun n => ∑ i ∈ range n, (1 / (i + 1) - 1 /(i + 2) : ℝ) :=
      funext fun n => sum_congr rfl (fun i hi => by field_simp; norm_num)
    _ = fun n => ∑ i ∈ range n, (- 1 /(↑i + 1 + 1 : ℝ) - (- 1 / (i + 1))) :=
      funext fun n => sum_congr rfl (fun i hi => by grind)
    _ = fun n : ℕ => (- 1 / ( n + 1)) -  (- 1 / (0 + 1) : ℝ) :=
      funext fun n => by -- by ext n ??
      have : Monotone fun i : ℕ  ↦ -1 / ((i : ℝ) + 1) :=
        monotone_nat_of_le_succ (fun n =>by
        rw [neg_div, neg_div, neg_le_neg_iff, one_div_le_one_div]
        norm_num; positivity; positivity)
      exact_mod_cast sum_range_tsub (M := ℝ) (f := fun i => - 1 / (i + 1)) this n
    _ = fun n : ℕ => 1 - 1 / (n + 1 : ℝ) := by grind
  rw [tendsto_congr (congr_fun this)]
  nth_rewrite 4 [← sub_zero (1 : ℝ)]
  exact Tendsto.sub (tendsto_const_nhds_iff.2 (by norm_num))
   tendsto_one_div_add_atTop_nhds_zero_nat

/- 几何级数，我们只考虑|q| < 1的计算-/
lemma geom_sum_eq' {q : Real} (h : q ≠ 1) (n : ℕ) : --自己算一下
  ∑ i ∈ range n, q ^ i = (q ^ n - 1) / (q - 1) :=
  haveI : q - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  calc _ = (q - 1) * (∑ i ∈ range n, q ^ i) / (q - 1) := by rwa [mul_div_cancel_left₀]
    _ = (∑ i ∈ range n, (q ^ (i + 1) - q ^ i)) / (q - 1) := by
        rw [mul_sum, sum_congr rfl (fun i hi => by rw[sub_mul, ← pow_succ', one_mul])]
    _ = (q ^ n - q ^ 0) / (q - 1) := by rw [sum_range_sub]
    _ = (q ^ n - 1) / (q - 1) := by rw[pow_zero]

lemma tendsto_of_geomSum (q : Real) (h : |q| < 1) :
  Tendsto (fun n : ℕ =>  ∑ i ∈ range n, q ^ i) atTop (𝓝 (1 / (1 - q))):= by
  have := calc (fun n => ∑ i ∈ range n, q ^ i)
    _ = (fun n => (q ^ n - 1) / (q - 1)) :=
     funext fun n => geom_sum_eq' (ne_of_lt (abs_lt.1 h).2) n
    _ = (fun n => 1 / (1 - q) - (1 - q) ⁻¹ * q ^ n ) := by grind
  rw [tendsto_congr (f₂ := fun n =>  1 / (1 - q) - (1 - q) ⁻¹ * q ^ n) (congr_fun this)]
  rw [show 1 / (1 - q) = 1 / (1 - q) -  (1 - q) ⁻¹ * 0 by grind]
  apply Tendsto.sub (tendsto_const_nhds_iff.2 (by norm_num))
  apply Tendsto.const_mul _
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one h

lemma summable_of_geomSum (q : ℝ) (h : |q| < 1) : Summable (fun n : ℕ => q ^ n) := by
  refine summable_of_absolute_convergence_real ⟨1 / (1 - |q|), ?_⟩
  rw [funext (fun i => abs_pow q i)]
  rw [← abs_abs q] at h
  exact_mod_cast tendsto_of_geomSum |q| h

example (q : Real) (h : |q| < 1) : ∑' n : ℕ, q ^ n = 1 / (1 - q) := by
  have : Summable (fun n : ℕ => q ^ n) := summable_of_geomSum q h
  exact_mod_cast tendsto_nhds_unique this.tendsto_sum_tsum_nat (tendsto_of_geomSum q h)

/- derivation -/
open Real
example (a : ℝ) (h : 0 < a) :
  deriv (fun x : ℝ ↦ x ^ x) a = a ^ a + a ^ a * log a := by
  have : (fun x : ℝ ↦ x ^ x) =ᶠ[𝓝 a] (fun x : ℝ ↦ exp (x * log x)) := by
    set s := Set.Ioo (a / 2) (a + 1) with hs
    filter_upwards [show s ∈ 𝓝 a from IsOpen.mem_nhds isOpen_Ioo (by simpa[s])] with x hx
    have : 0 < x := by
      rw [hs, Set.mem_Ioo] at hx
      refine lt_trans ?_ hx.1
      simp [h]
    rwa [mul_comm, exp_mul, exp_log]
  rw [EventuallyEq.deriv_eq this]
  have haNe0 : a ≠ 0 := ne_comm.1 (ne_of_lt h)
  exact calc deriv (fun x ↦ exp (x * log x)) a
    _ = exp (a * log a) * deriv (fun x ↦ x * log x) a := by
      rw [_root_.deriv_exp]
      · exact DifferentiableOn.differentiableAt differentiableOn_mul_log
         (show {0}ᶜ ∈ 𝓝 a by simpa only [compl_singleton_mem_nhds_iff])
    _ = exp (a * log a) * (log a + 1) := by rwa [deriv_mul_log]
    _ = a ^ a + a ^ a * log a := by rwa [mul_comm a, exp_mul, exp_log, mul_add, mul_one, add_comm]
