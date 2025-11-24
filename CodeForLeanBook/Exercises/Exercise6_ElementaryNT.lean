import Mathlib

def a (n : ℕ) : ℤ :=
  2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1

def b (n : ℕ) : ℤ := 2 ^ (2 * n + 1) + 2 ^ (n + 1)+ 1

example (n : ℕ) : a n + b n ≡ if Odd n then 3 else 1 [ZMOD 5] :=
  calc a n + b n
    _ ≡ 2 ^ (2 * n + 1) * 2 + 2 [ZMOD 5] := by simp only [a, b]; ring_nf; rfl
    _ ≡ 2 ^ (2 * n ) * 4 + 2 [ZMOD 5] := by simp [pow_add]; ring_nf; rfl
    _ ≡ 4 ^ n * 4 + 2 [ZMOD 5] := by simp [pow_mul]
    _ ≡ 4 ^ (n + 1) + 2 [ZMOD 5] := by simp[pow_add]
    _ ≡ (-1) ^ (n + 1) + 2 [ZMOD 5] := by gcongr; norm_num
    _ ≡ if Odd n then 1 + 2 else -1 + 2 [ZMOD 5] := by
      split_ifs with h
      · apply Odd.add_one at h
        obtain ⟨k, hk⟩ := h
        rw [hk, ← two_mul, pow_mul, neg_one_pow_two, one_pow]
      · apply Nat.not_odd_iff_even.1 at h
        obtain ⟨k, hk⟩ := h
        rw [hk, ← two_mul, pow_add, pow_mul, neg_one_pow_two, one_pow, pow_one, one_mul]
    _ ≡ if Odd n then 3 else 1 [ZMOD 5] := by
      split_ifs with h <;> congr


example (n : ℕ) : a n ≡   letI r := n % 4
    if r = 0 then 1 else if (r = 1 ∨ r = 2) then 0 else 3 [ZMOD 5] :=
  let r := n % 4
  have hmod : 2 ^ n ≡ 2 ^ r [ZMOD 5] := by
    apply Int.ModEq.trans (b := 2 ^ (4 * (n / 4) + r))
    · congr
      zify
      exact (Int.mul_ediv_add_emod n 4 |>.symm)
    · rw [pow_add, pow_mul]
      conv_rhs => rw [← one_mul (2 ^ r), ← one_pow (n / 4)]
      gcongr
      norm_num
  calc a n
    _ ≡ (2 ^ n) ^ 2 * 2 - 2 ^ n * 2 + 1 [ZMOD 5] := by
      simp only [a]
      congr
      ring
    _ ≡ (2 ^ r) ^ 2 * 2 - (2 ^ r) * 2 + 1 [ZMOD 5] := by
      gcongr
    _ ≡ if r = 0 then 1 else if (r = 1 ∨ r = 2) then 0 else 3 [ZMOD 5] := by
      split_ifs with hr0 hr12
      · rw [hr0]; norm_num
      · cases hr12 with
        | inl hr1 => rw [hr1]; norm_num
        | inr hr2 => rw [hr2]; norm_num
      · have : r = 3 := by  omega
        rw [this]
        norm_num

example (n : ℕ) : b n ≡ letI r := n % 4
    if r = 0 ∨ r = 3 then 0 else if r = 1 then 3 else 1[ZMOD 5] :=
  let r := n % 4
  have hmod : 2 ^ n ≡ 2 ^ r [ZMOD 5] := by
    apply Int.ModEq.trans (b := 2 ^ (4 * (n / 4) + r))
    · congr
      zify
      exact (Int.mul_ediv_add_emod n 4 |>.symm)
    · rw [pow_add, pow_mul]
      conv_rhs => rw [← one_mul (2 ^ r), ← one_pow (n / 4)]
      gcongr
      norm_num
  calc b n
    _ ≡ (2 ^ n) ^ 2 * 2 + 2 ^ n * 2 + 1 [ZMOD 5] := by
      simp only [b]; congr; ring
    _ ≡ (2 ^ r) ^ 2 * 2 + (2 ^ r) * 2 + 1 [ZMOD 5] := by
      gcongr
    _ ≡ if r = 0 ∨ r = 3 then 0 else if r = 1 then 3 else 1[ZMOD 5] := by
      split_ifs with h h
      · cases h with
        | inl hr0 => rw [hr0]; norm_num
        | inr hr3 => rw [hr3]; norm_num
      · rw [h]; norm_num
      · have : r = 2 := by omega
        rw [this]; norm_num

theorem totient_dvd_factorial (n : ℕ) (hn : 0 < n) : n.totient ∣ n.factorial := by
  let s := Nat.factorization n
  have eq1 : n.totient = (∏ p ∈ s.support, p ^ (s p - 1)) * (∏ p ∈ s.support, (p - 1)) := by
    rw [Nat.totient_eq_prod_factorization (by omega), ← Finset.prod_mul_distrib]
    rfl
  have eq2 : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, Nat.factorial_succ, show n - 1 + 1 = n by omega]

  rw [eq1, eq2]
  gcongr
  · rw [show n = ∏ p ∈ s.support, p ^ (s p) from
      Nat.factorization_prod_pow_eq_self (n := n) (by omega) |>.symm]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    exact Nat.pow_dvd_pow _ (by omega)
  · have (N : ℕ): N.factorial = ∏ j ∈ Finset.Ico 1 (N + 1), j := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [Nat.factorial_succ, ih, Finset.prod_Ico_succ_top (show 1 ≤ N + 1 by omega)]
          ring
    rw [this, show ∏ p ∈ s.support, (p - 1) = ∏ j ∈ Finset.Ico 1 n with j + 1 ∈ s.support, j by
      fapply Finset.prod_bij
      · exact fun p _ => p - 1
      · intro p hp
        simp only [Nat.support_factorization, Nat.mem_primeFactors, ne_eq, Finset.mem_filter,
          Finset.mem_Ico, s] at hp ⊢
        have p_ineq1 : 2 ≤ p := hp.1.two_le
        have p_ineq2 : p ≤ n := by
          exact Nat.le_of_dvd (by omega) hp.2.1
        simp only [show p - 1 + 1 = p by omega]
        exact ⟨⟨by omega, by omega⟩, hp.1, hp.2.1, by omega⟩
      · intro p hp q hq h
        simp only [Nat.support_factorization, Nat.mem_primeFactors, ne_eq, s] at hp hq ⊢
        have p_ineq : 2 ≤ p := hp.1.two_le
        have q_ineq : 2 ≤ q := hq.1.two_le
        omega
      · rintro i hi
        simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, Finset.mem_Ico] at hi
        exact ⟨i + 1, by simpa using hi.2, by omega⟩
      · simp]
    apply Finset.prod_dvd_prod_of_subset
    rw [show n - 1 + 1 = n by omega]
    simp?

-------------

example (n : ℕ) (h : Odd n) : n ∣(2 ^ n.factorial - 1) :=
  calc n
    _ ∣  2 ^ n.totient - 1 := by
      have : 2 ^ n.totient ≡ 1 [MOD n] :=
        Nat.ModEq.pow_totient (Nat.coprime_two_left.2 h)
      exact Nat.modEq_iff_dvd' (by rw [one_le_pow_iff (by aesop)]; grind)
        |>.1 this.symm
    _ ∣  2 ^ n.factorial - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one 2 (totient_dvd_factorial n (by grind))

namespace quadra_feature
variable (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]

@[simps]
def sq : (ZMod p)ˣ →* (ZMod p)ˣ :=
  { toFun := fun x => x ^ 2
    map_one' := by simp
    map_mul' x y := by ext; simpa using by ring }

example (hp : p ≠ 2) : Set.ncard { x : (ZMod p)ˣ | IsSquare x } = (p - 1) / 2 := by
  have set_eq : { x : (ZMod p)ˣ | IsSquare x } = MonoidHom.range (sq p) := by
    ext x; simp [IsSquare, pow_two, eq_comm]
  rw [set_eq]

  have card_eq₀ : Set.ncard {x : (ZMod p)ˣ | x ^ 2 = 1} = 2 := by
    rw [show {x : (ZMod p)ˣ | x ^ 2 = 1} = {1, -1} by
      ext x
      simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, sq_eq_one_iff,
        Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Units.val_neg]]
    rw [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    rw [Set.mem_singleton_iff]
    by_contra h
    rw [Units.ext_iff,Units.val_neg,  Units.val_one, ← sub_eq_zero] at h
    ring_nf at h
    refine Ring.two_ne_zero ?_ h
    rwa [ZMod.ringChar_zmod_n p]
  rw [Set.ncard_eq_toFinset_card, Set.Finite.toFinset_setOf] at card_eq₀

  let e : (ZMod p)ˣ ⧸ MonoidHom.ker (sq p) ≃* MonoidHom.range (sq p) :=
    QuotientGroup.quotientKerEquivRange _

  have card_eq₁ := Fintype.card_congr e.toEquiv

  have card_eq₂ :
      Fintype.card ((ZMod p)ˣ ⧸ MonoidHom.ker (sq p)) = (p - 1) / 2 := by
    have eq := (MonoidHom.ker (sq p)).card_eq_card_quotient_mul_card_subgroup
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, MonoidHom.mem_ker,
      sq_apply] at eq
    rw [Nat.totient_prime Fact.out, Fintype.subtype_card, card_eq₀] at eq
    omega

  rw [← card_eq₂, card_eq₁, Set.ncard_eq_toFinset_card, eq_comm]
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp

end quadra_feature
