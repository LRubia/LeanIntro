import Mathlib

#check Set.compl
#check Finset.card_compl_add_card
#check Fin
inductive Fruit
| apple | banana | orange | pear | kiwi | mango | peach | plum | cherry | grape | lemon | lime
deriving DecidableEq, Fintype

-------prove by bijection construction
example (n k : ℕ) (h : k ≤ n) : n.choose k = n.choose (n - k) := by -- k > n, then 0 = 1
  have e : Finset.powersetCard k (Finset.univ (α := Fin n)) ≃
    Finset.powersetCard (n - k) (Finset.univ (α := Fin n)) := {
      toFun p := ⟨p.1ᶜ, by
        have := Finset.card_compl_add_card p.1
        simp only [(Finset.mem_powersetCard.1 p.2), Fintype.card_fin, Finset.mem_powersetCard,
          Finset.subset_univ, true_and] at *
        omega⟩
      invFun p := ⟨p.1ᶜ, by
        have := Finset.card_compl_add_card p.1
        simp only [(Finset.mem_powersetCard.1 p.2), Fintype.card_fin, Finset.mem_powersetCard,
          Finset.subset_univ, true_and] at *
        omega⟩
      left_inv := by intro p; simp
      right_inv := by intro p; simp
    }
  simpa using Fintype.card_congr e

example (n : ℕ) : 2 ^ n = ∑ k ∈ Finset.range (n + 1), n.choose k := by
  have e : Finset.powerset (Finset.univ (α := Fin n)) ≃
    Σ k : Fin (n + 1), Finset.powersetCard k (Finset.univ (α := Fin n)) := {
      toFun p := ⟨⟨p.1.card, by
        have := Finset.card_le_card <| Finset.mem_powerset.1 p.2
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega ⟩, ⟨p, by simp⟩⟩
      invFun x := ⟨x.2.1, by simp⟩
      left_inv := by intro p; simp
      right_inv := by
        rintro ⟨⟨nk, hk⟩, ⟨p, hp⟩⟩
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hp
        subst hp
        rfl
    }
  simpa [Finset.sum_range] using Fintype.card_congr e

#check Sum
#check Sum.rec
#check Sigma.rec
#check Finset.card_univ
example : 2 + 2 + 2 = 3 * 2 := by
  let e : (Fin 2 ⊕ Fin 2) ⊕ Fin 2≃ Fin 3 × Fin 2 := {
    -- toFun := Sum.rec (inl := Sum.rec (fun x => ⟨(0 : Fin 3), x⟩)
    --   (fun x => ⟨(1 : Fin 3), x⟩)) (inr := fun x => ⟨(2 : Fin 3), x⟩)
    toFun
      | Sum.inl (Sum.inl x) => ⟨(0 : Fin 3), x⟩
      | Sum.inl (Sum.inr x) => ⟨(1 : Fin 3), x⟩
      | Sum.inr x => ⟨(2 : Fin 3), x⟩
    invFun
      | ⟨(0 : Fin 3), p⟩ => Sum.inl (Sum.inl p)
      | ⟨(1 : Fin 3), p⟩ => Sum.inl (Sum.inr p)
      | ⟨(2 : Fin 3), p⟩ => Sum.inr p
    left_inv := by intro p; aesop
    right_inv := by intro x; aesop
  }

  have := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin] at this ---- how to avoid rw close the goal

#check Finset.min'
#check Finset.max'
#check Finset.card_pos
#check Finset.min'_lt_max'
#check Nat.lt
#check Nat.sub_eq_iff_eq_add
#check Fin.eq_mk_iff_val_eq
example (n : ℕ) : {(x, y, z) : ℕ × ℕ × ℕ | x + y + z = n}.ncard = (n + 2).choose 2 := by
  let ppS := {(x, y, z) : ℕ × ℕ × ℕ | x + y + z = n}
  have e : ppS ≃ Finset.powersetCard 2 (Finset.univ (α := Fin (n + 2))) := {
    toFun | ⟨⟨x, y, z⟩, h⟩ => ⟨⟨{⟨x , by grind;⟩, ⟨x + y + 1, by grind⟩}, by simp; grind⟩, by
      simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, Finset.card_cons, Finset.card_mk,
        Multiset.card_singleton, Nat.reduceAdd]
      ⟩
    invFun p :=
      letI pCard2 := (Finset.mem_powersetCard.1 p.2).2
      letI pNem : p.1.Nonempty := Finset.card_pos.1 (by omega)
      letI x := (p.1.min' pNem).val; letI y := (p.1.max' pNem).val - (x + 1)
      ⟨(x, y, n - x - y), by
        have hz : n ≥ x + y := by
          have : p.1.max' pNem ≥ x + 1 := Finset.min'_lt_max'_of_card p.1 (by omega)
          grind                                                   --- _ ≥ _ + 1 "=" _ > _ !!!
        grind⟩
    left_inv := by
      rintro ⟨⟨x, y, z⟩, hsum⟩
      simp only [ppS, Set.coe_setOf, Set.mem_setOf_eq, Multiset.insert_eq_cons, Finset.mk_cons,
        Finset.cons_eq_insert, Finset.nonempty_mk, ne_eq, Multiset.singleton_ne_zero,
        not_false_eq_true, Finset.min'_insert, Fin.coe_min, Finset.max'_insert, Fin.coe_max,
        Subtype.mk.injEq, Prod.mk.injEq, inf_eq_left]
      let s := x + y + 1
      have h : x ≤ s := by omega
      change x ≤ s ∧ max x s - (min x s + 1) = y ∧ n - min x s - (max x s - (min x s + 1)) = z
      simp only [h, sup_of_le_right, inf_of_le_left, Nat.reduceSubDiff, add_tsub_cancel_left,
        true_and, s]
      grind
    right_inv := by
      rintro ⟨p, hp⟩
      have pCard2 := (Finset.mem_powersetCard.1 hp).2
      ext ⟨x, hx⟩
      simp only [Fin.eta, Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert,
        Finset.mem_insert, Finset.mem_mk, Multiset.mem_singleton, Fin.mk.injEq]
      let p1 := p.min' <| Finset.card_pos.1 (by omega)
      let p2 := p.max' <| Finset.card_pos.1 (by omega)
      have : p2.val ≥ p1.val + 1 := Finset.min'_lt_max'_of_card p (by omega)
      rw [← Nat.add_sub_assoc this, Nat.add_sub_add_left, Nat.sub_add_cancel (by omega)]
      constructor
      · intro h
        rcases h with (h | h)
        · simpa [h] using Finset.min'_mem p _
        · simpa [h] using Finset.max'_mem p _
      · obtain ⟨y1, y2, ⟨hy, rfl⟩⟩ := Finset.card_eq_two.1 pCard2
        have hp1 : p1.val = min y1 y2 := by aesop
        have hp2 : p2.val = max y1 y2 := by aesop
        grind
  }
  let f : ppS → Fin (n + 1) × Fin (n + 1) × Fin (n + 1) := fun p =>
    ⟨⟨p.1.1, by grind⟩, ⟨p.1.2.1, by grind⟩, ⟨p.1.2.2, by grind⟩⟩
  have injf : Function.Injective f := by rintro ⟨_, hp⟩ ⟨_, hq⟩ h; grind
  -- have : Finite ppS := Finite.of_injective f injf
  have : Fintype ppS := Fintype.ofInjective f injf
  have := Fintype.card_congr e
  rw [Set.ncard_eq_toFinset_card' ppS, ← Nat.card_eq_card_toFinset, Nat.card_eq_fintype_card, this]
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Fintype.card_finset_len,
    Fintype.card_fin]

#check Finite.card_subtype_le
#synth Fintype (Fin 100 × Fin 1000)
#check Nat.card
#check PowerSeries

---generating function
open PowerSeries
variable (n a b c : ℕ)

namespace power_series
def ppS (n : ℕ) : Finset (ℕ × ℕ × ℕ):=
  let bounds := Finset.range (n + 1)
  (bounds ×ˢ bounds ×ˢ bounds).filter (fun ⟨x, y, z⟩ ↦ x + y + z = n)

def fsFun : ℚ⟦X⟧ := mk fun n => (ppS n).card

def gf : ℚ⟦X⟧ := mk fun _ => 1

lemma product_rule : fsFun = gf  ^ 3 := by
  ext n
  simp only [fsFun, coeff_mk, gf, coeff_pow, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, Nat.cast_inj]
  have e : ppS n ≃ ((Finset.range 3).finsuppAntidiag n) := {
    toFun p := ⟨Finsupp.onFinset (Finset.range 3)
        (fun | 0 => p.1.1 | 1 => p.1.2.1 | 2 => p.1.2.2 | _ => 0 ) <| by grind, by
      have hp := p.2
      simp only [ppS, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_finsuppAntidiag, Finsupp.onFinset_apply,
        Finsupp.support_onFinset_subset, and_true]
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, ← hp.2]⟩
    invFun f := ⟨⟨f.1 0, f.1 1, f.1 2⟩, by
      simp only [ppS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      have hsum := f.2
      simp only [Finset.mem_finsuppAntidiag, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton] at hsum
      grind⟩
    left_inv := by intro p; simp
    right_inv := by
      intro f
      have := f.2
      ext x
      simp only [Finset.mem_finsuppAntidiag, Finsupp.onFinset_apply] at *
      have := Finsupp.support_subset_iff.1 this.2
      match x with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | x + 3 =>
        refine Eq.symm <| this _ ?_
        erw [Finset.mem_range]
        simp}
  have := Fintype.card_congr e
  simpa [Fintype.card_coe]

lemma fsFun_eq : fsFun = (1 - X)⁻¹ ^ 3 := by
  rw [product_rule]
  congr
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp), gf]
  ext n
  rw [coeff_one, mul_sub, mul_one, mul_comm, map_sub, coeff_mk,
    ← pow_one X, coeff_X_pow_mul', coeff_mk]
  by_cases h : n = 0
  · simp [h]
  rw [if_pos (by omega), if_neg h, sub_self]

lemma choose2_rat : (n.choose 2 : ℚ) = n * (n - 1) / 2 := by
    rw [Nat.choose_two_right]
    by_cases h : Even n
    · rcases h with ⟨k, rfl⟩
      simp only [← two_mul, mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_div_cancel_left₀, Nat.cast_mul, Nat.cast_ofNat, mul_eq_mul_left_iff,
        Rat.natCast_eq_zero]
      by_cases h : k = 0
      · simp [h]
      · simp [Nat.sub_eq_max_sub, show 1 ≤ 2 * k by omega]
    obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.1 <| Nat.not_even_iff_odd.1 h
    simp [mul_left_comm]

lemma powerS_eq : (1 - X : ℚ⟦X⟧)⁻¹ ^ 3 = mk fun n => ((n + 2).choose 2 : ℚ) := by
  suffices : (1 - 3 * X + 3 * X ^ 2 - X ^ 3 : ℚ⟦X⟧) * (mk _) = 1
  · rw [pow_three, Eq.comm (b := mk _), ← mul_assoc]
    repeat rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    rw [eq_inv_iff_mul_eq_one (by simp), mul_assoc, mul_assoc]
    conv_rhs => rw [← this]
    ring
  ext n
  rw [show (3 : ℚ⟦X⟧) * X = 3 * X ^ 1 by simp]
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add]
  erw [coeff_one, coeff_C_mul (a := 3), coeff_X_pow_mul']
  erw [coeff_C_mul (a := 3), coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [h1]
  by_cases h2 : n = 2
  · simpa [h2, (show Nat.choose 4 2 = 6
      by simp [Nat.choose_eq_fast_choose, Nat.fast_choose]; )] using by group
  have hge3 : 3 ≤ n := by omega
  simp only [coeff_mk, if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
    if_pos hge3, h0, ↓reduceIte]
  simp only [choose2_rat, Nat.cast_add, Nat.cast_ofNat]
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one, Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_ofNat, sub_add_cancel, Nat.cast_sub (by omega)]
  ring

example (n : ℕ) : (ppS n).card = (n + 2).choose 2 := by
  have := congr(coeff n $(fsFun_eq.trans powerS_eq))
  simp only [fsFun, coeff_mk] at this
  simpa

def ppS' (n a b c : ℕ) : Finset (ℕ × ℕ × ℕ):=
  let bounds := Finset.range (n + 1) ---- plus one makes it positive
  (bounds ×ˢ bounds ×ˢ bounds).filter (fun ⟨x, y, z⟩ ↦ (a + 1) * x + (b + 1) * y + (c + 1) * z = n)

def fsFun' : ℚ⟦X⟧ := mk fun n => (ppS' n a b c).card

def gf' : ℚ⟦X⟧ := mk fun n => if (a + 1) ∣ n then 1 else 0

lemma product_rule' : fsFun' a b c = gf' a * gf' b * gf' c := by
  ext n
  simp only [fsFun', coeff_mk, gf', coeff_mul, mul_ite, mul_one, mul_zero]
  let valueSet (n a b c : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Finset.antidiagonal n).filter (fun x => (c + 1) ∣ x.2)).biUnion fun x =>
    ((Finset.antidiagonal x.1).filter (fun y => (b + 1) ∣ y.2 ∧ (a + 1) ∣ y.1)).map
      ⟨fun y => (y, x.2), fun _ _ h => (Prod.ext_iff.1 h).1⟩

  have e : ppS' n a b c ≃ valueSet n a b c := {
    toFun | ⟨⟨p1, p2, p3⟩, hp⟩ => ⟨⟨⟨(a + 1) * p1, (b + 1) * p2⟩, (c + 1) * p3⟩, by
      simp only [ppS', Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp [hp.2, valueSet] ⟩
    invFun | ⟨⟨⟨m1, m2⟩, m3⟩, hm⟩ => ⟨⟨m1 / (a + 1), m2 / (b + 1), m3 / (c + 1)⟩, by
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_map,
        Function.Embedding.coeFn_mk, Prod.mk.injEq, Prod.exists, existsAndEq, and_true, true_and,
        exists_eq_right_right, valueSet] at hm
      rcases hm with ⟨⟨hsum, hc⟩, hb, ha⟩
      simp only [ppS', Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      simp only [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb, Nat.mul_div_cancel' hc, hsum,
        and_true]
      grind [Nat.div_le_self]⟩
    left_inv := by intro p; simp
    right_inv := by
      rintro  ⟨⟨⟨m1, m2⟩, m3⟩, hm⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_map,
        Function.Embedding.coeFn_mk, Prod.mk.injEq, Prod.exists, existsAndEq, and_true, true_and,
        exists_eq_right_right, valueSet] at hm
      rcases hm with ⟨⟨hsum, hc⟩, hb, ha⟩
      simp only [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb, Nat.mul_div_cancel' hc]
      }
  -- set rhs := _
  -- change _ = rhs
  have h_rhs : (valueSet n a b c).card =  -- r := by
      ∑ x ∈ Finset.antidiagonal n,
        if (c + 1) ∣ x.2 then ∑ y ∈ Finset.antidiagonal x.1,
        if (b + 1) ∣ y.2 ∧ (a + 1) ∣ y.1 then 1 else 0 else 0 := by
    simp only [Finset.sum_boole, Nat.cast_id, valueSet]
    rw [Finset.card_biUnion, Finset.sum_filter]
    · apply Finset.sum_congr rfl
      intro x hx
      split_ifs with h_div_c
      · rw [Finset.card_map]
      · rfl
    · -- Prove disjointness for biUnion
      intro x₁ hx₁ x₂ hx₂ h_diff
      simp only [Finset.disjoint_iff_ne, Finset.mem_map]
      rintro _ ⟨y₁, _, rfl⟩ _ ⟨y₂, _, rfl⟩ h_eq
      injection h_eq with _ h_k
      apply h_diff
      ext
      · have s1 := Finset.mem_antidiagonal.1 (Finset.mem_filter.1 hx₁).1
        have s2 := Finset.mem_antidiagonal.1 (Finset.mem_filter.1 hx₂).1
        grind
      · exact h_k
  have := Eq.trans (Fintype.card_coe <| ppS' n a b c).symm <| Fintype.card_congr e
  rw [this, Fintype.card_coe, h_rhs]
  norm_cast
  congr 1
  ext x
  split_ifs
  · simp [ite_and]
  · rfl

lemma gf_eq' : gf' a = (1 - X ^ (a + 1) : ℚ⟦X⟧)⁻¹ := by
  rw [gf', PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  simp only [mul_comm, sub_mul, one_mul, map_sub, coeff_mk, coeff_X_pow_mul',
    Nat.dvd_sub_self_right, coeff_one]
  by_cases h0 : n = 0
  · simp [h0]
  by_cases hdvd : a + 1 ∣ n
  · simp [hdvd, if_pos (show a + 1 ≤ n from Nat.le_of_dvd (by omega) hdvd), h0]
  simpa [h0, hdvd] using show _
    from Nat.lt_of_le_of_ne (h₂ := fun h => (h ▸ hdvd) <| Nat.dvd_refl n) ---cool

lemma fsFun_eq' : gf' 0 * gf' 1 * gf' 1 = mk fun n => ((n/2 + 2).choose 2 : ℚ) := by
  have : gf' 0 * gf' 1 * gf' 1 = (-X^5 + X^4 + 2 *X^3 - 2 *X^2 - X^1 + 1)⁻¹:= by
    simp only [gf_eq', zero_add, Nat.reduceAdd]
    -- repeat rw [← PowerSeries.mul_inv_rev] ---3 goals ??
    rw [← PowerSeries.mul_inv_rev, ← PowerSeries.mul_inv_rev]
    congr; ring
  rw [this, Eq.comm, PowerSeries.eq_inv_iff_mul_eq_one (by simp), mul_comm]
  ext n
  simp only [show (2 : ℚ⟦X⟧) = C 2 from rfl, add_mul, sub_mul, neg_mul, mul_assoc, one_mul,
    map_add, map_sub, map_neg, coeff_X_pow_mul', coeff_mk, coeff_C_mul, mul_ite, mul_zero,
    coeff_one]
  by_cases h5 : n < 5
  · interval_cases n <;> {try simp [choose2_rat]; try ring}
  rw [not_lt] at h5
  simp_rw [if_pos (show 4 ≤ n by omega), if_pos (show 3 ≤ n by omega),
      if_pos h5, if_pos (show 2 ≤ n by omega), if_pos (show 1 ≤ n by omega)]
  rcases Nat.even_or_odd' n with ⟨k, rfl|rfl⟩
  · have : 3 ≤ k := by omega
    have div_simp : ∀ (c : ℕ), c ≤ 2*k → (2*k - c) / 2 =
      k - (c + 1) / 2 := by intro c _; omega
    rw [div_simp _ (by omega), div_simp _ (by omega), div_simp _ (by omega),
      div_simp _ (by omega), div_simp _ (by omega)]
    simpa [choose2_rat, Nat.cast_sub this, Nat.cast_sub (show 2 ≤ k by omega),
     Nat.cast_sub (show 1 ≤ k by omega), if_neg (show k ≠ 0 by grind)]
      using by ring
  · have div_simp : ∀ (c : ℕ), c ≤ 2*k + 1 → (2*k + 1 - c) / 2 =
      k - c / 2 := by intro c _; omega
    rw [div_simp _ (by omega), div_simp _ (by omega), div_simp _ (by omega),
      div_simp _ (by omega), div_simp _ (by omega)]
    simp [choose2_rat, Nat.mul_add_div]

example (n : ℕ) : (ppS' n 0 1 1).card = (n/2 + 2).choose 2 := by
  have := congr(coeff n $(product_rule' 0 1 1 |>.trans fsFun_eq'))
  simp only [fsFun', coeff_mk] at this
  simpa

end power_series
