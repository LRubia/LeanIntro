import Mathlib

namespace nt

@[ext]
structure Zsqrt (d : ℤ) where
  re : ℤ
  im : ℤ

/--
a + b√d  + a' + b'√d  = (a + a') + (b + b')√d
-/
instance (d : ℤ) : Add (Zsqrt d) where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

@[simp]
lemma add_re (d : ℤ) (x y : Zsqrt d) : (x + y).re = x.re + y.re := rfl

@[simp]
lemma add_im (d : ℤ) (x y : Zsqrt d) : (x + y).im = x.im + y.im := rfl


instance (d : ℤ) : Zero (Zsqrt d) where
  zero := ⟨0, 0⟩

@[simp]
lemma zero_re (d : ℤ) : (0 : Zsqrt d).re = 0 := rfl

@[simp]
lemma zero_im (d : ℤ) : (0 : Zsqrt d).im = 0 := rfl

instance (d : ℤ) : Neg (Zsqrt d) where
  neg x := ⟨-x.re, -x.im⟩

@[simp]
lemma neg_re (d : ℤ) (x : Zsqrt d) : (-x).re = -x.re := rfl

@[simp]
lemma neg_im (d : ℤ) (x : Zsqrt d) : (-x).im = -x.im := rfl

/--
(a + b√d)(a' + b'√d) = (aa' + dbb') + (ab' + a'b)√d
-/
instance (d : ℤ) : Mul (Zsqrt d) where
  mul x y := ⟨x.re * y.re + d * x.im * y.im, x.re * y.im + x.im * y.re⟩

@[simp]
lemma mul_re (d : ℤ) (x y : Zsqrt d) :
    (x * y).re = x.re * y.re + d * x.im * y.im := rfl

@[simp]
lemma mul_im (d : ℤ) (x y : Zsqrt d) :
    (x * y).im = x.re * y.im + x.im * y.re := rfl

instance (d : ℤ) : One (Zsqrt d) where
  one := ⟨1, 0⟩

@[simp]
lemma one_re (d : ℤ) : (1 : Zsqrt d).re = 1 := rfl
@[simp]
lemma one_im (d : ℤ) : (1 : Zsqrt d).im = 0 := rfl

instance (d : ℤ) : AddCommGroup (Zsqrt d) where
  add_assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simp [add_assoc]
  zero_add := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  add_zero := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  add_comm := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;>
    simp [add_comm]

instance (d : ℤ) : CommRing (Zsqrt d) where
  left_distrib := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  right_distrib := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  zero_mul := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_zero := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext <;>
    simpa using by ring
  one := ⟨1, 0⟩
  one_mul := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_one := by
    rintro ⟨a, b⟩
    ext <;>
    simp
  mul_comm := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    ext <;>
    simpa using by ring

instance (d : ℤ) : Nontrivial (Zsqrt d) where
  exists_pair_ne := ⟨0, 1, by
    intro r
    simp [Zsqrt.ext_iff] at r⟩


@[simp]
lemma intCast_re (d : ℤ) (n : ℤ) : (n : Zsqrt d).re = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Int.cast_add, Int.cast_natCast] at *; simp [ih]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg] at *
    simp [neg_re, ih, sub_eq_add_neg]
@[simp]
lemma intCast_im (d : ℤ) (n : ℤ) : (n : Zsqrt d).im = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Int.cast_add, Int.cast_natCast] at *; simp [ih]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg] at *
    simp [ih]

open Polynomial

abbrev toQuotPoly (d : ℤ) : ℤ[X] →+* Zsqrt d := Polynomial.aeval (⟨0, 1⟩ : Zsqrt d) |>.toRingHom

-- #synth AddMonoid (WithBot ℕ)
-- #synth LE (WithBot ℕ)
-- #check Zsqrt.ext_iff
-- #synth ExistsAddOfLE (WithBot ℕ) --false
-- #synth OrderedSub (WithBot ℕ) -- false
-- #check tsub_le_iff_right
-- #check Polynomial.X_pow_add_C_ne_one
lemma ker_toQuotPoly (d : ℤ) :
    RingHom.ker (toQuotPoly d) = Ideal.span {X ^ 2 - Polynomial.C d} := by
  ext p
  simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe, eq_intCast]
  constructor
  · intro h
    let r := p %ₘ (X ^ 2 - C d)
    have eq : p = r + (X ^ 2 - C d) * (p /ₘ (X ^ 2 - C d))  := by
      rw [Polynomial.modByMonic_add_div]
      apply Polynomial.monic_X_pow_sub_C
      simp
    have := congr($(eq).aeval (⟨0, 1⟩ : Zsqrt d))
    simp only [h, eq_intCast, map_add, map_mul, aeval_sub, map_pow, aeval_X,
      show (⟨0, 1⟩ : Zsqrt d) ^ 2 = d by ext <;> simp [pow_two], map_intCast, sub_self, zero_mul,
      add_zero] at this
    -- p %ₘ (X ^ 2 - C d) can not have degree 1 so it must be zero
    have hdeg : natDegree r ≤ 1 := by
      suffices natDegree r < 2 by omega
      rw [← natDegree_X_pow_sub_C (n := 2) (r := d)]
      change (_ %ₘ _).natDegree < _
      apply natDegree_modByMonic_lt p ?_ ?_;
      · exact Polynomial.monic_X_pow_sub_C _ (by omega)
      · exact fun h => (show 2 ≠ 0 by omega) <| by
          simpa only [natDegree_X_pow_sub_C, natDegree_one] using congr_arg natDegree h
    obtain ⟨a, b, hreq⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
    simp only [hreq, eq_intCast, map_add, map_mul, map_intCast, aeval_X, Zsqrt.ext_iff, zero_re,
      add_re, mul_re, intCast_re, mul_zero, intCast_im, mul_one, add_zero, zero_add, zero_im,
      add_im, mul_im] at this
    suffices r = 0 by
      rw [eq, this, zero_add, eq_intCast]
      refine Ideal.mem_span_singleton.2 ?_
      exact dvd_mul_right ..
    simp [hreq, ← this.1, ← this.2]
  · intro h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨p, rfl⟩ := h
    simp only [map_mul, aeval_sub, map_pow, aeval_X,
      show (⟨0, 1⟩ : Zsqrt d) ^ 2 = d by ext <;> simp [pow_two], map_intCast, sub_self, zero_mul]

lemma toQuotPoly_surj (d : ℤ) : Function.Surjective (toQuotPoly d) := by
  rintro ⟨a, b⟩
  use (Polynomial.C a + Polynomial.C b * X)
  simp [Zsqrt.ext_iff]

end nt
