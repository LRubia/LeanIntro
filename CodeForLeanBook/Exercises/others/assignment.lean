import Mathlib
  -- I can NOT infer the precise definition of the set S, so I failed to complete it.
  -- The following is some experiments.

/- Let me try to complete some missing part for the assignment pdf-/
/- The possible question.
    Given positive integers a and b with gcd(a, b)= 1, and an integer N
  with a parity N = k * a + l * b with k, l ≥ 0, there exists a pair of integers (x, y)
  such that N = x * a + y * b, x ≥ 0, y ≥ 0, and x + y is odd. -/ -- NOT CORRECT

variable (a b : ℕ) (hab : b - a = (1 : ZMod 2))

-- def N := k * a + l * b
-- def u (t : ℤ) := k + b * t
-- def v (t : ℤ) := l - a * t

/- u + v ≡ 0 mod 2 iff t ≡ k + l mod 2 -/
def solution (k l : ℕ) (t : ℤ) :=
  letI u := k + b * t; letI v := l - a * t
  if (u + v : ℤ) = (1 : ZMod 2) then (u, v)
    else (u + b, v - a)

def S := {N : ℤ | ∃ x y : ℤ, N = x * a + y * b ∧ (0 ≤ x ∧ 0 ≤ y) ∧ (x + y : ℤ) = (1 : ZMod 2)}

#check Int.ceil
def tDomain (k l : ℕ) := {t : ℤ |
  letI u := k + b * t; letI v := l - a * t
  if (u + v : ℤ) = (1 : ZMod 2) then Int.ceil (- k / b : ℚ) ≤ t ∧ t ≤ Int.floor (l / a : ℚ)
    else Int.ceil (- (k + b) / b : ℚ) ≤ t ∧ t ≤ Int.floor ((l - a) / a : ℚ)}

lemma Nonneg_iff_tDomain (k l : ℕ) (t : ℤ) : t ∈ tDomain a b k l ↔
    0 ≤ (solution a b k l t).1 ∧ 0 ≤ (solution a b k l t).2 := by
  -- letI u := k + b * t; letI v := l - a * t
  by_cases h : (k + b * t + (l - a * t ): ℤ) = (1 : ZMod 2)
  · simp only [tDomain, neg_add_rev, Set.mem_setOf_eq, h, ↓reduceIte,
     solution, Int.sub_nonneg, Int.ceil_le, Int.le_floor]
    sorry
  · simp only [tDomain, neg_add_rev, Set.mem_setOf_eq, h, ↓reduceIte,
     solution, Int.sub_nonneg, Int.ceil_le, Int.le_floor]
    sorry

lemma IsSolution (k l : ℕ) (t : ℤ) (hab : b - a = (1 : ZMod 2)) (ht : t ∈ tDomain a b k l) :
    letI x := (solution a b k l t).1; letI y := (solution a b k l t).2;
    a * x  + b * y ∈ S a b := by
  use (solution a b k l t).1
  use (solution a b k l t).2
  -- letI u := k + b * t; letI v := l - a * t
  refine ⟨?_, (Nonneg_iff_tDomain a b k l t).1 ht, ?_⟩
  · by_cases h : (k + b * t) + (l - a * t) = (1 : ZMod 2) <;>
    · simp [solution, h]
      ring
  · by_cases h : (k + b * t  + (l - a * t) : ℤ) = (1 : ZMod 2)
    · simp only [solution, h, ↓reduceIte]
    · simp only [solution, h, ↓reduceIte]
      rw [ ZMod.intCast_eq_one_iff_odd, Int.not_odd_iff_even,
         ← ZMod.intCast_eq_zero_iff_even] at h
      rw [← add_zero 1, ← h, ← hab, ← sub_eq_zero]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_sub]
      abel

lemma AllSolution (t : ℤ) (hab : b - a = (1 : ZMod 2)) :
  ∀ N ∈ S a b, ∃ (k l : ℕ), ∀ t ∈ tDomain a b k l,
    N = (solution a b k l t).1 * a + (solution a b k l t).2 * b := by
  let P (m : ℕ) := ∀ (x y : ℤ), (2* m + 1= x + y ∧ (0 ≤ x ∧ 0 ≤ y)) → (∃ (k l : ℕ),
   ∀ t ∈ tDomain a b k l, x * a + y * b = (solution a b k l t).1 * a + (solution a b k l t).2 * b)
  suffices h : ∀ (m : ℕ), P m by
    rintro N ⟨x, y, hsum, hnneg, hodd⟩
    obtain ⟨m, hm⟩ := ZMod.intCast_eq_one_iff_odd.1 hodd
    have hm' : x + y = 2 * (Int.toNat m) + 1 := by
      have : 0 ≤ m := by linarith [hm, hnneg]
      rwa [hm, Int.toNat_eq_max, max_eq_left_iff.2]
    obtain ⟨k, l, hkl⟩ := (h (Int.toNat m)) x y ⟨hm'.symm, hnneg⟩
    use k, l
    intro t ht
    rw [hsum, hkl t ht]
  intro m
  induction m with
  | zero =>
      rintro x y ⟨hsum, hnneg, hodd⟩
      simp_all
      by_cases h : x = 1
      · subst h
        simp_all
        use 0, 0
        intro t ht
        simp? [solution, hsum, ht]
        sorry
      sorry
  | succ m hPm =>
    rintro x y ⟨hsum, hnneg⟩
    have : x + y ≥ 3 := by simp [← hsum]; linarith
    by_cases hxy : x ≥ 1 ∧ y ≥ 1
    · have hsum' := calc 2 * (m : ℤ) + 1
          _ = 2 * ↑(m + 1) + 1 - 2 := by omega
          _ = x + y - 2 := by rw [hsum]
          _ = (x - 1) + (y - 1) := by ring
      have hnneg' : 0 ≤ (x - 1) ∧ 0 ≤ (y - 1) := ⟨by linarith [hxy], by linarith [hxy]⟩
      obtain ⟨k, l, hkl⟩ := hPm (x - 1) (y - 1) ⟨hsum', hnneg'⟩
      use k + 1, l + 1
      intro t ht
      simp only [solution, hsum, ht]
      sorry
