import Mathlib

variable (R : Type) [Ring R]
variable (Q : Type) [AddCommGroup Q] [Module R Q]

variable (n : ℕ)

-- Q^n Fin n -> Q
instance : SMul (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  smul M v i := ∑ j, M i j • v j

@[simp]
lemma smul_apply (M : Matrix (Fin n) (Fin n) R) (v : Fin n → Q) (i : Fin n) :
    (M • v) i = ∑ j, M i j • v j := rfl

instance : MulAction (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  one_smul v := by
    ext i
    simp [Matrix.one_apply]
  mul_smul := by
    intro M N v
    ext i
    simp only [smul_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]

instance : DistribMulAction (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  smul_zero := by
    intro M
    ext
    simp
  smul_add := by
    intro M v w
    ext i
    simp [smul_add, Finset.sum_add_distrib]

instance : Module (Matrix (Fin n) (Fin n) R) (Fin n → Q) where
  add_smul := by
    intro M N v
    ext i
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul := by
    intro v
    ext i
    simp

#check Module.Finite
#check TwoSidedIdeal.mem_matricesOver
variable (R : Type) [CommRing R]
variable (M : Type) [AddCommGroup M] [Module R M]
variable (I : Ideal R)

/- S is the span set ,  S = {x₁, ..., x_n}, x_i = ∑ a_ij x_j, a_ij ∈ I.
  (A-I) S.vec = 0 => f= det (A-I)- =
-/
#check Matrix.map
open Module Submodule
theorem Nakayama (hfin : Module.Finite R M) (hi: I • ⊤ = (⊤ : Submodule R M)) :
   ∃ (f : R), 1 + f ∈ I ∧ ∀ (m : M), f • m = (0 : M) := by
  rw [Module.finite_def, fg_def] at hfin
  rcases hfin with ⟨S', hsf, hspan⟩
  let S := hsf.toFinset
  let n := Finset.card S
  let gen : (Fin n) → M := fun i => ((Finset.equivFin S).symm i)
  have rep (m : M) : ∃ v : Fin n →  I, m = ∑ i, (v i : R) • (gen i) := by sorry
  let A := Matrix.map (Matrix.of fun i j => (Classical.choose (rep (gen i)) j) ) <| I.subtype
  let f := - (1 - A).det
  use f
  constructor
  · suffices 1 + (f : R⧸I) = 0 by
      change ((1 : R) + f : R⧸I) = 0 at this
      rw [← map_add, Ideal.Quotient.eq_zero_iff_mem,] at this
      exact this
    simp [Matrix.map_det]
    have : Matrix.map A (Ideal.Quotient.mk I) = (0 : Matrix (Fin n) (Fin n) (R ⧸ I)) := by sorry
    sorry -- det on R/ I to det
  · intro m
    have vm := rep m

 sorry

#check Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
