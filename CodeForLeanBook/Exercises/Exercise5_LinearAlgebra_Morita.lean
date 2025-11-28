import Mathlib

/-
category R-mod

category Matrix(R)-mod

-/

section MatrixMod
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

-- Q →ₗ[R] Q'
-- Q^n →ₗ[Matrix (Fin n) (Fin n) R] Qⁿ

variable (Q' : Type) [AddCommGroup Q'] [Module R Q']
variable (f : Q →ₗ[R] Q')

variable {Q Q'}
def map_lift : (Fin n → Q) →ₗ[Matrix (Fin n) (Fin n) R] (Fin n → Q') :=
{ toFun := fun v i => f (v i)
  map_add' := by intro v w; ext i; simp
  map_smul' := by
    intro M v
    ext i
    change f (∑ j, M i j • v j) = ∑ j, _
    simp }

-- #check LinearMap.id
-- #check map_lift R n (LinearMap.id (M := Q))
example : map_lift R n (LinearMap.id (M := Q)) = LinearMap.id (M := (Fin n → Q)):= by
  ext v i
  simp [map_lift]

variable (Q'' : Type) [AddCommGroup Q''] [Module R Q''] in
example (g : Q' →ₗ[R] Q'') : map_lift R n (g ∘ₗ f) = (map_lift R n g) ∘ₗ (map_lift R n f) := by
  ext v i
  simp [map_lift]

end MatrixMod

section E11
variable (R : Type) [Ring R] (n : ℕ)
variable (P : Type) [AddCommGroup P] [Module (Matrix (Fin n) (Fin n) R) P] [NeZero n]

-- P as R-module r • p => [r, 000; 0, r, 000; 0 0 r 00]

-- def asMod (P : Type) [AddCommGroup P] [Module (Matrix (Fin n) (Fin n) R) P] [NeZero n] := P

-- instance : AddCommGroup (asMod R n P) :=
--   inferInstanceAs (AddCommGroup P)

-- instance : Module (Matrix (Fin n) (Fin n) R) (asMod R n P) :=
--     inferInstanceAs (Module (Matrix (Fin n) (Fin n) R) P)


-- instance : Module R (asMod R n P) where
--   smul r p := Matrix.diagonal (fun i : Fin n => r) • p
--   one_smul := _
--   mul_smul := _
--   smul_zero := _
--   smul_add := _
--   add_smul := _
--   zero_smul := _

def E11_mul : P →+ P where
  toFun p := Matrix.single (0 : Fin n) (0 : Fin n) (1 : R) • p
  map_zero' := by simp
  map_add' := by simp

abbrev mod : AddSubgroup P  :=
  AddMonoidHom.range (E11_mul R n P)

@[simp]
lemma mod_ext (p p' : mod R n P) : p = p' ↔ p.val = p'.val := by
  simp only [SetLike.coe_eq_coe]

instance : AddCommGroup (mod R n P) := by
  infer_instance

instance : SMul R (mod R n P) where
  smul r p := ⟨Matrix.scalar (Fin n) r • p.val, by
    rcases p with ⟨_, ⟨p0, rfl⟩⟩
    use (Matrix.scalar (Fin n) r) • p0
    simp only [E11_mul, ← mul_smul, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 1
    apply Matrix.mem_range_scalar_iff_commute_single'.1
    simp
    ⟩

@[simp]
lemma smul_apply_val (r : R) (p : mod R n P) :
  (r • p : mod R n P) = Matrix.scalar (Fin n) r • p.val := rfl

instance : MulAction R (mod R n P) where
  one_smul := by
    rintro ⟨_, ⟨p, rfl⟩⟩
    simp
  mul_smul r r' p:= by
    simp only [mod_ext, smul_apply_val, map_mul, mul_smul]

instance : DistribMulAction R (mod R n P) where
  smul_zero r := by simp
  smul_add r p p' := by simp

instance : Module R (mod R n P) where
  add_smul r s p := by simp only [mod_ext, smul_apply_val, map_add, add_smul]; rfl
  zero_smul p := by simp

-- P →ₗ[Matrix n n R] P'
-- mod P ->ₗ[R] mod P'

variable (P' : Type) [AddCommGroup P'] [Module (Matrix (Fin n) (Fin n) R) P']
variable (f : P →ₗ[Matrix (Fin n) (Fin n) R] P')
def map_reduce : (mod R n P) →ₗ[R] (mod R n P') where
  toFun p := Subtype.mk (f p.val) <| by
    rcases p with ⟨_, ⟨p, rfl⟩⟩
    use f p
    simp only [E11_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  map_add' x y := by simp
  map_smul' x := by simp


#check DecidableRel
-- ℚ

set_option maxHeartbeats 0 in
example : 2 ^ 100 = 1267650600228229401496703205376 := by
  decide

-- open Classical in
set_option maxHeartbeats 0 in
example : Nat.sqrt 4 = 2 := by --???
  -- letI : DecidableEq ℕ := Classical.decEq ℕ
  decide
