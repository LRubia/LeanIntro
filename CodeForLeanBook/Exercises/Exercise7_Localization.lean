-- import Mathlib.GroupTheory.MonoidLocalization.Basic
-- import Mathlib.Algebra.Module.LocalizedModule.Basic
-- import Mathlib.LinearAlgebra.TensorProduct.Tower
-- import Mathlib.Algebra.Group.Submonoid.Pointwise
-- import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib

suppress_compilation

namespace loc
open Localization

variable {R : Type} [CommRing R] (S T : Submonoid R)
variable (M : Type) [AddCommGroup M] [Module R M]

#check Localization S
#check Nontrivial

example : Nontrivial (Localization S) ↔ 0 ∉ S := by
  constructor
  · rintro ⟨x, y, h⟩ hS
    have : x = y := by
      induction x, y using Localization.induction_on₂ with | H x y =>
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use ⟨0, hS⟩
      simp
    exact h this
  · intro hS
    refine ⟨0, 1, ?_⟩
    intro heq
    rw [← mk_zero 1, ← mk_one, mk_eq_mk_iff, r_iff_exists] at heq
    rcases heq with ⟨⟨s, hsm⟩, hs⟩
    simp only [OneMemClass.coe_one, mul_zero, mul_one] at hs
    subst hs
    exact hS hsm

instance : IsLocalization (nonZeroDivisors ℤ) ℚ where
  map_units x := by
    rw [isUnit_iff_exists]
    refine ⟨(x⁻¹ : ℚ), by simp, by simp⟩
  surj y := ⟨(y.num, ⟨y.den, by simp⟩), by simp⟩
  exists_of_eq := by
    intro y1 y2 h
    refine ⟨1, by simpa using h⟩

open TensorProduct
#check curry
instance : IsLocalizedModule S (Algebra.ofId R (Localization S)).toLinearMap where
  map_units s := by
    rw [isUnit_iff_exists]
    let φ : Localization S →ₗ[R] Localization S :=
    { toFun x := x.liftOn (fun r t => Localization.mk r (s * t)) (by
        intro r r' t t'
        simp only [Localization.r_iff_exists, Subtype.exists, exists_prop,
          Localization.mk_eq_mk_iff, Submonoid.coe_mul, forall_exists_index, and_imp]
        intro s' hs' H
        refine ⟨s', hs', ?_⟩
        rw [← mul_assoc, ← mul_assoc, mul_comm s' s, mul_assoc, mul_assoc, H]
        ring)
      map_add' := by
        intros x y
        induction x using Localization.induction_on with | H x =>
        induction y using Localization.induction_on with | H y =>
        rcases x with ⟨x, ⟨tx, hs⟩⟩
        rcases y with ⟨y, ⟨ty, ht⟩⟩
        simp only [Localization.add_mk, Submonoid.mk_mul_mk, Localization.liftOn_mk,
          Submonoid.coe_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists, Subtype.exists,
          exists_prop]
        exact ⟨1, by simp, by ring⟩
      map_smul' := by
        intros r x
        induction x using Localization.induction_on with | H x =>
        rcases x with ⟨x, ⟨s, hs⟩⟩
        simp [Localization.smul_mk, Localization.liftOn_mk] }
    refine ⟨φ, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨t, ht⟩⟩
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Localization.liftOn_mk,
        Module.algebraMap_end_apply, Localization.smul_mk, smul_eq_mul, Module.End.one_apply,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists, Submonoid.coe_mul, Subtype.exists,
        exists_prop, φ]
      exact ⟨1, by simp, by ring⟩
  surj := by
    intro x
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨x, ⟨t, ht⟩⟩
    refine ⟨(x, ⟨t, ht⟩), ?_⟩
    simp [Localization.smul_mk, ← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
  exists_of_eq := by
    rintro r r' eq
    simp only [AlgHom.toLinearMap_apply, Algebra.ofId_apply, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, OneMemClass.coe_one, one_mul,
      Subtype.exists, exists_prop] at eq
    obtain ⟨c, hc, eq⟩ := eq
    exact ⟨⟨c, hc⟩, eq⟩

def divByAux (s : S) : R →ₗ[R] Localization S :=
{ toFun r := Localization.mk r s
  map_add' := by intro r r'; simp [Localization.add_mk_self]
  map_smul' := by intro r x; simp [Localization.smul_mk] }

def divBy (s : S) : Localization S →ₗ[R] Localization S :=
IsLocalizedModule.lift S
  ((Algebra.ofId R (Localization S)).toLinearMap)
  (divByAux (s := s))
  (by
    intro t
    rw [isUnit_iff_exists]
    refine ⟨⟨⟨(· * Localization.mk 1 t), by simp [add_mul]⟩, by simp⟩, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_mul,
        mul_one, Module.algebraMap_end_apply, Localization.smul_mk, smul_eq_mul,
        Module.End.one_apply, Localization.mk_eq_mk_iff, Localization.r_iff_exists,
        Submonoid.coe_mul, Subtype.exists, exists_prop]
      exact ⟨1, by simp, by ring⟩)

@[simp]
lemma divBy_apply (r : R) (s t : S) :
    divBy S s (Localization.mk r t) = Localization.mk r (s * t) := by
  delta divBy
  generalize_proofs h1 h2 h3 h4 h5 h
  have ht := h t
  rw [Module.End.isUnit_iff] at ht
  apply_fun _ using ht.injective
  simp only [Module.algebraMap_end_apply]
  rw [← map_smul, Localization.smul_mk, Localization.smul_mk]
  simp only [smul_eq_mul,
    show Localization.mk (t * r) t = Localization.mk r 1 by
      simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists],
    show Localization.mk (t * r) (s * t) = Localization.mk r s by
      simpa [Localization.mk_eq_mk_iff, Localization.r_iff_exists] using ⟨1, by simp, by ring⟩]
  exact IsLocalizedModule.lift_apply S
    ((Algebra.ofId R (Localization S)).toLinearMap) (divByAux (s := s)) h r

#synth Module R (LocalizedModule S M)
#synth IsLocalizedModule S (LocalizedModule.mkLinearMap S M)
-- def divByModAux (s : S) : M →ₗ[R] LocalizedModule S M := ---LocalizedModule.divBy
-- { toFun m := LocalizedModule.mk m s
--   map_add' m m':= by
--     simp [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
--     refine ⟨1, by simp [smul_smul]⟩
--   map_smul' := by intro r m; simp [LocalizedModule.smul'_mk] }

-- def divByMod (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
--   toFun x := Localization.mk 1 s • x
--   map_add' x y := by simp
--   map_smul' r x:= by
--     induction x using LocalizedModule.induction_on with | h m mr =>
--     simp [LocalizedModule.smul'_mk, LocalizedModule.mk_smul_mk]
-- def divByMod (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M :=
--   Module.toModuleEnd (Localization S) (S := (Localization S))
--       (LocalizedModule S M) (Localization.mk 1 s)

-- @[simp]
-- lemma divByMod_apply (t s : S) (m : M) :
--     divByMod S M s (LocalizedModule.mk m t) = LocalizedModule.mk m (s * t) := by
--   delta divByMod
--   simp [LocalizedModule.mk_smul_mk]

def ex02 : LocalizedModule S M →ₗ[R] Localization S ⊗[R] M :=
IsLocalizedModule.lift S (LocalizedModule.mkLinearMap S M)
  { toFun m := 1 ⊗ₜ m
    map_add' := by simp [tmul_add]
    map_smul' := by simp }
  (by
    intro s
    rw [isUnit_iff_exists]
    refine ⟨TensorProduct.map (divBy (s := s)) LinearMap.id, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        Module.End.mul_apply, map_tmul, divBy_apply, LinearMap.id_coe, id_eq,
        Module.algebraMap_end_apply, smul_tmul', Localization.smul_mk, smul_eq_mul,
        Module.End.one_apply]
      congr 1
      simpa [Localization.mk_eq_mk_iff, Localization.r_iff_exists] using ⟨1, by simp, by ring⟩)

@[simp]
lemma ex02_apply (s : S) (m : M) :
    ex02 S M (LocalizedModule.mk m s) = Localization.mk 1 s ⊗ₜ m := by
  delta ex02
  let phi := algebraMap R (Module.End R (Localization S ⊗[R] M)) s
  have phi_inj : Function.Injective phi := by
    apply Function.LeftInverse.injective (g := algebraMap (Localization S)
      (Module.End (Localization S) (Localization S ⊗[R] M)) (Localization.mk 1 s))
    intro p
    simp only [Module.algebraMap_end_apply, LinearMap.map_smul_of_tower, phi]
    rw [← algebraMap_smul (A := Localization S), ← Localization.mk_one_eq_algebraMap, smul_smul]
    rw [show Localization.mk (s : R) 1 * Localization.mk 1 s = 1
      by simp [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]]
    rw [one_smul]
  apply_fun phi using phi_inj
  simp only [Module.algebraMap_end_apply, phi, ← map_smul, LocalizedModule.smul'_mk,
    TensorProduct.smul_tmul']
  rw [show LocalizedModule.mk ((s : R) • m) s = LocalizedModule.mkLinearMap S M m
    by simp [LocalizedModule.mk_eq]; use 1; aesop]
  rw [IsLocalizedModule.lift_apply]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr
  rw [← Localization.mk_one, Localization.smul_mk, Localization.mk_eq_mk_iff,
   Localization.r_iff_exists]
  refine ⟨1, by simp⟩

def ex03 : (Localization S ⊗[R] M) →ₗ[R] LocalizedModule S M :=
  TensorProduct.lift <| IsLocalizedModule.lift S ((Algebra.ofId R (Localization S)).toLinearMap)
    { toFun r := r • LocalizedModule.mkLinearMap S M
      map_add' := by simp [add_smul]
      map_smul' := by simp [mul_smul] } <| by
    rintro ⟨s, hs⟩
    rw [isUnit_iff_exists]
    refine ⟨⟨⟨fun f => LocalizedModule.divBy ⟨s, hs⟩ ∘ₗ f, by simp [LinearMap.comp_add]⟩,
      by simp [LinearMap.comp_smul]⟩, ?_, ?_⟩
    all_goals
    · ext φ m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply,
        LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply, LocalizedModule.divBy_apply,
        Module.End.one_apply]
      set x := φ m
      clear_value x
      induction x using LocalizedModule.induction_on with | h m x =>
      simpa [LocalizedModule.liftOn_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] using
        ⟨1, by simp, by simp [mul_smul]⟩

@[simp]
lemma ex03_apply (r : R) (m : M) : (ex03 S M) (Localization.mk r 1 ⊗ₜ[R] m)
  = LocalizedModule.mk (r • m) 1 := by
  simp only [ex03, lift.tmul]
  rw [show (Localization.mk r 1) = (Algebra.ofId R (Localization S)).toLinearMap r
    by simp only [AlgHom.toLinearMap_apply, Algebra.ofId_apply, Localization.mk_one_eq_algebraMap]]
  rw [IsLocalizedModule.lift_apply]
  simp [LocalizedModule.smul'_mk]

@[simp]
lemma ex03_apply' (r : R) (s : S) (m : M) :
    ex03 S M (Localization.mk r s ⊗ₜ[R] m) = LocalizedModule.mk (r • m) s := by
  let hs := algebraMap R (Module.End R (LocalizedModule S M)) s
  have hs_inj :Function.Injective hs := by
    apply Function.LeftInverse.injective (g := LocalizedModule.divBy s)
    intro p
    simp only [hs]
    exact LocalizedModule.divBy_mul_by s p
  apply_fun hs using hs_inj
  simp only [Module.algebraMap_end_apply, LocalizedModule.smul'_mk, hs, ← map_smul,
    TensorProduct.smul_tmul', Localization.smul_mk]
  rw [show Localization.mk ((s : R) • r) s = Localization.mk r 1
    by simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists]]
  rw [show LocalizedModule.mk ((s : R) • r • m) s = LocalizedModule.mk (r • m) 1
    by simp [LocalizedModule.mk_eq]; exact ⟨1, by aesop⟩]
  rw [ex03_apply]


-- #synth  IsLocalizedModule S (LocalizedModule.mkLinearMap S M)
-- #check IsLocalizedModule.lift_apply
-- #check IsLocalizedModule.iso_symm_apply'
-- #check IsUnit.unit

-- instance IsLocalizedModule S
def ex04 : LocalizedModule S M ≃ₗ[R] Localization S ⊗[R] M :=
  LinearEquiv.ofLinear (ex02 ..) (ex03 ..) (by
  ext x m
  induction x using Localization.induction_on with | H x =>
  rcases x with ⟨x, ⟨tx, htx⟩⟩
  simp [TensorProduct.smul_tmul', Localization.smul_mk]
  )<| by
  ext x
  induction x using LocalizedModule.induction_on with | h m s =>
  simp


instance : IsLocalizedModule S (M' := Localization S ⊗[R] M) {
  toFun m := 1 ⊗ₜ m
  map_add' m n := by simp [tmul_add]
  map_smul' r m := by simp
} where
  map_units s := by
    rw [isUnit_iff_exists]
    refine ⟨TensorProduct.map (divBy (s := s)) LinearMap.id, ?_, ?_⟩
    all_goals
    · ext x
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        Module.End.mul_apply, map_tmul, divBy_apply, LinearMap.id_coe, id_eq,
        Module.algebraMap_end_apply, smul_tmul', Localization.smul_mk, smul_eq_mul,
        Module.End.one_apply]
      congr 1
      simpa [Localization.mk_eq_mk_iff, Localization.r_iff_exists] using ⟨1, by simp, by ring⟩
  surj x := by
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [smul_zero, LinearMap.coe_mk, AddHom.coe_mk, Prod.exists, exists_const]
      use 0
      simp
    | tmul x y =>
      induction x using Localization.induction_on with | H x =>
      rcases x with ⟨x, ⟨tx, htx⟩⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.exists, Subtype.exists, Submonoid.mk_smul,
        exists_prop]
      refine ⟨x • y,  tx, htx, ?_⟩
      simp only [smul_tmul', smul_mk, smul_eq_mul, ← mk_one, tmul_smul, mul_one]
      congr 1
      simp [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    | add x y hx hy =>
      rcases hx with ⟨⟨mx, ⟨rx, _⟩⟩, hx⟩
      rcases hy with ⟨⟨my, ⟨ry, _⟩⟩, hy⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_add, Prod.exists, Subtype.exists,
        Submonoid.mk_smul, exists_prop] at *
      refine ⟨ry • mx + rx • my, rx * ry, by aesop, ?_⟩
      rw [mul_comm, ← smul_smul, mul_comm, ← smul_smul, hx, hy, smul_tmul', smul_tmul,
        smul_tmul', smul_tmul, tmul_add]
  exists_of_eq := by
    intro x y heq
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at *
    have := congr(ex03 S M $heq)
    simpa [← mk_one, ex03_apply, one_smul, LocalizedModule.mk_eq] using this

-- -- #synth IsScalarTower R (Localization S) M
-- #check Function.Injective
-- #check Algebra.TensorProduct.mk_one_injective_of_isScalarTower
-- #check TensorProduct.tmul_zero
-- #check isLocalizedModule_iff_isBaseChange
#check S ⊔ T

def ex05 : Localization (S ⊔ T) →+* Localization (S.map (algebraMap R (Localization T))) :=
  IsLocalization.lift (M := S ⊔ T) (g := algebraMap R _) <| by
    rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Submonoid.coe_sup] at hx
    rcases hx with ⟨s, hs, t, ht, rfl⟩
    simp only [map_mul, IsUnit.mul_iff] at hx ⊢
    constructor
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk 1 ⟨algebraMap _ _ s, by simpa using ⟨s, hs, rfl⟩⟩, ?_, ?_⟩
      · simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
      · rw [mul_comm]
        simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk (Localization.mk 1 ⟨t, ht⟩) ⟨1, by simp⟩, ?_, ?_⟩
      · simp [← Algebra.smul_def, Localization.smul_mk]
      · rw [mul_comm]
        simp [← Algebra.smul_def, Localization.smul_mk]

#synth SMul R (Localization S)
@[simp]
lemma ex05_apply (r : R) (s : S) (t : T) : --- how to define the apply better
    ex05 S T (Localization.mk r (⟨s.1 * t.1, Submonoid.mul_mem_sup s.2 t.2⟩)) =
    Localization.mk (Localization.mk r t) (⟨algebraMap R (Localization T) s, by aesop⟩) := by
    simp only [ex05, mk_eq_mk', IsLocalization.lift_mk'_spec, map_mul]
    simp_rw [← mk_eq_mk']
    change mk (mk r 1) 1 = (mk _ 1) * (mk _ 1) * (Localization.mk _ _)
    simp only [← mk_one_eq_algebraMap, mk_mul, mul_one, one_mul, mk_eq_mk_iff, r_iff_exists,
      OneMemClass.coe_one, Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and]
    refine ⟨1, by simp, 1, by simp, by group⟩

def ex06 : Localization (S.map (algebraMap R (Localization T))) →+* Localization (S ⊔ T) :=
  IsLocalization.lift (M := S.map (algebraMap R (Localization T)))
    (g := IsLocalization.map (M := T) (T := S ⊔ T) _ (RingHom.id _)
      (by erw [Submonoid.comap_id]; exact le_sup_of_le_right fun ⦃x⦄ a ↦ a)) <| by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    simp only [IsLocalization.map_eq, RingHom.id_apply]
    rw [isUnit_iff_exists]
    refine ⟨Localization.mk 1 ⟨x, Submonoid.mem_sup_left hx⟩, ?_, ?_⟩
    · simp [← Algebra.smul_def, Localization.smul_mk]
    · rw [mul_comm]; simp [← Algebra.smul_def, Localization.smul_mk]

@[simp]
lemma ex06_apply (r : R) (s : S) (t : T) :
    ex06 S T (Localization.mk (Localization.mk r t) (⟨algebraMap R (Localization T) s, by aesop⟩)) =
    Localization.mk r (⟨s.1 * t.1, Submonoid.mul_mem_sup s.2 t.2⟩) := by
    simp only [ex06, mk_eq_mk', IsLocalization.lift_mk'_spec, IsLocalization.map_mk',
      RingHom.id_apply, IsLocalization.map_eq]
    simp_rw [← mk_eq_mk', ← mk_one_eq_algebraMap, mk_mul, mk_eq_mk_iff, r_iff_exists]
    refine ⟨1, by group⟩

#synth SMul R (Localization (S ⊔ T))
def ex07 : Localization (S ⊔ T) ≃+* Localization (S.map (algebraMap R (Localization T))) :=
  RingEquiv.ofHomInv (ex05 ..) (ex06 ..) (by
    ext x
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨x, ⟨_, htx⟩⟩
    rw [← SetLike.mem_coe, Submonoid.coe_sup] at htx
    rcases htx with ⟨s, hs, t, ht, rfl⟩
    simp only [SetLike.mem_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      RingHom.id_apply] at *
    rw [ex05_apply S T x ⟨s, hs⟩ ⟨t, ht⟩]
    rw [ex06_apply]
  ) <| by
    ext x
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨x, ⟨_, htx⟩⟩
    induction x using Localization.induction_on with | H x =>
    rcases x with ⟨x, ⟨t, ht⟩⟩
    simp only [Submonoid.mem_map] at htx
    rcases htx with ⟨s, hs, rfl⟩
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingHom.id_apply]
    rw [ex06_apply S T x ⟨s, hs⟩ ⟨t, ht⟩]
    rw [ex05_apply]


#check S.map (algebraMap R (Localization T))
instance : IsLocalization (S ⊔ T) <| Localization (S.map (algebraMap R (Localization T))) where
  map_units ts := by
    rcases ts with ⟨_, hst⟩
    rw [← SetLike.mem_coe, Submonoid.coe_sup] at hst
    rcases hst with ⟨s, hs, t, ht, rfl⟩
    simp only [map_mul, IsUnit.mul_iff] at hst ⊢
    constructor
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk 1 ⟨algebraMap _ _ s, by simpa using ⟨s, hs, rfl⟩⟩, ?_, ?_⟩
      · simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
      · rw [mul_comm]
        simp only [← Localization.mk_one_eq_algebraMap, ← Algebra.smul_def, Localization.smul_mk]
        rw [← Algebra.algebraMap_eq_smul_one, ← Localization.mk_one]
        simp [Localization.mk_one_eq_algebraMap]
    · rw [isUnit_iff_exists]
      refine ⟨Localization.mk (Localization.mk 1 ⟨t, ht⟩) ⟨1, by simp⟩, ?_, ?_⟩
      · simp [← Algebra.smul_def, Localization.smul_mk]
      · rw [mul_comm]
        simp [← Algebra.smul_def, Localization.smul_mk]
  surj y := by
    induction y using Localization.induction_on with | H y =>
    rcases y with ⟨y, ⟨_, ⟨s, hs, rfl⟩⟩⟩
    induction y using Localization.induction_on with | H y =>
    rcases y with ⟨x, t, ht⟩
    use ⟨x, ⟨s * t, Submonoid.mul_mem_sup hs ht⟩⟩
    simp only [map_mul, ← Localization.mk_one_eq_algebraMap]
    change _ * (Localization.mk (Localization.mk s 1) 1 * Localization.mk (Localization.mk t 1) 1)
       = Localization.mk (Localization.mk x 1) 1
    simp [Localization.mk_mul, mk_eq_mk_iff, r_iff_exists]
    refine ⟨1, by simp, ?_⟩
    simp only [map_one, one_mul, mk_eq_mk_iff, r_iff_exists]
    refine ⟨1, by simp; group⟩
  exists_of_eq := by
    intro x y h
    simp only [Subtype.exists, exists_prop] at *
    change mk (mk x 1) 1 = mk (mk y 1) 1 at h
    simp [mk_eq_mk_iff, r_iff_exists] at h
    rcases h with ⟨s, hs, h⟩
    simp [← mk_one_eq_algebraMap, mk_mul, mk_eq_mk_iff, r_iff_exists] at h
    rcases h with ⟨t, ht, h⟩
    refine ⟨s * t, Submonoid.mul_mem_sup hs ht, by grind⟩

#synth Algebra R (Localization (Submonoid.map (algebraMap R (Localization T)) S))
end loc
