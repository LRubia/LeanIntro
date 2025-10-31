import Mathlib

suppress_compilation

variable {G : Type} [Group G] (H : Subgroup G)

open Pointwise
#check Ne

structure QGroup : Type where
  carrier : Set G
  isCoset : ∃ g : G, carrier = g • H

namespace QGroup

variable {H}

instance : SetLike (QGroup H) G where
  coe C := C.carrier
  coe_injective' := by
    intro C D; cases C; cases D; simp

@[ext]
lemma ext {C D : QGroup H} (h : (C : Set G) = D) : C = D := by
  cases C; cases D; simp at h; simp [h]

def out (C : QGroup H) : G := Classical.choose C.isCoset

@[simp]
lemma out_spec (C : QGroup H) : C.out • H = (C : Set G) :=
  Classical.choose_spec C.isCoset |>.symm

lemma mem_iff_out (C : QGroup H) (g : G) : g ∈ C ↔ ∃ h ∈ H, g = C.out • h := by
  rw [← SetLike.mem_coe, ← C.out_spec, Set.mem_smul_set]
  tauto

variable (H) in
def gen (g : G) : QGroup H :=
  ⟨g • H, ⟨g, rfl⟩⟩


lemma gen_def (g : G) : (gen H g : Set G) = g • H := rfl

@[simp]
lemma mem_gen_iff (g : G) {x : G} : x ∈ gen H g ↔ ∃ h ∈ H, x = g * h := by
  rw [← SetLike.mem_coe, gen_def, Set.mem_smul_set]
  tauto

@[simp]
lemma gen_out (C : QGroup H) : gen H C.out = C := by
  ext g
  simp only [SetLike.mem_coe, mem_gen_iff]
  rw [C.mem_iff_out]
  rfl

/-New lemma: ∃ h,  out = g * h -/
lemma out_eq_gentor_mul (g : G) : ∃ h ∈ H, (gen H g).out = g * h := (mem_gen_iff g).mp (
    show (gen H g).out ∈ gen H g  by
      nth_rewrite 1 [← gen_out (gen H g)]
      simp [-gen_out])

@[simp]
lemma mem_out_gen (g : G) {x : G} : x ∈ ((gen H g).out • H : Set G) ↔ x ∈ (g • H : Set G) := by
  simp [Set.mem_smul_set, eq_comm]

/- We don NOT require H.Normal except for some special lemmas,
  so we write this condition in these special lemmas. -/
/-completion of the sorry part-/
@[simp]
lemma mem_out_gen_smul [H.Normal] (g g' : G) {x : G} :
    x ∈ ((gen H g).out • g' • H : Set G) ↔ x ∈ (g • g' • H : Set G) := by
  simp only [Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul, eq_comm]
  obtain ⟨g0, hg0, hout⟩ := out_eq_gentor_mul g
  rw [hout]
  constructor
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, rfl⟩⟩
    refine ⟨g0 * g' * y, ?_, by simp [mul_assoc]⟩
    refine ⟨g'⁻¹ * g0 * g' * y, ?_, by simp [mul_assoc]⟩
    refine H.mul_mem ?_ hy
    exact Subgroup.Normal.conj_mem' ‹H.Normal› g0 hg0 g'
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, rfl⟩⟩
    refine ⟨g0⁻¹ * g' * y, ?_, by simp [mul_assoc]⟩
    refine ⟨g'⁻¹ * g0⁻¹ * g' * y, ?_, by simp [mul_assoc]⟩
    refine H.mul_mem ?_ hy
    exact Subgroup.Normal.conj_mem' (inferInstance : H.Normal) g0⁻¹ (H.inv_mem hg0) g'

@[elab_as_elim]
theorem gen_induction {P : QGroup H → Prop}
    (h : ∀ g : G, P (gen H g)) :
    ∀ C : QGroup H, P C := by
  intro C
  rw [← C.gen_out]
  tauto

@[simp]
theorem gen_eq_iff (g : G) (C : QGroup H) : gen H g = C ↔ g ∈ C := by
  constructor
  · rintro rfl
    simp
  · intro h
    rw [C.mem_iff_out] at h
    obtain ⟨x, hx, rfl⟩ := h
    ext y
    simp only [smul_eq_mul, SetLike.mem_coe, mem_gen_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [C.mem_iff_out]
      use x * y, mul_mem hx hy
      simp [mul_assoc]
    · rw [C.mem_iff_out]
      rintro ⟨y, hy, rfl⟩
      use x⁻¹ * y, mul_mem (H.inv_mem hx) hy
      simp [mul_assoc]

instance : One (QGroup H) where
  one := ⟨H, ⟨1, by simp⟩⟩

lemma one_def : ((1 : QGroup H) : Set G) = H := rfl

@[simp]
lemma mem_one_iff {g : G} : g ∈ (1 : QGroup H) ↔ g ∈ H := Iff.rfl

@[simp]
lemma gen_one : gen H 1 = 1 := by -- little simplication
  simp

instance : Mul (QGroup H) where
  mul C D := ⟨C.out • D.out • H, ⟨C.out * D.out, by simp [mul_smul, out_spec]⟩⟩

lemma mul_def (C D : QGroup H) :
    ((C * D : QGroup H) : Set G) = C.out • D.out • H := rfl

/-completion of the sorry part-/
@[simp] lemma gen_mul_gen [H.Normal] (g g' : G) : gen H g * gen H g' = gen H (g * g') := by
  symm
  simp only [gen_eq_iff]
  change g * g' ∈ ((gen H g).out • (gen H g').out • H : Set G)
  rw [mem_out_gen_smul, Set.mem_smul_set]
  simp only [smul_eq_mul, mem_out_gen]
  exact ⟨g', by simp [← gen_def]⟩

lemma mul_one' [H.Normal] (C : QGroup H) : C * 1 = C := by
  induction C using gen_induction with | h g =>
  rw [← gen_one, gen_mul_gen, mul_one]

lemma one_mul' [H.Normal] (C : QGroup H) : 1 * C = C := by
  induction C using gen_induction with | h g =>
  rw [← gen_one, gen_mul_gen, one_mul]

lemma mul_assoc' [H.Normal] (C D E : QGroup H) : (C * D) * E = C * (D * E) := by
  induction C using gen_induction with | h g =>
  induction D using gen_induction with | h g' =>
  induction E using gen_induction with | h g'' =>
  simp [gen_mul_gen, mul_assoc]

instance : Inv (QGroup H) where
  inv C := ⟨C.out⁻¹ • H, ⟨C.out⁻¹, rfl⟩⟩

/-completion of the sorry part-/
lemma gen_inv [H.Normal] (g : G) : (gen H g)⁻¹ = gen H g⁻¹ := by
  apply ext  --ext1
  change ((gen H g).out⁻¹ • H : Set G) = (gen H g⁻¹)
  simp [← gen_def, inv_eq_iff_eq_inv]
  rcases out_eq_gentor_mul g with ⟨h, hh, hout⟩ -- rcases ... with ⟨h, hh, rfl⟩ takes mistakes
  rw[hout]
  use g * h⁻¹ * g⁻¹ -- can refine ⟨_, ?_, simp [mul_assoc]⟩
  constructor
  · exact Subgroup.Normal.conj_mem ‹H.Normal› _ (H.inv_mem hh) g
  · simp [mul_assoc]

lemma inv_mul_cancel' [H.Normal] (C : QGroup H) : C⁻¹ * C = 1 := by
  induction C using gen_induction with | h g =>
  simp [gen_inv, gen_mul_gen]

instance [H.Normal] : Group (QGroup H) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

end QGroup

variable {X Y : Type} [Group X] [Group Y] (f : X →* Y)

/-completion of the sorry part-/
def QGroup.kerToImage : QGroup f.ker →* f.range where
  toFun C := ⟨f C.out, ⟨C.out, rfl⟩⟩
  map_one' := by
    ext1
    simp only [OneMemClass.coe_one]
    have mem : out (1 : QGroup f.ker) ∈ (out (1 : QGroup f.ker) • f.ker : Set X) := by
      rw [Set.mem_smul_set]
      use 1, one_mem _
      simp
    simpa using mem
  map_mul' := by
    intro x y
    ext1
    simp only [Subgroup.coe_mul]
    rw [← f.map_mul]
    suffices ∃ z ∈ f.ker, (x * y).out = (x.out * y.out) *z by
      obtain ⟨z, h, heq⟩ := this
      simp [heq, ← f.mem_ker, h]
    rw [← gen_out x, ← gen_out y, gen_mul_gen, gen_out, gen_out]
    exact out_eq_gentor_mul _
