import Mathlib

-- #check CategoryTheory.IsPullback
-- #check Quotient
-- #check Subtype.mk
-- #check QuotientAddGroup.lift
-- #check AddSubgroup
-- #check AddEquiv.prodComm
-- #check Function.Exact.comp_eq_zero
-- #check AddMonoid.End
-- #check Subset
-- #check Function.surjInv
-- #check Function.Exact
-- #check AddMonoidHom.instNeg
-- #check SnakeLemma.δ
-- #check QuotientAddGroup.mk
-- #check Quotient.exact'
-- #check Quotient.map₂
-- #check Quotient.mk''
-- #check AddOpposite
-- #check AddMonoidHom.snd_comp_prod
-- #check AddMonoidHom.comp_coprod
-- #check DFunLike
-- #check QuotientGroup.lift
-- #check AddEquiv
-- #check AddMonoidHom.toAddEquiv

variable (A B : Type) [AddCommGroup A] [AddCommGroup B]

def AddSubgroup.pullback {B E E' : Type} [AddCommGroup B] [AddCommGroup E] [AddCommGroup E']
    (g : E →+ B) (g' : E' →+ B) : AddSubgroup (E × E') where
  carrier := { (e, e') | g e = g' e'  }
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ (h: g a = g' b) (h': g a' = g' b')
    simp [h, h']
  zero_mem' := by simp
  neg_mem' := by simp

@[simp]
lemma AddSubgroup.mem_pullback {B E E' : Type} [AddCommGroup B] [AddCommGroup E] [AddCommGroup E']
    (g : E →+ B) (g' : E' →+ B) (x : E × E') :
    x ∈ AddSubgroup.pullback g g' ↔ g x.1 = g' x.2 := Iff.rfl

/-pullback is commutative under the two maps-/
def AddSubgroup.pullback_symm {B E E' : Type} [AddCommGroup B] [AddCommGroup E] [AddCommGroup E']
    (g : E →+ B) (g' : E' →+ B) : AddSubgroup.pullback g g' ≃+ AddSubgroup.pullback g' g where
  toFun := AddEquiv.prodComm |>.restrict _ |>.codRestrict _ (by aesop)
  invFun := AddEquiv.prodComm |>.restrict _ |>.codRestrict _ (by aesop)
  left_inv := by rintro ⟨⟨e, e'⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨e', e⟩, _⟩; rfl
  map_add' := by simp

@[simp]
lemma AddSubgroup.pullback_comm_apply {B E E' : Type} [AddCommGroup B]
  [AddCommGroup E] [AddCommGroup E'] (g : E →+ B) (g' : E' →+ B) (x : AddSubgroup.pullback g g') :
    AddSubgroup.pullback_symm g g' x = ⟨⟨x.1.2, x.1.1⟩, x.2.symm⟩ := by rfl

def AddSubgroup.tri_pullback {B E1 E2 E3 : Type}
    [AddCommGroup B] [AddCommGroup E1] [AddCommGroup E2] [AddCommGroup E3]
    (g₁ : E1 →+ B) (g₂ : E2 →+ B) (g₃ : E3 →+ B) : AddSubgroup (E1 × E2 × E3) where
  carrier := { (e₁, e₂, e₃) | g₁ e₁ = g₂ e₂ ∧ g₂ e₂ = g₃ e₃}
  add_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ (h: g₁ a = g₂ b ∧ g₂ b = g₃ c) (h': g₁ a' = g₂ b' ∧ g₂ b' = g₃ c')
    simp [h, h']
  zero_mem' := by simp
  neg_mem' := by simp

@[simp]
lemma AddSubgroup.mem_tri_pullback {B E1 E2 E3 : Type} [AddCommGroup B] [AddCommGroup E1]
[AddCommGroup E2] [AddCommGroup E3] (g₁ : E1 →+ B) (g₂ : E2 →+ B) (g₃ : E3 →+ B)
  (x : E1 × E2 × E3) :
    x ∈ AddSubgroup.tri_pullback g₁ g₂ g₃ ↔ g₁ x.1 = g₂ x.2.1 ∧ g₂ x.2.1 = g₃ x.2.2 := Iff.rfl

structure PreExtension where
  carrier : Type
  [ab : AddCommGroup carrier]
  f : A →+ carrier
  g : carrier →+ B
  injective : Function.Injective f
  surjective : Function.Surjective g
  -- exact : ∀ a : A, g (f a) = 0 --wrong!!!
  exact : Function.Exact f g

-- @[simp]
-- lemma PreExtension.exact2_apply {E : PreExtension A B} :
--     ∀ a : A, E.g (E.f a) = 0 := E.exact.apply_apply_eq_zero

instance : CoeSort (PreExtension A B) Type where
  coe := PreExtension.carrier

instance (E : PreExtension A B) : AddCommGroup E := E.ab

namespace PreExtension

variable {A B}

@[simps f g]
def zero : PreExtension A B where
  carrier := A × B
  ab := inferInstance
  f := AddMonoidHom.inl A B
  g := AddMonoidHom.snd A B
  injective := by rintro a a' h; dsimp at h; rfl --magic rintro empty constructor?
  surjective b := ⟨(0, b), rfl⟩
  exact := by rintro ⟨a, b⟩; simp [eq_comm]

@[simps f g]
def neg (E : PreExtension A B) : PreExtension A B where
  carrier := E
  ab := inferInstance
  f := - E.f
  g := E.g
  injective := by
    intro a a'
    simp only [AddMonoidHom.neg_apply, neg_inj]
    apply E.injective
  surjective := by
    intro b
    obtain ⟨e, he⟩ := E.surjective (-b)
    use -e
    simp [he]
  exact a := by
    simp [E.exact a]
    constructor <;>
    · rintro ⟨a, h⟩
      exact ⟨-a, by simp[h]⟩

/- view E.neg.carrier as E.carrier-/ -- 类型转换！
@[simp]
def negE_toE {E : PreExtension A B} : E.neg →+ E where
  toFun := fun x => x
  map_zero' := rfl
  map_add' := by simp only [implies_true]

@[simps f g]
def add (E E' : PreExtension A B) : PreExtension A B where
  carrier := AddSubgroup.pullback E.g E'.g ⧸
  (AddMonoidHom.prod E.f (-E'.f) |>.range).addSubgroupOf _
  ab := inferInstance
  f :=
  { toFun a := QuotientAddGroup.mk' _ ⟨(E.f a, 0), by simp [(E.exact _).2]⟩
    map_zero' := by
      simpa [AddSubgroup.mem_addSubgroupOf] using ⟨0, by simp, by simp⟩
    map_add' a a' := Quotient.sound <| by simp }
  g := QuotientAddGroup.lift _
    { toFun e := E.g e.1.1  --e.1 is the representation element of e
      map_zero' := by simp
      map_add' :=  by
        rintro ⟨⟨e1, e1'⟩, (h : _ = _)⟩ ⟨⟨e2, e2'⟩, (h' : _ = _)⟩
        simp } <| by
    rintro ⟨⟨e, e'⟩, (h : _ = _)⟩ ⟨x, rfl, rfl⟩
    simp [(E.exact _).2]
  injective := by
    rintro a a' h
    simp only [QuotientAddGroup.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    rw [QuotientAddGroup.eq] at h
    apply_fun E.f using E.injective
    simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk,
      neg_zero, Prod.mk_add_mk, add_zero, AddMonoidHom.mem_range, AddMonoidHom.prod_apply,
      AddMonoidHom.neg_apply, Prod.mk.injEq, neg_eq_zero] at h
    obtain ⟨x, hx, x_eq⟩ := h
    rw [← show E'.f 0 = 0 by simp] at x_eq
    have := E'.injective x_eq
    subst this
    rw [map_zero, neg_add_eq_sub, eq_comm, sub_eq_zero] at hx
    exact hx.symm
  surjective := by
    intro b
    obtain ⟨e, he⟩ := E.surjective b
    obtain ⟨e', he'⟩ := E'.surjective b
    use QuotientAddGroup.mk' _ ⟨(e, e'), by simp [he, he']⟩
    simp [he]
  exact := by /-抄抄-/
    intro a
    induction a using QuotientAddGroup.induction_on with | H a =>
    rcases a with ⟨⟨a, b⟩, ha : E.g a = E'.g b⟩
    simp only [QuotientAddGroup.lift_mk, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, QuotientAddGroup.mk'_apply, Set.mem_range]
    constructor
    · rintro h
      have h' : E'.g b = 0 := by
        rw [← ha]
        exact h
      obtain ⟨a, rfl⟩ := E.exact a |>.1 h
      obtain ⟨a', rfl⟩ := E'.exact b |>.1 h'
      use a + a'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simp only [map_add, AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, neg_add_rev,
        neg_zero, Prod.mk_add_mk, neg_add_cancel_right, zero_add, AddMonoidHom.mem_range,
        AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, Prod.mk.injEq]
      use -a'
      simp
    · rintro ⟨x, hx⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hx
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, neg_zero, Prod.mk_add_mk,
        zero_add, AddMonoidHom.mem_range, AddMonoidHom.prod_apply, AddMonoidHom.neg_apply,
        Prod.mk.injEq] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [map_neg] at ha
      rw [show E'.g (E'.f y) = 0 from congr($(E'.exact.comp_eq_zero) y)] at ha
      simp [ha]

protected def tri_quot_kernel_in_prod (E₁ E₂ E₃ : PreExtension A B) :  --
  AddSubgroup (E₁ × E₂ × E₃) where
    carrier := ({x : E₁ × E₂ × E₃ | ∃ a : A × A × A, a.1 + a.2.1 + a.2.2 = 0 ∧
       x = (E₁.f a.1, E₂.f a.2.1, E₃.f a.2.2)})
    add_mem' := by
      rintro x x' ⟨a, h⟩ ⟨a', h'⟩
      exact ⟨a + a', by nth_rewrite 1 [← add_zero 0, ← h.1, ← h'.1]; simp [h.2, h'.2]; abel⟩
    zero_mem' := ⟨(0, 0, 0), by simp [Prod.zero_eq_mk]⟩
    neg_mem' := by
      rintro x ⟨a, h⟩
      exact ⟨-a, by rw[← neg_zero, ← h.1]; simp [h.2]; abel⟩

def tri_add_midext (E₁ E₂ E₃ : PreExtension A B) : PreExtension A B where
  carrier := AddSubgroup.tri_pullback E₁.g E₂.g E₃.g ⧸
  (PreExtension.tri_quot_kernel_in_prod _ _ _).addSubgroupOf _
  ab := inferInstance
  f := {
    toFun a := QuotientAddGroup.mk' _ ⟨(E₁.f a, 0, 0),
      by simp [E₁.exact.apply_apply_eq_zero], by simp⟩
    map_zero' := by simpa [AddSubgroup.mem_addSubgroupOf] using ⟨0, by simp, by simp⟩
    map_add' a a':= QuotientAddGroup.eq.2 <| ⟨0, by simp; abel⟩
  }
  g := QuotientAddGroup.lift _ {
    toFun e := E₁.g e.1.1
    map_zero' := by simp
    map_add' a a' := by simp
  } <| by
    rintro ⟨x, _⟩ ⟨a,_, ha2 : x = _⟩
    simp [ha2, E₁.exact.apply_apply_eq_zero]
  injective := by
    rintro a a' h
    -- obtain ⟨aaa, ha1, ha2 : - _ + _ = _⟩ := QuotientAddGroup.eq.1 h --closed ????!!!!   ?? 现在又不行了
    obtain ⟨aaa, ha1, ha2⟩ := QuotientAddGroup.eq.1 h
    simp at ha2
    rw [← map_neg, ← map_add, ← map_zero E₂.f,←  map_zero E₃.f] at ha2
    rwa [← E₁.injective ha2.1, ← E₂.injective ha2.2.1, ← E₃.injective ha2.2.2,
      add_zero, add_zero, add_comm, ← sub_eq_add_neg, sub_eq_zero, eq_comm] at ha1
  surjective b := by
    obtain ⟨e₁, he1⟩ := E₁.surjective b
    obtain ⟨e₂, he2⟩ := E₂.surjective b
    obtain ⟨e₃, he3⟩ := E₃.surjective b
    use QuotientAddGroup.mk' _ ⟨(e₁, e₂, e₃), by simp [he1, he2, he3]⟩
    erw [QuotientAddGroup.lift_mk]
    exact he1
  exact := by
    -- rintro ⟨x, hx1, hx2⟩
    intro x --do NOT rintro ⟨x, hx1, hx2⟩
    induction x using QuotientAddGroup.induction_on with | H x =>
    rcases x with ⟨⟨a, b, c⟩, h1 : E₁.g a = E₂.g b, h2 : E₂.g b = E₃.g c⟩
    rw [QuotientAddGroup.lift_mk, Set.mem_range]; simp
    constructor
    · intro ha;
      rw [ha, eq_comm] at h1
      rw [h1, eq_comm] at h2
      obtain ⟨y1, hy1⟩ := (E₁.exact a).1 ha
      obtain ⟨y2, hy2⟩ := (E₂.exact b).1 h1
      obtain ⟨y3, hy3⟩ := (E₃.exact c).1 h2
      use y1 + y2 + y3
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      exact ⟨(-y2 - y3, y2, y3), by simp; abel, by simp[hy1, hy2, hy3]; abel⟩
    · rintro ⟨y, hy⟩
      obtain ⟨aaa, _ , h⟩ := QuotientAddGroup.eq.1 hy
      simp at h
      rw [show a = E₁.f (aaa.1 + y) by rw [map_add, ← h.1];simp]
      exact E₁.exact.apply_apply_eq_zero _

end PreExtension

variable {A B} (E₁ E₂ E₃ E₄ : PreExtension A B)
-- @[ext]
structure PreExtensionHom extends E₁ →+ E₂ where
  comm_f : toAddMonoidHom.comp E₁.f = E₂.f
  comm_g : E₂.g.comp toAddMonoidHom = E₁.g

namespace PreExtensionHom

instance : FunLike (PreExtensionHom E₁ E₂) E₁ E₂ where
  coe h := h.toAddMonoidHom
  coe_injective' := by rintro ⟨⟨⟨h, _⟩, _⟩, _, _⟩ ⟨⟨⟨h, _⟩, _⟩, _, _⟩ rfl; rfl

instance : AddHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where
  map_add h := h.toAddMonoidHom.map_add

instance : ZeroHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where
  map_zero h := h.toAddMonoidHom.map_zero

instance : AddMonoidHomClass (PreExtensionHom E₁ E₂) E₁ E₂ where --完整吗?

@[ext]
lemma ext {h₁ h₂ : PreExtensionHom E₁ E₂} (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ := DFunLike.ext h₁ h₂ H

@[simp]
lemma comm_f_apply (h : PreExtensionHom E₁ E₂) (a : A) :
    h (E₁.f a) = E₂.f a := congr($h.comm_f a)

@[simp]
lemma comm_g_apply (h : PreExtensionHom E₁ E₂) (e : E₁) :
    E₂.g (h e) = E₁.g e := congr($h.comm_g e)

def id (E : PreExtension A B) : PreExtensionHom E E where
  toAddMonoidHom := AddMonoidHom.id E
  comm_f := rfl
  comm_g := rfl

@[simp]
lemma id_apply (x : E₁) : (PreExtensionHom.id E₁) x = x := rfl

@[simps! toAddMonoidHom] --???
def comp {E₁ E₂ E₃ : PreExtension A B}
    (h₁ : PreExtensionHom E₂ E₃) (h₂ : PreExtensionHom E₁ E₂) : PreExtensionHom E₁ E₃ where
  toAddMonoidHom := h₁.toAddMonoidHom.comp h₂.toAddMonoidHom
  comm_f := by rw [AddMonoidHom.comp_assoc, h₂.comm_f, h₁.comm_f]
  comm_g := by rw [← AddMonoidHom.comp_assoc, h₁.comm_g, h₂.comm_g]

@[simp]
lemma comp_apply {E₁ E₂ E₃ : PreExtension A B}
    (h₁ : PreExtensionHom E₂ E₃) (h₂ : PreExtensionHom E₁ E₂) (x : E₁) :
    (h₁.comp h₂) x = h₁ (h₂ x) := rfl

lemma comp_assoc {E₁ E₂ E₃ E₄ : PreExtension A B}
    (h₁ : PreExtensionHom E₃ E₄) (h₂ : PreExtensionHom E₂ E₃) (h₃ : PreExtensionHom E₁ E₂) :
    (h₁.comp h₂).comp h₃ = h₁.comp (h₂.comp h₃) := by
  ext x; simp

@[simp]
lemma comp_id (h : PreExtensionHom E₁ E₂) : h.comp (PreExtensionHom.id E₁) = h := by
  ext x; simp

@[simp]
lemma id_comp (h : PreExtensionHom E₁ E₂) : (PreExtensionHom.id E₂).comp h = h := by
  ext x; simp

noncomputable def inverse {E₁ E₂ : PreExtension A B}
    (h : PreExtensionHom E₁ E₂) (hbij : Function.Bijective h) :
    PreExtensionHom E₂ E₁ := { (AddEquiv.ofBijective h hbij).symm.toAddMonoidHom with
      comm_f := by
        rw [← h.comm_f, AddMonoidHom.ext_iff, ← funext_iff, AddMonoidHom.coe_comp,
           AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_comp_eq]
        ext a; simp [AddEquiv.ofBijective_apply, h.comm_f]
      comm_g := by
        rw [← h.comm_g, AddMonoidHom.ext_iff, ← funext_iff, AddMonoidHom.coe_comp,
           AddEquiv.coe_toAddMonoidHom, AddEquiv.comp_symm_eq]
        ext a; simp [h.comm_g]
    }

@[simp]
lemma inverse_comp_eq {E₁ E₂ : PreExtension A B} (h : PreExtensionHom E₁ E₂)
  (hbij : Function.Bijective h) : ((h.inverse hbij).comp h).toAddMonoidHom= AddMonoidHom.id E₁ := by
  ext x; simp [inverse, AddEquiv.symm_apply_eq]; rfl

@[simp]
lemma inverse_comp_eq_apply {E₁ E₂ : PreExtension A B} (h : PreExtensionHom E₁ E₂)
  (hbij : Function.Bijective h) (x : E₁) : (h.inverse hbij) (h x) = x := by
  change (AddEquiv.ofBijective h hbij).symm (h x) = x
  simp [AddEquiv.symm_apply_eq]

@[simp]
lemma comp_inverse_eq {E₁ E₂ : PreExtension A B} (h : PreExtensionHom E₁ E₂)
  (hbij : Function.Bijective h) : (h.comp (h.inverse hbij)).toAddMonoidHom= AddMonoidHom.id E₂ := by
  rw [inverse, AddMonoidHom.ext_iff, ← funext_iff]
  ext x; simp; change h ((AddEquiv.ofBijective _ _).symm  x) = x
  erw [AddEquiv.ofBijective_apply_symm_apply]

@[simp]
lemma comp_inverse_eq_apply {E₁ E₂ : PreExtension A B} (h : PreExtensionHom E₁ E₂)
  (hbij : Function.Bijective h) (x : E₂) : h (h.inverse hbij x) = x := by
  erw [inverse, AddEquiv.ofBijective_apply_symm_apply]
  exact hbij

variable {E₁ E₂ E₃ E₄} in
@[simps toAddMonoidHom]
def add (h₁ : PreExtensionHom E₁ E₂) (h₂ : PreExtensionHom E₃ E₄) :
    PreExtensionHom (.add E₁ E₃) (.add E₂ E₄) where
  toAddMonoidHom :=
    QuotientAddGroup.map _ _ (AddMonoidHom.prodMap h₁ h₂ |>.restrict _ |>.codRestrict _ (by
      rintro ⟨⟨e, e'⟩, h⟩
      simp only [AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe,
        Prod.map_apply, AddSubgroup.mem_pullback, comm_g_apply]
      exact h)) <| by
      rintro ⟨⟨e, e'⟩, (h : _ = _)⟩ ⟨x, rfl, rfl⟩
      simp only [AddMonoidHom.neg_apply, AddSubgroup.mem_comap, AddMonoidHom.codRestrict_apply,
        AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe, Prod.map_apply,
        comm_f_apply, map_neg, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range,
        AddMonoidHom.prod_apply, Prod.mk.injEq, neg_inj]
      use x
  comm_f := by ext x; refine QuotientAddGroup.eq.2 ?_; simp
  comm_g := by
    ext x
    obtain ⟨⟨⟨e, e'⟩, (hx : _ = _)⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    -- refine QuotientAddGroup.eq.1 ?_
    simp only [PreExtension.add_g, QuotientAddGroup.mk'_apply, AddMonoidHom.coe_comp,
      Function.comp_apply]
    -- refine QuotientAddGroup.mk'_eq_mk'.1 ?_
    erw [QuotientAddGroup.map_mk', AddMonoidHom.codRestrict_apply]
    simp only [AddMonoidHom.restrict_apply, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_coe,
      Prod.map_apply]
    erw [QuotientAddGroup.lift_mk']
    change E₂.g (h₁ _) = E₁.g e
    rw [h₁.comm_g_apply]

@[simp]
lemma add_apply {h₁ : PreExtensionHom E₁ E₂} {h₂ : PreExtensionHom E₃ E₄} (x : E₁ × E₃) (hx) :
    (h₁.add h₂) ⟦⟨x, hx⟩⟧= ⟦⟨(h₁ x.1, h₂ x.2), (by simpa)⟩⟧ := rfl

variable {E₂' : PreExtension A B} in
lemma comp_add
    (h₁ : PreExtensionHom E₁ E₂)
    (h₁' : PreExtensionHom E₂ E₂')
    (h₂ : PreExtensionHom E₃ E₄) :
    (h₁'.comp h₁).add h₂ =
    (h₁'.add h₂).comp (h₁.add (.id _)) := by
  ext ⟨a, b⟩
  rfl

variable {E₁' E₂' E₃' : PreExtension A B} in
lemma add_comp_add
    (h₁ : PreExtensionHom E₁ E₂)
    (h₁' : PreExtensionHom E₁' E₂')
    (h₂ : PreExtensionHom E₂ E₃)
    (h₂' : PreExtensionHom E₂' E₃') :
    (h₂.add h₂').comp (h₁.add h₁') =
    (h₂.comp h₁).add (h₂'.comp h₁') := by
  ext ⟨a, b⟩
  simp
  rfl

@[simp]
lemma id_add_id (E₁ E₂ : PreExtension A B) :
    (PreExtensionHom.id E₁).add (PreExtensionHom.id E₂) = PreExtensionHom.id (E₁.add E₂) := by
  ext ⟨a, b⟩; simp; rfl

variable {E₁ E₂ E} in
@[simps toAddMonoidHom]
def neg (h : PreExtensionHom E₁ E₂) : PreExtensionHom E₁.neg E₂.neg where
  toAddMonoidHom := h.toAddMonoidHom
  comm_f := by simp [h.comm_f]
  comm_g := by simp [h.comm_g]

@[simp]
lemma neg_apply (h : PreExtensionHom E₁ E₂) (x : E₁) :
  h.neg x = h x := rfl

lemma neg_comp (h₁ : PreExtensionHom E₁ E₂) (h₂ : PreExtensionHom E₂ E₃) :
    h₂.neg.comp h₁.neg = (h₂.comp h₁).neg := by
  ext x; simp

end PreExtensionHom

structure PreExtensionIso where
  hom : PreExtensionHom E₁ E₂
  inv : PreExtensionHom E₂ E₁
  hom_inv_id : hom.comp inv = .id _
  inv_hom_id : inv.comp hom = .id _

namespace PreExtensionIso

def refl (E : PreExtension A B) : PreExtensionIso E E where
  hom := PreExtensionHom.id E
  inv := PreExtensionHom.id E
  hom_inv_id := rfl
  inv_hom_id := rfl

variable {E₁ E₂ E₃}
def symm (h : PreExtensionIso E₁ E₂) : PreExtensionIso E₂ E₁ where
  hom := h.inv
  inv := h.hom
  hom_inv_id := h.inv_hom_id
  inv_hom_id := h.hom_inv_id

def trans (h₁ : PreExtensionIso E₁ E₂) (h₂ : PreExtensionIso E₂ E₃) : PreExtensionIso E₁ E₃ where
  hom := PreExtensionHom.comp h₂.hom h₁.hom
  inv := PreExtensionHom.comp h₁.inv h₂.inv
  hom_inv_id := by
    rw [← PreExtensionHom.comp_assoc, PreExtensionHom.comp_assoc _ _ h₁.inv, h₁.hom_inv_id,
      PreExtensionHom.comp_id, h₂.hom_inv_id]
  inv_hom_id := by
    rw [← PreExtensionHom.comp_assoc, PreExtensionHom.comp_assoc _ _ h₂.hom, h₂.inv_hom_id,
      PreExtensionHom.comp_id, h₁.inv_hom_id]

noncomputable def ofBijective {E E' : PreExtension A B} (h : PreExtensionHom E E')
  (hbij : Function.Bijective h) : PreExtensionIso E E' where
    hom := h
    inv := PreExtensionHom.inverse h hbij
    hom_inv_id := by ext e; simp
    inv_hom_id := by ext e; simp

def addZero (E : PreExtension A B) :
    PreExtensionIso E (E.add .zero) where
  hom :=
  { toFun e := QuotientAddGroup.mk' _ ⟨(e, 0, E.g e), by simp; rfl⟩
    map_zero' := by simp only [map_zero]; rfl
    map_add' := by
      intro e e'
      simp only [PreExtension.zero_g, PreExtension.zero_f, map_add, QuotientAddGroup.mk'_apply]
      refine QuotientAddGroup.eq.2 ?_
      simp [AddSubgroup.mem_addSubgroupOf]
      refine ⟨0, by simp only [map_zero]; abel, Prod.ext ?_ ?_⟩

      · simp only [map_zero, Prod.fst_zero]
        change (0 : A) = -0 + (0 + 0)
        simp
      · simp only [map_zero, Prod.snd_zero]
        change 0 = -(_ + _) + (_ + _)
        abel
    comm_f := by
      ext a
      simp only [PreExtension.zero_g, PreExtension.zero_f, QuotientAddGroup.mk'_apply,
        AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
        PreExtension.add_f]
      erw [QuotientAddGroup.eq]
      simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, NegMemClass.coe_neg,
        Prod.neg_mk, Prod.mk_add_mk, neg_add_cancel, add_zero, AddMonoidHom.mem_range,
        AddMonoidHom.prod_apply, Prod.mk.injEq]
      use 0
      simp only [map_zero, E.exact.apply_apply_eq_zero, zero_eq_neg, true_and]
      rfl
    comm_g := by rfl }
  inv :=  --- the original defination is wrong!!!
  { toAddMonoidHom := QuotientAddGroup.lift _ (((AddMonoidHom.fst E.carrier _) +
      (E.f.comp ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd E.carrier _)))
      ).comp (AddSubgroup.subtype _))
      (by
        rintro ⟨⟨e, a, b⟩, ⟨⟩⟩ h
        simp only [PreExtension.zero_g, PreExtension.zero_f, ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range,
          AddMonoidHom.prod_apply, Prod.mk.injEq] at h
        obtain ⟨x, rfl, hx⟩ := h
        erw [E.exact.apply_apply_eq_zero, Prod.ext_iff,
           AddMonoidHom.neg_apply, AddMonoidHom.inl_apply] at hx
        simp only [Prod.neg_mk, neg_zero, and_true] at hx
        subst hx
        simp only [PreExtension.zero_g, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
          AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
          E.exact.apply_apply_eq_zero]
        change E.f x + E.f (-x) = 0
        rw [map_neg, add_neg_cancel])
    comm_f := by
      ext a
      simp only [PreExtension.zero_g, PreExtension.zero_f, PreExtension.add_f,
        QuotientAddGroup.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        PreExtension.add_f]
      erw [QuotientAddGroup.lift_mk]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply,
        AddMonoidHom.coe_fst, AddMonoidHom.coe_snd]
      change E.f a + E.f 0 = E.f a --good change!  change神
      rw [map_zero, add_zero]
    comm_g := by
      ext x
      induction x using QuotientAddGroup.induction_on with | H x =>
      rcases x with ⟨⟨e, a, _⟩, _⟩
      dsimp [PreExtension.zero_g, PreExtension.zero_f, PreExtension.add_g,
         AddMonoidHom.coe_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change E.g (e + E.f a) = E.g e
      rw [map_add, E.exact.apply_apply_eq_zero, add_zero]
  }
  hom_inv_id := by
      ext x
      induction x using QuotientAddGroup.induction_on with | H x =>
      rcases x with ⟨⟨e, a, b⟩, he : E.g e = b⟩ -- nice expression
      erw [QuotientAddGroup.eq]
      simp only [PreExtension.zero_g, PreExtension.zero_f, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, Prod.mk_add_mk,
        AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]
      refine ⟨-a, ?_,  ?_⟩
      · change E.f (-a) = -(e + E.f a) + e
        rw [map_neg, neg_add_rev, neg_add_cancel_right]
      · change -(-a, 0) = -(0, E.g (e + E.f a)) + (a, b)
        simp [(E.exact _).2, he]
  inv_hom_id := by
      ext e
      change e + E.f 0 = e
      rw [map_zero, add_zero]

def addComm_mapis (E E' : PreExtension A B) : PreExtensionHom (E.add E') (E'.add E) :={
  toFun := QuotientAddGroup.map _ _ (AddSubgroup.pullback_symm E.g E'.g) <| by
    rintro ⟨⟨e, e'⟩, hmem⟩ ⟨a, rfl, rfl⟩
    simp [AddSubgroup.mem_addSubgroupOf]
    exact ⟨-a, map_neg _ _, by simp⟩
  map_zero' := rfl
  map_add' := by simp
  comm_f := by ext a; apply QuotientAddGroup.eq.2; exact ⟨a, by simp⟩
  comm_g := by
    ext ⟨⟨e, e'⟩, h⟩
    simp; erw [QuotientAddGroup.lift_mk']
    -- change E'.g e' = E.g e
    exact h.symm}

def addComm_comp_addComm_eq_id (E E' : PreExtension A B) :
    (addComm_mapis E E').comp (addComm_mapis E' E) = PreExtensionHom.id (E'.add E) := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H x =>
  rcases x with ⟨⟨e, e'⟩, hmem⟩
  simp only [PreExtensionHom.comp_apply, PreExtensionHom.id_apply]
  exact QuotientAddGroup.eq.2 ⟨0, by simp⟩

def addComm (E E' : PreExtension A B) :
    PreExtensionIso (E.add E') (E'.add E) where
      hom := addComm_mapis _ _
      inv := addComm_mapis _ _
      hom_inv_id := addComm_comp_addComm_eq_id _ _
      inv_hom_id := addComm_comp_addComm_eq_id _ _

def zeroAdd (E : PreExtension A B) :
    PreExtensionIso E (PreExtension.zero.add E) :=
    PreExtensionIso.trans (addZero _) (addComm _ _)

-- set_option pp.all true
-- set_option pp.proofs true
@[simp]
noncomputable def section_ofNegAdd (E : PreExtension A B) :
    AddMonoidHom B (E.neg.add E) where
      toFun b :=
        QuotientAddGroup.mk <| (fun e ↦ ⟨(e, e), rfl⟩) <| (Function.surjInv E.surjective b)
      map_zero' := by
        obtain ⟨a, ha⟩ := (E.exact <| Function.surjInv E.surjective <| 0).1
          (0 |> Function.surjInv_eq E.surjective); rw[← ha]
        refine QuotientAddGroup.eq.2 ⟨a, by simp; exact AddMonoidHom.neg_apply E.f a⟩
      map_add' := by

        rintro b1 b2
        apply QuotientAddGroup.eq.2
        let diff := - (b1 + b2 |> Function.surjInv E.surjective) +
          ((b1 |> Function.surjInv E.surjective) + (b2 |> Function.surjInv E.surjective))
        have : E.g diff = 0 := by
          rw [AddMonoidHom.map_add E.g, AddMonoidHom.map_add E.g, map_neg,
            Function.surjInv_eq E.surjective, Function.surjInv_eq E.surjective,
            Function.surjInv_eq E.surjective]
          abel
        simp only [PreExtension.neg_g, PreExtension.neg_f, AddSubgroup.mem_addSubgroupOf,
          AddSubgroup.coe_add, NegMemClass.coe_neg, Prod.neg_mk, Prod.mk_add_mk,
          AddMonoidHom.mem_range, AddMonoidHom.prod_apply, Prod.mk.injEq]  ---??? "and_self" fails!
        -- simp_rw [and_self_iff]
        obtain ⟨a, ha⟩ := (E.exact diff).1 this
        refine ⟨-a, ?_, ?_⟩ <;>
        · erw [map_neg,AddMonoidHom.neg_apply,neg_neg, ha]

@[simp]
lemma Comp_section_OfNegAdd_eq_id (E : PreExtension A B) : --section is the right inverse.
    (E.neg.add E).g.comp (section_ofNegAdd E) = (AddMonoidHom.id B) := by
  ext x
  simp only [PreExtension.add_g, PreExtension.neg_g, PreExtension.neg_f, section_ofNegAdd,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
    AddMonoidHom.id_apply]
  erw [QuotientAddGroup.lift_mk, Function.surjInv_eq E.surjective]

@[simp]
lemma comp_section_ofNegAdd_eq_id_apply {E : PreExtension A B} (b : B) :
  (E.neg.add E).g.comp (section_ofNegAdd E) b = b := by
  rw [Comp_section_OfNegAdd_eq_id, AddMonoidHom.id_apply]


@[simp]
def NegAdd_toE {E : PreExtension A B} : (E.neg.add E) →+ E :=
  QuotientAddGroup.lift _ ({
  toFun :=(fun x ↦ x.1.2 - (PreExtension.negE_toE x.1.1)) /-头大的类型转换-/
  map_zero' := by simp
  map_add' := by
    rintro x y
    -- induction x, y using Quotient.inductionOn₂ with | h a b =>
    rw [AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add, map_add, PreExtension.negE_toE]
    abel
  })  <| by
    rintro ⟨x, _⟩ ⟨a, rfl⟩
    change - E.f a - ( - E.f a) = 0
    simp only [sub_self]


def NegAdd_toSelf {E : PreExtension A B} : (E.neg.add E) →+ E.neg.add E :=
    (QuotientAddGroup.mk' _).comp <| AddMonoidHom.codRestrict
     (AddMonoidHom.prod (-NegAdd_toE) (0 : AddMonoidHom _ E)) _ <| by
    rintro ⟨⟨e, e'⟩, h : E.g e = E.g e'⟩
    rw [NegAdd_toE]
    change E.g (- (QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk' _ _))) = E.g 0
    erw [QuotientAddGroup.lift_mk
      ((E.neg.f.prod (-E.f)).range.addSubgroupOf (AddSubgroup.pullback E.neg.g E.g))]
    simp [h]

variable (E : PreExtension A B) (x : AddSubgroup.pullback E.neg.g E.g)

@[simp]
def choose_cond {E : PreExtension A B} (x : E.neg.add E) :
  ∃ y, E.f y = NegAdd_toE x :=
  Set.mem_range.1 <| (E.exact (NegAdd_toE x)).1 (by
    induction x using Quotient.inductionOn with | h x =>
    -- change E.g (NegAdd_toSelf.toFun _) = 0
    erw [QuotientAddGroup.lift_mk
      ((E.neg.f.prod (-E.f)).range.addSubgroupOf (AddSubgroup.pullback E.neg.g E.g))] --urgly
    simp [PreExtension.neg_g, sub_eq_zero] at ⊢
    change E.g x.1.2 = E.g x.1.1
    exact x.2.symm)


@[simp]
noncomputable def retraction_ofNegAdd (E : PreExtension A B) :
    AddMonoidHom (E.neg.add E) A where
    toFun := fun x => Classical.choose <| choose_cond x
    map_zero' := by
      apply E.injective
      rw [Classical.choose_spec (choose_cond 0), map_zero, map_zero]
    map_add' := by
      rintro x y
      apply E.injective
      let chspec := fun (e : E.neg.add E) => Classical.choose_spec (choose_cond e)
      rw[map_add E.f, chspec _, chspec x, chspec y, map_add]
              --repeat rw fails! chspec _ chspec_ fails!
@[simp]
lemma FComp_retraction_ofNegAdd_eq_NegDiff_apply {E : PreExtension A B} (x : E.neg.add E) :
  E.f ((retraction_ofNegAdd E) x) = NegAdd_toE x := by
  induction x using Quotient.inductionOn with | h x =>
  erw [Classical.choose_spec (choose_cond _)]

@[simp]
lemma FComp_retraction_ofNegAdd_eq_NegDiff (E : PreExtension A B) :
  E.f.comp (retraction_ofNegAdd E) = NegAdd_toE :=
  AddMonoidHom.ext FComp_retraction_ofNegAdd_eq_NegDiff_apply

lemma Comp_retraction_ofNegAdd_apply {E : PreExtension A B} (x : E.neg.add E) :
  (E.neg.add E).f.comp (retraction_ofNegAdd E) x = NegAdd_toSelf x := by
  -- induction x using Quotient.inductionOn with | h x =>
  apply QuotientAddGroup.eq.2
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
  change - ( _ , 0) + ( _, 0) ∈ _
  use 0
  rw [map_zero, Prod.mk_add_mk, add_zero]
  change 0 = (-(-E.f _) + _ , -0)
  rw [neg_zero, FComp_retraction_ofNegAdd_eq_NegDiff_apply x, AddMonoidHom.neg_apply,
    neg_neg, add_neg_cancel]
  rfl
      ---why rw fails to close the goal?

@[simp]
lemma retraction_ofNegAdd_comp_eq_id (E : PreExtension A B) :
  (retraction_ofNegAdd E).comp (E.neg.add E).f = (AddMonoidHom.id A):= by
  ext a
  apply E.injective
  simp only  [retraction_ofNegAdd, AddMonoidHom.id_apply]
  erw [Classical.choose_spec (choose_cond _), QuotientAddGroup.lift_mk]
  change 0 - (- E.f a) = E.f a
  simp only [sub_neg_eq_add, zero_add]

@[simp]
lemma retraction_ofNegAdd_comp_eq_id_apply {E : PreExtension A B} (a : A) :
  (retraction_ofNegAdd E).comp (E.neg.add E).f a = a := by
  rw [retraction_ofNegAdd_comp_eq_id, AddMonoidHom.id_apply]

@[simp]
lemma retraction_comp_section_ofNegAdd_eqZero_apply {E : PreExtension A B} (b : B) :
  (retraction_ofNegAdd E).comp (section_ofNegAdd E) b = 0 := by
  have : NegAdd_toE (section_ofNegAdd E b) = 0 := by
    erw [QuotientAddGroup.lift_mk]
    simp
  apply E.injective
  erw [retraction_ofNegAdd, AddMonoidHom.comp_apply,
    Classical.choose_spec (choose_cond _), this, map_zero]

@[simp]
lemma retraction_comp_section_ofNegAdd_eqZero (E : PreExtension A B) :
  (retraction_ofNegAdd E).comp (section_ofNegAdd E) = 0 :=
  AddMonoidHom.ext retraction_comp_section_ofNegAdd_eqZero_apply


noncomputable def negAddCancel (E : PreExtension A B) :
    PreExtensionIso (E.neg.add E) PreExtension.zero where
    hom := {
      AddMonoidHom.prod (retraction_ofNegAdd E) (E.neg.add E).g with
      -- map_zero' := by simp only [retraction_ofNegAdd, NegAdd_toSelf, PreExtension.neg_g,
      --   PreExtension.neg_f, PreExtension.negE_toE, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      --   PreExtension.add_g, map_zero]
      -- -- map_zero' := by simp -----???fails???
      -- map_add' := by
      --   intro x y
      --   rw [map_add]
      comm_f := by
        ext x
        erw [Prod.mk.injEq]
        refine ⟨retraction_ofNegAdd_comp_eq_id_apply x, (E.neg.add E).exact.apply_apply_eq_zero x⟩
      comm_g := AddMonoidHom.snd_comp_prod _ _
    }
    inv  := {
      AddMonoidHom.coprod (E.neg.add E).f (section_ofNegAdd E) with
      comm_f := AddMonoidHom.coprod_comp_inl _ _
      comm_g := by
        ext ⟨a, b⟩
        erw [AddMonoidHom.comp_apply, AddMonoidHom.coprod_apply, map_add,
         (E.neg.add E).exact.apply_apply_eq_zero, zero_add, comp_section_ofNegAdd_eq_id_apply,
         PreExtension.zero_g, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    }
    hom_inv_id := by
      ext ⟨a, b⟩
      change AddMonoidHom.prod _ _ (AddMonoidHom.coprod _ _ <| _ ) = (a, b)
      erw [AddMonoidHom.coprod_apply, AddMonoidHom.prod_apply, map_add, map_add,
        retraction_ofNegAdd_comp_eq_id_apply a, comp_section_ofNegAdd_eq_id_apply b,
        (E.neg.add E).exact.apply_apply_eq_zero, retraction_comp_section_ofNegAdd_eqZero_apply,
        add_zero, zero_add]
    inv_hom_id := by
      ext x
      induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨⟨e : E , e'⟩, he : E.g e = E.g e'⟩
      apply QuotientAddGroup.eq.2
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.coe_fst,
         AddMonoidHom.coe_snd, AddMemClass.mk_add_mk]
      change -((E.neg.f (retraction_ofNegAdd E _), 0) + (Function.surjInv _ <| (E.neg.add E).g _,
         Function.surjInv _ <| (E.neg.add E).g _)) + _ ∈ _
      set t1 := E.neg.f (retraction_ofNegAdd E _) with h1
      set t2 := (Function.surjInv _ <| (E.neg.add E).g _ : E) with h2
      have h1 : t1 = e - e' := by
        change t1 = - (E.f _) at h1
        rw [h1, FComp_retraction_ofNegAdd_eq_NegDiff_apply, NegAdd_toE]
        erw [QuotientAddGroup.lift_mk]
        simp only [PreExtension.negE_toE, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_sub]
      have h2 : E.g t2 = E.g e := by
        rw [h2, Function.surjInv_eq E.surjective ((E.neg.add E).g _), PreExtension.add_g]
        exact QuotientAddGroup.lift_mk _ _ _
      simp only [PreExtension.neg_f, h1, Prod.mk_add_mk, zero_add, Prod.neg_mk, neg_add_rev,
        neg_sub, add_assoc, sub_add_cancel, AddMonoidHom.mem_range, AddMonoidHom.prod_apply,
        AddMonoidHom.neg_apply, Prod.mk.injEq]
      change ∃ x, -E.f x = _ ∧ _     -- exists_congr ?
      simp only [neg_eq_iff_eq_neg, neg_add, neg_neg]
      obtain ⟨a, ha⟩ := (E.exact (t2 + -e')).1
        (by rw [map_add, map_neg, h2, he, add_comm, neg_add_cancel])
      exact ⟨a, ⟨ha, ha⟩⟩
    /-终于终于！-/

def Tri_pullback_to_triadd {E₁ E₂ E₃ : PreExtension A B} :
  (AddSubgroup.tri_pullback E₁.g E₂.g E₃.g) →+ AddSubgroup.pullback E₁.g (E₂.add E₃).g := {
    toFun x := ⟨(x.1.1, QuotientAddGroup.mk' _ ⟨x.1.2,x.2.2⟩), by
      simp only [PreExtension.add_g, AddSubgroup.mem_pullback, ]
      erw [QuotientAddGroup.lift_mk'
        ((E₂.f.prod (-E₃.f)).range.addSubgroupOf (AddSubgroup.pullback E₂.g E₃.g))]
      exact x.2.1⟩
    map_zero' := rfl
    map_add' x1 x2 := rfl
  }

def midext_to_tri_add {E₁ E₂ E₃ : PreExtension A B} :
  PreExtensionHom (PreExtension.tri_add_midext E₁ E₂ E₃) (E₁.add (E₂.add E₃)) := {
  __ := QuotientAddGroup.map _ _ Tri_pullback_to_triadd <| by
    rintro ⟨x, _⟩ ⟨a, hasum, rfl : x = _⟩
    simp only [PreExtension.add_g, PreExtension.add_f, QuotientAddGroup.mk'_apply,
      AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range,
      Tri_pullback_to_triadd]
    use a.1
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Prod.mk.injEq, true_and]
    apply QuotientAddGroup.eq.2
    simp [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    exact ⟨-a.2.2,
      by simp; rw[neg_eq_iff_add_eq_zero, ← map_zero E₂.f, ← hasum, map_add, map_add]; abel⟩
  comm_f := by ext a; rfl
  comm_g := by
    ext x
    induction x using QuotientAddGroup.induction_on with | H x =>
      simp only [PreExtension.tri_add_midext, QuotientAddGroup.mk'_apply, PreExtension.add_g,
        PreExtension.add_f, AddMonoidHom.coe_comp, Function.comp_apply,
        QuotientAddGroup.lift_mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      erw [QuotientAddGroup.map_mk, QuotientAddGroup.lift_mk]
}

noncomputable
def midext123_eq_add123 {E₁ E₂ E₃ : PreExtension A B} :
  PreExtensionIso (PreExtension.tri_add_midext E₁ E₂ E₃) (E₁.add (E₂.add E₃)) := by
    refine ofBijective midext_to_tri_add ⟨?_, ?_⟩
    · intro x y h
      induction x, y using Quotient.inductionOn₂ with | h x y =>
      rcases x, y with ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩
      apply QuotientAddGroup.eq.2
      apply QuotientAddGroup.eq.1 at h
      simp [Tri_pullback_to_triadd, AddSubgroup.mem_addSubgroupOf,
        PreExtension.tri_quot_kernel_in_prod] at h ⊢
      obtain ⟨a, ha1, ha2⟩ := h
      rw [← QuotientAddGroup.mk_neg, ← QuotientAddGroup.mk_add] at ha2
      apply QuotientAddGroup.eq.1 at ha2
      obtain ⟨b, hb⟩ := ha2
      simp only [AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, neg_neg,
        AddSubgroup.subtype_apply, AddSubgroup.coe_add, NegMemClass.coe_neg] at hb
      rw [Eq.comm, add_comm] at hb
      apply eq_sub_of_add_eq at hb
      simp only [Prod.mk_sub_mk, sub_zero] at hb
      use a; use b - a; use -b
      simp [← hb, ha1, ← Prod.mk_add_mk, ← Prod.neg_mk]
    · intro y
      induction y using Quotient.inductionOn with | h y =>
      rcases y with ⟨⟨e1, e23⟩, h1 : _ = _⟩
      induction e23 using Quotient.inductionOn with | h e23 =>
      rcases e23 with ⟨⟨e2, e3⟩, h23 : _ = _⟩
      erw [PreExtension.add_g, QuotientAddGroup.lift_mk
        ((E₂.f.prod (-E₃.f)).range.addSubgroupOf (AddSubgroup.pullback E₂.g E₃.g))] at h1
      change _ = E₂.g e2 at h1
      use QuotientAddGroup.mk ⟨(e1, e2, e3), ⟨h1, h23⟩⟩
      apply QuotientAddGroup.eq.2
      simp [Tri_pullback_to_triadd]

noncomputable
def midext312_eq_add12_3 {E1 E2 E3 : PreExtension A B} :
  PreExtensionIso (PreExtension.tri_add_midext E3 E1 E2) ((E1.add E2).add E3) :=
    trans midext123_eq_add123 (addComm E3 (E1.add E2))

def midext312_to_midext123 {E1 E2 E3 : PreExtension A B} : PreExtensionHom
    (PreExtension.tri_add_midext E3 E1 E2) (PreExtension.tri_add_midext E1 E2 E3) where
    __ := QuotientAddGroup.map _ _
      ((AddEquiv.trans AddEquiv.prodComm AddEquiv.prodAssoc).toAddMonoidHom
        |>.restrict _ |>.codRestrict _ (by
        rintro ⟨x, hx : _ ∧ _ ⟩
        exact ⟨hx.2, (Eq.trans hx.1 hx.2).symm⟩)) <| by
      intro ⟨x, _⟩ ⟨a, hasum, (hx : x = _)⟩
      simp [AddSubgroup.mem_addSubgroupOf, PreExtension.tri_quot_kernel_in_prod]
      use a.2.1; use a.2.2; use a.1
      simp [← hasum, hx]
      abel
    comm_f := by
      ext a
      simp[PreExtension.tri_add_midext, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      exact ⟨(a, 0 , -a), by simp, by simp⟩
    comm_g := by
      ext x
      induction x using QuotientAddGroup.induction_on with | H x =>
      rcases x with ⟨⟨e3, e1, e2⟩, h1, h2⟩
      simp only [PreExtension.tri_add_midext, QuotientAddGroup.mk'_apply, AddMonoidHom.coe_comp,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, QuotientAddGroup.map_mk,
        QuotientAddGroup.lift_mk, AddMonoidHom.codRestrict_apply, AddMonoidHom.restrict_apply,
        AddEquiv.toAddMonoidHom_eq_coe]
      simp only [AddEquiv.coe_addMonoidHom_trans, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
        AddEquiv.coe_prodAssoc, AddEquiv.coe_prodComm, Function.comp_apply, Prod.swap_prod_mk,
        Equiv.prodAssoc_apply]
      exact h1.symm

def midext123_eq_midext312 {E1 E2 E3 : PreExtension A B} : PreExtensionIso
  (PreExtension.tri_add_midext E1 E2 E3) (PreExtension.tri_add_midext E3 E1 E2) where
    hom := midext312_to_midext123.comp midext312_to_midext123
    inv := midext312_to_midext123
    hom_inv_id := by
      ext x
      induction x using QuotientAddGroup.induction_on with | H x =>
      rcases x with ⟨⟨e1, e2, e3⟩, h1, h2⟩
      simp [midext312_to_midext123]
      rfl
    inv_hom_id := by
      ext x
      induction x using QuotientAddGroup.induction_on with | H x =>
      simp [midext312_to_midext123]
      rfl

noncomputable
def addAssoc (E1 E2 E3 : PreExtension A B) :
    PreExtensionIso ((E1.add E2).add E3) (E1.add (E2.add E3)) :=
    midext312_eq_add12_3.symm |>.trans midext123_eq_midext312.symm |>.trans midext123_eq_add123

-- def addAssoc (E1 E2 E3 : PreExtension A B) : -- TODO (immediate definition??)
--     PreExtensionIso (E1.add (E2.add E3)) ((E1.add E2).add E3) where
--   hom :=
--   { toFun := QuotientAddGroup.map _ _ (
--      by sorry
--   )
--     map_zero' := rfl
--     map_add' _ _ := rfl
--     comm_f := rfl
--     comm_g := by ext ⟨a, b, c⟩; exact add_assoc _ _ _ }
--   inv :=
--   { toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
--     map_zero' := rfl
--     map_add' _ _ := rfl
--     comm_f := rfl
--     comm_g := by ext ⟨⟨a, b⟩, c⟩; exact (add_assoc _ _ _).symm }
--   hom_inv_id := rfl
--   inv_hom_id := rfl

end PreExtensionIso

variable (A B) in
abbrev Extension :=  Quotient (α := PreExtension A B)
  { r E₁ E₂ := Nonempty (PreExtensionIso E₁ E₂)
    iseqv :=
    { refl E := ⟨PreExtensionIso.refl E⟩
      symm := Nonempty.map PreExtensionIso.symm
      trans := by intro _ _ _ ⟨e⟩ ⟨e'⟩; exact ⟨e.trans e'⟩ } }

instance : Zero (Extension A B) where
  zero := Quotient.mk'' .zero

instance : Add (Extension A B) where
  add := Quotient.map₂ PreExtension.add <| by
    rintro E E' ⟨e⟩ F F' ⟨f⟩
    refine ⟨⟨.add e.hom f.hom, .add e.inv f.inv, ?_, ?_⟩⟩
    · rw [PreExtensionHom.add_comp_add, e.hom_inv_id, f.hom_inv_id, PreExtensionHom.id_add_id]
    · rw [PreExtensionHom.add_comp_add, e.inv_hom_id, f.inv_hom_id, PreExtensionHom.id_add_id]

instance : Neg (Extension A B) where
  neg := Quotient.map PreExtension.neg <| by
    rintro E E' ⟨e⟩
    refine ⟨⟨e.hom.neg, e.inv.neg, ?_, ?_⟩⟩
    · rw [PreExtensionHom.neg_comp, e.hom_inv_id]; rfl
    · rw [PreExtensionHom.neg_comp, e.inv_hom_id]; rfl

instance : AddCommGroup (Extension A B) where
  add_assoc E₁ E₂ E₃ := Quotient.inductionOn₃ E₁ E₂ E₃ <| fun E₁ E₂ E₃ =>
    Quotient.sound ⟨PreExtensionIso.addAssoc _ _ _⟩
  zero_add E := E.induction_on <| fun E =>Quotient.sound ⟨(PreExtensionIso.zeroAdd E).symm⟩
  add_zero E := E.induction_on <| fun E =>Quotient.sound ⟨(PreExtensionIso.addZero E).symm⟩
  nsmul := nsmulRec
  neg := _
  -- sub_eq_add_neg := sub_eq_add_negRec
  zsmul := zsmulRec
  neg_add_cancel E := Quotient.inductionOn E <| fun E =>
    Quotient.sound (⟨PreExtensionIso.negAddCancel E⟩ : Nonempty _)
  add_comm E E':= Quotient.inductionOn₂ E E' <| fun E E' =>
    Quotient.sound ⟨PreExtensionIso.addComm E E'⟩
