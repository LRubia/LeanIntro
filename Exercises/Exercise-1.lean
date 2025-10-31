import Mathlib
import CodeForLeanBook.PartOne.ChapterTwo.Example
--------自测-----------------------
example (P : Prop) : (P → ¬ ¬ P) := by
  intro p np
  apply np p
--------定义整数-------------------
inductive Integer : Type where
  | nonneg : Nat → Integer --n → n
  | neg : Nat → Integer --n → - (n + 1)

-- def Integer.add (x y : Integer) : Integer :=
--   match x, y with
def Integer.add
  | nonneg m, nonneg n => nonneg (m + n)
  | neg m,    neg n    => neg (m + n + 1)
  | nonneg m, neg n    => if m > n then nonneg (m - n - 1) else neg (n - m)
  | neg m,    nonneg n => if n > m then nonneg (n - m - 1) else neg (m - n)

def Integer.multiply
  | nonneg m, nonneg n => nonneg (m * n )
  | neg m,    neg n    => nonneg (m * n)
  | nonneg m, neg n    => if m = 0 then nonneg 0 else neg (m * n + m - 1)
  | neg m,    nonneg n => if n = 0 then nonneg 0 else neg (m * n + n - 1)

-- #eval Integer.add (Integer.nonneg 19) (Integer.neg 91)  -- 19+(-92)=-73
-- #eval Integer.add (Integer.nonneg 53) (Integer.neg 37)  -- 53+(-38)=15
-- #eval Integer.multiply (Integer.nonneg 13) (Integer.neg 14)  -- 13*(-15)=-195

-------逻辑或-------------------------
def Or.swap (P Q : Prop) : Or P Q → Or Q P := fun ---逻辑或的交换性
  | inl hp => Or.inr hp
  | inr hq => Or.inl hq
def Or.swap' (P Q : Prop) : Or P Q → Or Q P := by ---tactic mode
  intro poq
  exact match poq with
  | inl hp => Or.inr hp
  | inr hq => Or.inl hq
-------逻辑证明-------------------------
example {P Q R S T : Prop} (h : (P ∧ Q ∧ R) ∧ S ∧ T) : S ∧ Q :=
  ⟨h.2.1, h.1.2.1⟩
  -- by
  -- rcases h with ⟨⟨_, q, _⟩,s,_⟩
  -- exact ⟨s,q⟩
--------------------------------
/-用商类型定义整数-/
-- #check Quot.ind
-- #check Quot.recOn
-- #check Quotient.recOn
-- #check Quotient
-- #check Setoid
abbrev r : ℕ × ℕ  → ℕ × ℕ → Prop := fun (m, n) (m', n') => m + n' = m' + n
lemma r_eqv : Equivalence r where
  refl _ := rfl
  symm := by
    intro _ _ h
    simp [r] at h ⊢
    rw [h]
  trans := by
    intro _ _ _ h1 h2
    simp [r] at h1 h2 ⊢
    linarith

def stZ : Setoid (ℕ × ℕ) where
  r := r
  iseqv := r_eqv

def intt : Type := Quotient stZ

-- #check max (-1) (-2)

example : ℤ ≃ intt where
  toFun := fun z => ⟦((max 0 z).toNat, ((max 0 z) - z).toNat)⟧
  invFun  := Quotient.lift (fun x : ℕ × ℕ => ↑x.1 - ↑x.2) <| by
    intro x y hxy
    have hxy' : r x y := hxy---必须要这步？
    simp [r] at hxy'
    linarith
  left_inv := by
    intro z
    aesop
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      rcases le_total x.1 x.2 with h | h
      · simp_all only [Quotient.lift_mk, tsub_le_iff_right, zero_add, Nat.cast_le,
         sup_of_le_left, Int.toNat_zero, zero_sub, neg_sub, Int.toNat_sub', Int.toNat_natCast]
        apply Quotient.sound
        have h: r (0, x.2-x.1) x := by --- r 与≃的转化？
          rw [r]
          aesop
        exact h
      · simp_all only [Quotient.lift_mk, Int.sub_nonneg, Nat.cast_le,
         sup_of_le_right, Int.toNat_sub', Int.toNat_natCast, sub_self, Int.toNat_zero]
        apply Quotient.sound
        have h: r (x.1-x.2, 0) x := by --- r 与≃的转化？
          rw [r]
          aesop
        exact h
----------带点集合态射的id, 复合-------------------
def idd {A : PointedSet} : PointedFunc A A where
  toFun := id
  preserves' := rfl

def compos {A B C : PointedSet} (g : PointedFunc B C) (f : PointedFunc A B) : PointedFunc A C where
  toFun := g ∘ f
  preserves' := by simp only [Function.comp_apply, PointedFunc.preserves]

----------带点集合的同态--------------------------
structure PointedIsom (A B : PointedSet) extends Equiv A B, PointedFunc A B
infix: 25 "≃ₚ" => PointedIsom
example (A B C : PointedSet) :
    (A.Smash B).InternalHom C ≃ₚ A.InternalHom (B.InternalHom C) where
    toFun f :=
      { toFun a :=
        { toFun b := f ⟦(a, b)⟧
          preserves' := by
            convert f.preserves
            simp only [PointedSet.Smash_t, PointedSet.Smash_base, Quotient.eq, smashedSetoid_rel]
            exact .base (by simp) }
        preserves' := by
          rw [PointedFunc.ext_iff]
          ext
          simp only [PointedSet.Smash_t]
          convert f.preserves
          simp only [PointedSet.Smash_base, Quotient.eq, smashedSetoid_rel]
          exact .base (by simp) }
    invFun f :=
    { toFun a := a.recOn (fun a => f a.1 a.2) <| by
        rintro ⟨a, b⟩ ⟨a', b'⟩ (h|h)
        · aesop
        · aesop
      preserves' := by
        change f A.base B.base = C.base
        simp }
    left_inv := by
      rintro f
      ext x
      induction x using Quotient.inductionOn with | h x =>
      rfl
    right_inv _ := rfl
    preserves' := rfl


----------1. Fin n---------------------------
structure IsMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop where
  entryElem :
    ( ∀ i j, 0 < M i j ∧ M i j ≤ n ^ 2 ) ∧
    ( ∀ i1 i2 j1 j2, M i1 j1 = M i2 j2 → (i1, j1) = (i2, j2))
  eqSum :
    let esum := n * ( n ^ 2 +  1) / 2
    (∀ i, ∑ j, M i j = esum ) ∧
    (∀ j, ∑ i, M i j = esum ) ∧
    (∑ i, M i i = esum) ∧
    (∑ i, M i (Fin.rev i) = esum)

--------2. 定义图---------------------------
structure graph (α : Type) where ---有向图
  vertex : Set α
  linkvtx : α × α × ℕ → Bool ---第n条 两点之间是否为连线
  edge : Set (α × α × ℕ) := {(a, b, n) | vertex a ∧ vertex b ∧  linkvtx (a, b, n) = True}

def KonigsbergGraph : graph String where ---KönigsbergGraph
  vertex := ({"NBank", "SBank", "LIsland", "RIsland"} : Set String)
  linkvtx :=
    let undirected {α} (f : α × α × ℕ → Bool) : α × α × ℕ → Bool :=
      fun (a, b, n) => f (a, b, n) || f (b, a, n)
    undirected fun
      | ("LIsland", "NBank", 0) => True
      | ("LIsland", "NBank", 1) => True
      | ("LIsland", "SBank", 0) => True
      | ("LIsland", "SBank", 1) => True
      | ("LIsland", "RIsland", 0) => True
      | ("NBank", "RIsland", 0) => True
      | ("SBank", "RIsland", 0) => True
      | (_, _, _) => False


--------3. 单满vs左右逆---------------------
def InjFun {α β : Type} (f : α → β) : Prop := ∀ a1 a2, f a1 = f a2 → a1 = a2
def LInv {α β : Type} (f : α → β) : Prop := ∃ g: β → α, ∀ a: α,  g (f a) = a
example {α β : Type} (hNE : Nonempty α) (f : α → β) : (InjFun f ↔ LInv f) := by
  constructor
  · intro hinj
    classical
    let g: β → α := fun b =>
      if h : (∃ a : α, f a = b) then
        Classical.choose h
      else
        Classical.choice hNE
    use g
    intro a
    have h: ∃ a', f a' = f a := ⟨a, rfl⟩
    apply hinj
    simp [g]
    exact Classical.choose_spec h
  · intro ⟨g, hg⟩
    intros a1 a2 h
    rw [← hg a1, ← hg a2, h]

def SurjFun {α β : Type} (f : α → β) : Prop := ∀ b, ∃ a, b = f a
def RInv {α β : Type} (f : α → β) : Prop := ∃ g: β → α, ∀ b : β, f (g b) = b
example {α β : Type} (f : α → β) :(SurjFun f ↔ RInv f) := by
  constructor
  · intro hsurj
    let g : β → α := fun b =>
      Classical.choose (hsurj b)
    exact ⟨g, fun x => Eq.symm (Classical.choose_spec (hsurj x))⟩
  · intro h_rinv b
    rcases h_rinv with ⟨g, hg⟩
    use g b
    rw [hg]

def BijFun {α β : Type} (f : α → β) : Prop := InjFun f ∧ SurjFun f
def UInv {α β : Type} (f : α → β) : Prop := ∃! g : β → α, (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b)
example {α β : Type} (f : α → β) :(BijFun f ↔ UInv f) := by
  constructor
  · intro ⟨hinj, hsurj⟩
    let g : β → α := fun b =>
      Classical.choose (hsurj b)
    use g
    have pfl: (∀ a, g (f a) = a) := by
        intro a
        apply hinj
        simp [g]
        exact Eq.symm (Classical.choose_spec (hsurj (f a)))
    have pfr: (∀ b, f (g b) = b) := fun b => (Classical.choose_spec (hsurj b)).symm
    -- aesop
    constructor
    · exact ⟨pfl, pfr⟩
    · intro y ⟨_, hyrinv⟩
      funext b
      apply hinj
      simp [hyrinv, pfr]
  · intro ⟨g, ⟨hglinv, hgrinv⟩, _⟩
    constructor
    · intros a1 a2 h
      rw [← hglinv a1, ← hglinv a2, h]
    · intro b
      exact ⟨g b, (hgrinv b).symm⟩
------------4. Hom交换图--------------------
def homa_ {B B' : Type} (A : Type) (g : B → B') :(A → B) → (A → B'):= fun f0 => g ∘ f0
def hom_b {A' A : Type} (f : A' → A) (B : Type) :(A → B) → (A' → B):= fun g0 => g0 ∘ f
--也没说要证函子性啊
example {A' A B B' : Type} (f : A' → A) (g : B → B') :
  (hom_b f B') ∘ (homa_ A g) = (homa_ A' g) ∘ (hom_b f B):= by
  funext h
  simp[homa_, hom_b]
  rfl
------------5. 余积-------------------------
example {α β : Type} : ∀ (γ : Type) (f: α → γ) (g: β → γ), ∃! fag: Sum α β → γ,
  f = fag ∘ Sum.inl ∧ g = fag ∘ Sum.inr := by
  intro γ f g
  let fag := fun x: Sum α β  =>
    match x with
    | Sum.inl a => f a
    | Sum.inr b => g b
  use fag
  -- aesop
  constructor
  · constructor
    · funext a
      rfl
    · funext b
      rfl
  · intro y ⟨hyf, hyg⟩
    funext x
    match x with
    | Sum.inl a =>
      have h1: f a = fag (Sum.inl a) := rfl
      have h2: f a = y (Sum.inl a) :=by simp [hyf]
      rw [← h1, h2]
    | Sum.inr b =>
      have h1: g b = fag (Sum.inr b) := rfl
      have h2: g b = y (Sum.inr b) := by simp [hyg]
      rw [← h1, h2]

inductive Coprod {ι : Type} (A : ι → Type) : Type where ---余积定义
  | ini : (i : ι) → A i → Coprod A

-- #check Coprod.ini
example {ι : Type} (A : ι → Type) : ∀ (γ : Type) (f : (i : ι ) → A i → γ), ∃! Cof : Coprod A → γ,
  ∀ i, f i = Cof ∘ .ini i := by ---泛性质
  intro γ f
  let Cof : Coprod A → γ := fun x =>
    match x with
    | .ini i ai => f i ai
  use Cof
  -- aesop
  constructor
  · exact fun _ => rfl
  · intro y hy
    ext x
    match x with
    | .ini i ai =>
      have hh: f i ai = y ( .ini i ai) :=by simp [hy]
      rw [← hh]

---------------6. 带点集合---------------
-- structure PointedIsom (A B : PointedSet) extends Equiv A B, PointedFunc A B --回顾定义
-- infix: 25 "≃ₚ" => PointedIsom

infix: 70 "⨂ₚ" => PointedSet.Smash
instance {A B : PointedSet} : CoeSort (A ≃ₚ B) (PointedFunc A B) :=
  ⟨fun e => { toFun := e.toFun, preserves' := e.preserves' }⟩ /- 不管用啊-/

/-对称幺半性的三条-/
-- lemma matchSmash (A B C : PointedSet) (x1 x2 : (A.Product B).t) (c : C)
--    (h : baseInProduct x1 ∧ baseInProduct x2) :
--     (match x1 with | (a, b) => ⟦(a,⟦(b, c)⟧)⟧ :A ⨂ₚ (B ⨂ₚ C)) =
--     (match x2 with | (a, b) => ⟦(a,⟦(b, c)⟧)⟧) := by
--   apply Quotient.sound
--   refine smashedRel.base ?_
--   simp [baseInProduct] at *
--   have heqbase :∀ (bb : B) (cc : C), ((bb = B.base) ∨ (cc = C.base)) →
--     (smashedRel B C (bb, cc) (B.base, C.base)) := by
--     rintro bb cc (hbbase | hcbase) <;>
--     · refine smashedRel.base ?_
--       aesop
--   rcases h with ⟨(h|h),(h|h)⟩ <;> aesop

/-结合律-/
def assoc (A B C : PointedSet) : (A ⨂ₚ B) ⨂ₚ C ≃ₚ A ⨂ₚ (B ⨂ₚ C) where
  toFun := Quotient.lift (fun (abp, c) =>
    (Quotient.lift (fun (a,b) => ⟦(a,⟦(b,c)⟧)⟧) <| by ----Quotient.recOn 会出Eq.rec? 怎么处理
      rintro _ _ (h|h)
      · apply Quotient.sound
        refine smashedRel.base ?_
        simp [baseInProduct] at *
        have heqbase :∀ (bb : B) (cc : C), ((bb = B.base) ∨ (cc = C.base)) →
          (smashedRel B C (bb, cc) (B.base, C.base)) := by
          rintro bb cc (h|h) <;>
          · refine smashedRel.base ?_
            aesop
        aesop
      · aesop
   ) abp) <|  by
    rintro ⟨abp1, c1⟩ ⟨abp2, c2⟩ (h|h)
    · induction abp1 using Quotient.inductionOn with | h ab1 =>
        induction abp2 using Quotient.inductionOn with | h ab2 =>
          simp_all only [baseInProduct, PointedSet.Smash_t,
                PointedSet.Product_t, PointedSet.Smash_base, Quotient.lift_mk, Quotient.eq]
          refine smashedRel.base ?_
          have hbaseq :
            ∀ ab: A × B, (smashedRel A B (ab.1, ab.2) (A.base, B.base))
              → ((ab.1 = A.base) ∨ (ab.2 = B.base)) := by
              rintro ⟨aa, bb⟩ (h|h) <;> aesop

          have hbaseCoord :
            ∀ a b c, (a = A.base) ∨ (b = B.base) ∨ (c = C.base)
              → baseInProduct ((a, ⟦(b, c)⟧) : (A.Product (B ⨂ₚ C)).t) := by
            rintro a b c (ha|hb|hc)
            · exact Or.inl ha
            · apply Or.inr
              simp [PointedSet.Smash]
              apply smashedRel.base
              aesop
            · apply Or.inr
              simp [PointedSet.Smash]
              apply smashedRel.base
              aesop

          have heqBase_baseInProd :
            ∀ (ab : A × B) (c : C.t) , ((smashedSetoid A B) ab (A.base, B.base))
              → baseInProduct ((ab.1, ⟦(ab.2, c)⟧) : (A.Product (B ⨂ₚ C)).t) := by
             intro ab c hab
             rcases hbaseq ab hab with (hab|hab)
             · aesop
             · exact hbaseCoord ab.1 ab.2 c <| Or.inr <| Or.inl hab

          rcases h with ⟨(h1|h2),(h3|h4)⟩
          · exact ⟨heqBase_baseInProd ab1 c1 h1, heqBase_baseInProd ab2 c2 h3⟩
          · exact ⟨heqBase_baseInProd ab1 c1 h1, hbaseCoord ab2.1 ab2.2 c2 <| Or.inr <| Or.inr h4⟩
          · exact ⟨hbaseCoord ab1.1 ab1.2 c1 <| Or.inr <| Or.inr h2, heqBase_baseInProd ab2 c2 h3⟩
          · exact ⟨hbaseCoord ab1.1 ab1.2 c1 <| Or.inr <| Or.inr h2,
                   hbaseCoord ab2.1 ab2.2 c2 <| Or.inr <| Or.inr h4⟩
    · aesop
  invFun := Quotient.lift (fun (a, bcp) =>
    (Quotient.lift (fun (b,c) => ⟦(⟦(a,b)⟧,c)⟧) <| by
      rintro _ _ (h|h)
      · apply Quotient.sound
        refine smashedRel.base ?_
        simp [baseInProduct] at *
        have heqbase :∀ (aa : A) (bb : B), ((aa = A.base) ∨ (bb = B.base)) →
          (smashedRel A B (aa, bb) (A.base, B.base)) := by
          rintro _ _ (h|h) <;>
          · refine smashedRel.base ?_
            aesop
        aesop
      · aesop
    ) bcp) <| by
    rintro ⟨a1, bcp1⟩ ⟨a2, bcp2⟩ (h|h)
    · induction bcp1 using Quotient.inductionOn with | h bc1 =>
        induction bcp2 using Quotient.inductionOn with | h bc2 =>
          simp_all only [baseInProduct, PointedSet.Smash_t,
                PointedSet.Product_t, PointedSet.Smash_base, Quotient.lift_mk, Quotient.eq]
          refine smashedRel.base ?_
          have hbaseq :
            ∀ bc: B × C, (smashedRel B C (bc.1, bc.2) (B.base, C.base))
              → ((bc.1 = B.base) ∨ (bc.2 = C.base)) := by
              rintro ⟨_, _⟩ (h|h) <;> aesop

          have hbaseCoord :
            ∀ a b c, (a = A.base) ∨ (b = B.base) ∨ (c = C.base)
              → baseInProduct ((⟦(a, b)⟧, c) : ((A ⨂ₚ B).Product C).t) := by
            rintro a b c (ha|hb|hc)
            · apply Or.inl
              simp [PointedSet.Smash]
              apply smashedRel.base
              aesop
            · apply Or.inl
              simp [PointedSet.Smash]
              apply smashedRel.base
              aesop
            · exact Or.inr hc

          have heqBase_baseInProd :
            ∀ (a : A) (bc : B × C), ((smashedSetoid B C) bc (B.base, C.base))
              → baseInProduct ((⟦(a, bc.1)⟧, bc.2) : ((A ⨂ₚ B).Product C).t) := by
             intro a bc hbc
             rcases hbaseq bc hbc with (hbc|hbc)
             · exact hbaseCoord a bc.1 bc.2 <| Or.inr <| Or.inl hbc
             · exact hbaseCoord a bc.1 bc.2 <| Or.inr <| Or.inr hbc

          rcases h with ⟨(h1|h2),(h3|h4)⟩
          · exact ⟨hbaseCoord a1 bc1.1 bc1.2 <| Or.inl h1,
                   hbaseCoord a2 bc2.1 bc2.2 <| Or.inl h3⟩
          · exact ⟨hbaseCoord a1 bc1.1 bc1.2 <| Or.inl h1, heqBase_baseInProd a2 bc2 h4⟩
          · exact ⟨heqBase_baseInProd a1 bc1 h2, hbaseCoord a2 bc2.1 bc2.2 <| Or.inl h3⟩
          · exact ⟨heqBase_baseInProd a1 bc1 h2, heqBase_baseInProd a2 bc2 h4⟩
    · aesop
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨abp, _⟩
      induction abp using Quotient.inductionOn with | h _ =>
        simp_all [PointedSet.Smash_t, PointedSet.Product_t, Quotient.lift_mk]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨_, bcp⟩
      induction bcp using Quotient.inductionOn with | h _ =>
        simp_all [PointedSet.Smash_t, PointedSet.Product_t, Quotient.lift_mk]
  preserves' := by aesop
/-左逆-/
def lunit (A : PointedSet) : (S0 ⨂ₚ A ≃ₚ A) where
  toFun x := x.recOn (fun| (true, a) => A.base | (false, a) => a) <| by
      rintro ⟨⟨⟩|⟨⟩, a⟩ ⟨⟨⟩|⟨⟩, a'⟩ (h|h) <;> aesop
  invFun a := ⟦(false, a)⟧
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨⟨⟩|⟨⟩,a⟩
      · simp only [PointedSet.Smash_t, PointedSet.Product_t, S0_t, Quotient.eq]
        rfl
      · simp only [PointedSet.Smash_t, PointedSet.Product_t, S0_t, Quotient.eq]
        refine .base ?_
        simp only [baseInProduct, S0_t, S0_base, Bool.false_eq_true, false_or, true_or, and_true]
        rfl
  right_inv := by
    intro a
    simp_all only [PointedSet.Product_t, S0_t, PointedSet.Smash_t]
    rfl
  preserves' := rfl
/-右逆-/
def runit (A : PointedSet) : (A ⨂ₚ S0 ≃ₚ A) where
  toFun := Quotient.lift (fun| (a, true) => A.base | (a, false) => a) <| by
      rintro ⟨a, ⟨⟩|⟨⟩⟩ ⟨a', ⟨⟩|⟨⟩⟩ (h|h) <;> aesop
  invFun := fun a ↦ ⟦(a, false)⟧
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨a, ⟨⟩|⟨⟩⟩
    · simp only [PointedSet.Smash_t, S0_t, Quotient.eq]
      exact .eq rfl
    · simp only [PointedSet.Smash_t, S0_t, Quotient.eq]
      refine .base ?_
      simp only [baseInProduct, S0_t, S0_base, Bool.false_eq_true, or_false, or_true, and_true]
      rfl
  right_inv _ := rfl
  preserves' := rfl
/-交换性-/
def commu (A B : PointedSet) : A ⨂ₚ B ≃ₚ B ⨂ₚ A where
  toFun := Quotient.lift (fun (a, b) => ⟦(b, a)⟧) <| by
    rintro x1 x2 (h|h)
    · rcases h with ⟨(h|h), (h|h)⟩ <;>
      · apply Quotient.sound
        constructor
        aesop
    · aesop
  invFun := Quotient.lift (fun (b, a) => ⟦(a, b)⟧) <| by
    rintro x1 x2 (h|h)
    · rcases h with ⟨(h|h), (h|h)⟩ <;>
      · apply Quotient.sound
        constructor
        aesop
    · aesop
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
    aesop
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
    aesop
  preserves' := rfl

notation "alp" => assoc
notation "lam" => lunit
notation "rho" => runit
notation "bet" => commu
/-commu ∘ commu = id-/
-- def idd {A : PointedSet} : PointedFunc A A where ---回顾一下
--   toFun := id
--   preserves' := rfl

@[simps]
def PointedFunc.comp {S T T' : PointedSet} (g : PointedFunc T T') (f : PointedFunc S T) :
    PointedFunc S T' where
  toFun := g ∘ f
  preserves' := by simp
infix : 60 "∘pf" => PointedFunc.comp
example (A B : PointedSet) :
  (bet B A).toPointedFunc ∘pf (bet A B).toPointedFunc = (@idd (A ⨂ₚ B)):= by ---为什么不用证preserves'
  ext x
  induction x using Quotient.inductionOn with | h x =>
  aesop

/-ρ ⨂ id = id ⨂ λ ∘ α-/
infix: 70 "⨂pf" => PointedFunc.smash

example (A B : PointedSet) : (rho A) ⨂pf idd =
      (idd ⨂pf (lam B)) ∘pf (alp A S0 B).toPointedFunc := by
  ext x
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x1, b⟩
    induction x1 using Quotient.inductionOn with | h as =>
      rcases as with ⟨a, ⟨⟩|⟨⟩⟩
      · simp_all only [PointedSet.Smash_t, PointedSet.Product_t, S0_t]
        rfl
      · simp_all only [PointedSet.Smash_t, PointedSet.Product_t, S0_t, Equiv.toFun_as_coe,
          PointedFunc.smash, PointedFunc.comp]
        apply Quotient.sound
        refine smashedRel.base ?_
        aesop

/-五边形 α ∘ α = id⨂α  ∘ α ∘ α⨂α-/
example (A B C D : PointedSet) :
  (alp A B (C⨂ₚD)) ∘pf (alp (A⨂ₚB) C D).toPointedFunc =
  (idd ⨂pf (alp B C D).toPointedFunc) ∘pf
    ((alp A (B⨂ₚC) D).toPointedFunc ∘pf
     ((alp A B C).toPointedFunc⨂pf idd)) := by
  ext x
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x, d⟩
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨x, c⟩
      induction x using Quotient.inductionOn with | h x =>
        rcases x with ⟨a, b⟩
        aesop

/-六边形 α ∘ β ∘ α = id⊗β ∘ α ∘ β⊗id-/
example (A B C : PointedSet) :
  (alp B C A) ∘pf ((bet A (B⨂ₚC)).toPointedFunc ∘pf (alp A B C).toPointedFunc) =
    (idd ⨂pf (bet A C).toPointedFunc) ∘pf ((alp B A C).toPointedFunc ∘pf ((bet A B)⨂pf idd)) := by
  ext x
  induction x using Quotient.inductionOn with | h x =>
    rcases x with ⟨x, c⟩
    induction x using Quotient.inductionOn with | h x =>
      rcases x with ⟨a, b⟩
      aesop
