import Mathlib

section direct_sum
variable (R : Type) [CommRing R]
variable (ι : Type) [DecidableEq ι]
variable (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (B : Type) [AddCommGroup B] [Module R B]

open DirectSum

#check Finsupp.lift
#check DFinsupp.lsingle
#check DFinsupp.finset_sum_apply
#check DirectSum.sum_support_of


variable {R ι M B} in
lemma hsimp (af : ⨁ i : ι, (B →ₗ[R] M i)) (b : B) (i : ι) : open Classical in
      ((lmk R ι M (DFinsupp.support af)) fun i ↦ (af ↑i) b) i = af i b := by
      erw [DFinsupp.lmk_apply]
      simp only [Finset.coe_sort_coe, DFinsupp.mk_apply, DFinsupp.mem_support_toFun, ne_eq,
        dite_eq_ite, ite_eq_left_iff, not_not]
      aesop

noncomputable
def map_mu : (⨁ i : ι, (B →ₗ[R] M i)) →ₗ[R] (B →ₗ[R] ⨁ i : ι, M i) where
  toFun f := open Classical in
    lmk _ _ M f.support ∘ₗ ( {
      toFun b i := f i b
      map_add' x y := by ext i; rw [map_add]; rfl
      map_smul' r := by aesop
    } )
  map_add' f g := by
    ext b i
    simp only [Finset.coe_sort_coe, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    conv => rhs; simp only [add_apply, LinearMap.add_apply, LinearMap.coe_comp, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply]
    erw [hsimp (f + g), hsimp f, hsimp g]
    simp
  map_smul' r f := by
    ext b i
    have hsimp (af : ⨁ i : ι, (B →ₗ[R] M i)): open Classical in
      ((lmk R ι M (DFinsupp.support af)) fun i ↦ (af ↑i) b) i = af i b := by
      erw [DFinsupp.lmk_apply]
      simp only [Finset.coe_sort_coe, DFinsupp.mk_apply, DFinsupp.mem_support_toFun, ne_eq,
        dite_eq_ite, ite_eq_left_iff, not_not]
      aesop
    simp only [Finset.coe_sort_coe, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply, RingHom.id_apply, LinearMap.smul_apply]
    erw [hsimp, smul_apply, smul_apply, hsimp f, LinearMap.smul_apply]

example : Function.Injective (map_mu R ι M B) := by
    intro f g h
    ext i b
    have h : (map_mu _ _ _ _) f b i = (map_mu _ _ _ _) g b i := by rw[h]
    erw [hsimp f, hsimp g] at h
    exact h

end direct_sum

noncomputable section basis

variable {F : Type} [Field F]
variable {V : Type} [AddCommGroup V] [Module F V]
variable {W : Type} [AddCommGroup W] [Module F W]
variable {n : ℕ} (B : Module.Basis (Fin n) F V)
variable {m : ℕ} (C : Module.Basis (Fin m) F W)

def homToMatrix : (V →ₗ[F] W) → Matrix (Fin m) (Fin n) F :=
  fun f => Matrix.of fun i j => C.equivFun (f (B j)) i

variable (f g : V →ₗ[F] W)

lemma homToMatrix_spec :
    C.equivFun ∘ₗ f = (homToMatrix B C f).mulVecLin ∘ₗ B.equivFun := by
  apply B.ext
  intro j
  ext i
  simp [Matrix.mulVec, dotProduct, Finsupp.single_apply]
  rfl

lemma homToMatrix_spec' :
    C.equivFun ∘ₗ f ∘ₗ B.equivFun.symm = (homToMatrix B C f).mulVecLin := by
  rw [← LinearMap.comp_assoc, homToMatrix_spec, LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.comp_id]

lemma homToMatrix_spec'' :
    f = C.equivFun.symm ∘ₗ (homToMatrix B C f).mulVecLin ∘ₗ B.equivFun := by
  rw [← homToMatrix_spec, LinearEquiv.symm_comp_cancel_left]

def matrixToHom (M : Matrix (Fin m) (Fin n) F) : V →ₗ[F] W :=
  C.equivFun.symm ∘ₗ M.mulVecLin ∘ₗ B.equivFun

lemma homToMatrix_add :
    homToMatrix B C (f + g) = homToMatrix B C f + homToMatrix B C g := by
  have eq₁ := calc (homToMatrix B C (f + g)).mulVecLin
    _ = C.equivFun ∘ₗ (f + g) ∘ₗ B.equivFun.symm := homToMatrix_spec' B C (f + g)
      |>.symm
    _ = C.equivFun ∘ₗ (f ∘ₗ B.equivFun.symm + g ∘ₗ B.equivFun.symm) := by
      rw [LinearMap.add_comp]
    _ = C.equivFun ∘ₗ f ∘ₗ B.equivFun.symm + C.equivFun ∘ₗ g ∘ₗ B.equivFun.symm :=
      LinearMap.comp_add _ _ _
    _ = (homToMatrix B C f).mulVecLin + (homToMatrix B C g).mulVecLin := by
      rw [homToMatrix_spec', homToMatrix_spec']
    _ = (homToMatrix B C f + homToMatrix B C g).mulVecLin :=
      Matrix.mulVecLin_add _ _ |>.symm
  apply Matrix.ext_of_mulVec_single
  intro i
  exact congr($eq₁ (Pi.single i 1))

lemma homToMatrix_smul (r : F):
    homToMatrix B C (r • f) = r • homToMatrix B C f := by
  apply Matrix.ext_of_mulVec_single
  intro i
  have eq := calc (homToMatrix B C (r • f)).mulVecLin
    _ = C.equivFun ∘ₗ (r • f) ∘ₗ B.equivFun.symm := homToMatrix_spec' _ _ _ |>.symm
    _ = C.equivFun ∘ₗ (r • (f ∘ₗ B.equivFun.symm)) := by
      rw [LinearMap.smul_comp]
    _ = r • (C.equivFun ∘ₗ f ∘ₗ B.equivFun.symm) := LinearMap.comp_smul _ _ _
    _ = r • (homToMatrix B C f).mulVecLin := by rw [homToMatrix_spec']
    _ = (r • homToMatrix B C f).mulVecLin := by
      simp only [map_smul]
  exact congr($eq (Pi.single i 1))

def endEquivMatrix :
    (V →ₗ[F] W) ≃+ Matrix (Fin m) (Fin n) F where
  toFun := homToMatrix B C
  invFun := matrixToHom B C
  left_inv := by
    intro f
    rw [matrixToHom, ← homToMatrix_spec'']
  right_inv := by
    intro M
    have eq₁ := calc (homToMatrix B C (matrixToHom B C M)).mulVecLin
      _ = C.equivFun ∘ₗ (matrixToHom B C M) ∘ₗ B.equivFun.symm :=
        homToMatrix_spec' B C (matrixToHom B C M) |>.symm
      _ = C.equivFun ∘ₗ (C.equivFun.symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ B.equivFun)
        ∘ₗ B.equivFun.symm.toLinearMap := by rfl
      _ = (C.equivFun ∘ₗ C.equivFun.symm.toLinearMap) ∘ₗ M.mulVecLin ∘ₗ
          (B.equivFun ∘ₗ B.equivFun.symm.toLinearMap) := by
        simp [LinearMap.comp_assoc, C.equivFun.comp_symm_cancel_left]
      _ = M.mulVecLin := by
        simp [LinearMap.id_comp, LinearMap.comp_id]
    apply Matrix.ext_of_mulVec_single
    intro i
    have eq₂ := congr($eq₁ (Pi.single i 1))
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul] at eq₂ ⊢
    rw [eq₂]
  map_add' := homToMatrix_add B C
end basis
