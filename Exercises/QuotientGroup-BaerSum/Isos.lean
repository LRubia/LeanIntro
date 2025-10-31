import Mathlib
suppress_compilation

variable (G : Type) [Group G] (H : Subgroup G)
#check AddSubgroup.map
#check Subgroup.subgroupOf
#check H ⊓ (⊤ : Subgroup G)
#check QuotientGroup.map_mk'
#check Subgroup.subgroupOf
#check Subtype.val
#check Subgroup.inclusion_inj
#check Subgroup.sup_eq_closure
#check Quotient.inductionOn'
#check Quotient.inductionOn
#check Quotient.mk'
#check Quotient.mk
#check @HMul.hMul (Set G) (Set G) (Set G)
#check Abelianization.commutator_subset_ker

/-shall i mark it with a noncomputable label? -/
def qutoKer_eq_image (G H : Type) [Group G] [Group H] (ϕ : G →* H) : G ⧸ ϕ.ker ≃* ϕ.range := by
  refine MulEquiv.ofBijective (QuotientGroup.lift _ ϕ.rangeRestrict (by simp)) ?_
  constructor
  · intro a b
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H y =>
      simp
      intro h
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, ← ϕ.ker_rangeRestrict, MonoidHom.mem_ker,
        map_mul, ← h, map_inv, inv_mul_cancel]
  · rintro y
    obtain ⟨x, hx⟩ := ϕ.rangeRestrict_surjective y
    use Quotient.mk _ x
    simpa using hx
  -- · rintro ⟨_, x, rfl⟩
  --   use Quotient.mk _ x
  --   rfl

def qutoIntersect_eq_Mulquto (G : Type) [Group G] (H N : Subgroup G) [N.Normal] :
  H ⧸ (N.subgroupOf H) ≃* ((H ⊔ N : Subgroup G) : Type) ⧸ (N.subgroupOf (H ⊔ N)) := by
  refine MulEquiv.ofBijective (QuotientGroup.map _ _ (Subgroup.inclusion (by simp)) (by simp) ) ?_
  constructor
  · intro a b
    induction a, b using Quotient.inductionOn₂' with | h a b =>
      intro h
      simp only [QuotientGroup.map_mk, QuotientGroup.eq, ← map_inv, ← map_mul,
        Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at h
      apply Quotient.sound'
      rwa [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  · intro y
    induction y using Quotient.inductionOn' with | h y =>
    obtain ⟨y, hy⟩ := y
    simp [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H N
       (by simp[Subgroup.normalizer_eq_top])] at hy
    rcases hy with ⟨a, ha, b, hb, rfl⟩
    use Quotient.mk'' ⟨a, ha⟩
    apply Quotient.sound'
    simpa [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]

variable (G : Type) [Group G] (N : Subgroup G) [N.Normal] (M : Subgroup G) [M.Normal] (h : N ≤ M)
#check QuotientGroup.map N M (.id G) h

def quotQuotToQuot : (G ⧸ N) ⧸ (Subgroup.map (QuotientGroup.mk' N) M) ≃* G ⧸ M := by
  refine MulEquiv.ofBijective (QuotientGroup.lift _
  (QuotientGroup.map _ _ (.id _) h) (by rintro _ ⟨x, _, rfl⟩; simpa)) ?_
  constructor
  · intro a b
    induction a, b using Quotient.inductionOn₂' with | h a b =>
    induction a, b using Quotient.inductionOn₂' with | h a b =>
      simp [QuotientGroup.eq]
      exact fun h => ⟨a⁻¹ * b, h, by simp⟩
  · intro y
    induction y using Quotient.inductionOn' with | h y =>
      exact ⟨Quotient.mk'' (Quotient.mk'' y), by simp⟩
