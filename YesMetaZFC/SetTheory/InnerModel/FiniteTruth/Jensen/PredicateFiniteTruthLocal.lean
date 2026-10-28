import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTruthLocal
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AssignmentSpaceCertificate

/-! # 外部 amenable 谓词的完整赋值空间与历史的同层联合预算 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pfiniteTruth_bundle_l (hZF : M.Models ZF) {α C T A ω n X F L : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (amenable : AmenableSet_d C A)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) :
    ∃ e s Z S E V H, M.mem e C ∧ M.mem s C ∧ M.mem Z C ∧ M.mem S C ∧ M.mem E C ∧ M.mem V C ∧ M.mem H C ∧
      AssignmentSpaceCert_d ω n X e s Z S E ∧ PtruthCheck_d T A n X E F L V H := by
  obtain ⟨e,s,Z,S,E,heC,hsC,hZC,hSC,hEC,space⟩ :=
    jh_assignmentSpaceCertificate_l hZF hα hC hω hωC hXC valid.variables
  obtain ⟨V,H,hVC,hHC,history⟩ :=
    jh_ptruthCertificate_l hZF hα hC amenable hω hωC hTC hnC hXC hEC hFC valid
  exact ⟨e,s,Z,S,E,V,H,heC,hsC,hZC,hSC,hEC,hVC,hHC,space,history⟩

/-- 不要求 A∈C；E 在同层构造后由有界证书见证，不再占源参数槽。 -/
theorem jh_pfiniteTruth_within_l (hZF : M.Models ZF) (positive : Bool) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (ρ : Env M 7)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hp : ∀ i : Fin 6, M.mem (ρ.bound i.succ) C)
    (hω : M.IsOmega (ρ.bound 5))
    (valid : PBoundedFormula_d (ρ.bound 6) (ρ.bound 5) (ρ.bound 4) (ρ.bound 1) (ρ.bound 2)) (r f : M.Domain) :
    Within_d (pfiniteTruth_s positive) ρ r f C ↔
      PFiniteTruth_d positive (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) r f := by
  constructor
  · intro hit
    exact (pfiniteTruth_sat_l (ZF.modelsKP hZF) positive ρ r f).mp (within_toSchema_l _ _ hit)
  · rintro ⟨e0,s0,Z0,S0,Q,V0,H0,space0,hf0,truth0,answer0⟩
    obtain ⟨e,s,Z,S,E,V,H,heC,hsC,hZC,hSC,hEC,hVC,hHC,space,truth⟩ :=
      jh_pfiniteTruth_bundle_l hZF hα hC amenable hω (hp 4) (hp 5) (hp 3) (hp 2) (hp 1) valid
    have fullQ := assignmentSpaceCert_sound_l hZF hω space0
    have fullE := assignmentSpaceCert_sound_l hZF hω space
    have eq := hZF.1.eq_of_same_members Q E (fun g => (fullQ g).trans (fullE g).symm)
    subst Q
    have answer := (pcertifiedTruth_value_l hZF positive valid truth).mp ⟨V0,H0,truth0,answer0⟩
    have inC : ∀ v, v ∈ [e,s,Z,S,E,V,H] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα hC) (hp 4) [e,s,Z,S,E,V,H] inC
    exact ⟨w,hwC,(pfiniteTruth_matrix_sat_l hZF.1 positive ρ r f w).mpr
      ⟨e,hw e (by simp),s,hw s (by simp),Z,hw Z (by simp),S,hw S (by simp),
        E,hw E (by simp),V,hw V (by simp),H,hw H (by simp),space,hf0,truth,answer⟩⟩

theorem jh_pfiniteTruth_assignment_iff_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (ρ : Env M 7)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hp : ∀ i : Fin 6, M.mem (ρ.bound i.succ) C)
    (hω : M.IsOmega (ρ.bound 5))
    (valid : PBoundedFormula_d (ρ.bound 6) (ρ.bound 5) (ρ.bound 4) (ρ.bound 1) (ρ.bound 2)) (r f : M.Domain) :
    (Within_d (pfiniteTruth_s true) ρ r f C ∨ Within_d (pfiniteTruth_s false) ρ r f C) ↔
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f (ρ.bound 4) (ρ.bound 3) := by
  rw [jh_pfiniteTruth_within_l hZF true hα hC ρ amenable hp hω valid,
    jh_pfiniteTruth_within_l hZF false hα hC ρ amenable hp hω valid]
  exact pfiniteTruth_assignment_iff_l hZF hω valid

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
