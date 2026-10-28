import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateCertifiedTruth

/-! # 实际 amenable 谓词的全内部有限历史与完整 Σ₁ 证书预算

A 可以不属于当前层。先取 B=A∩X 的实际层内迹，再运输同一整张历史。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_ptruthHistory_l (hZF : M.Models ZF) {α C T A n X E F L ω : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (amenable : AmenableSet_d C A)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hEC : M.mem E C) (hFC : M.mem F C) (program : Fn0_d L T F) :
    ∀ r, M.mem r ω → ∃ H, M.mem H C ∧ PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F r H := by
  obtain ⟨B,hBC,trace⟩ := amenable.2 X hXC
  intro r hr
  obtain ⟨H,hHC,history⟩ := rd_finite_ptruthHistory_l hZF
    (jh_value_closed_l (ZF.models_kpi_l hZF) hα hC) (jh_value_transitive_l (ZF.models_kpi_l hZF) hC)
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) hα hC) hω hωC hTC hBC hnC hXC hEC hFC program r hr
  exact ⟨H,hHC,(ptruthEval_trace_l (kp_pair_l (ZF.modelsKP hZF)) trace).mpr history⟩

theorem jh_ptruthEval_mem_l (hZF : M.Models ZF) {α C T A n X E F L ω r H : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (amenable : AmenableSet_d C A)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hEC : M.mem E C) (hFC : M.mem F C) (program : Fn0_d L T F) (hr : M.mem r ω)
    (history : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F r H) : M.mem H C := by
  obtain ⟨K,hKC,small⟩ := jh_ptruthHistory_l hZF hα hC amenable hω hωC hTC hnC hXC hEC hFC program r hr
  exact (ptruthEval_unique_l hZF history small).symm ▸ hKC

theorem jh_ptruthCertificate_l (hZF : M.Models ZF) {α C T A n X E F L ω : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (amenable : AmenableSet_d C A)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hEC : M.mem E C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) :
    ∃ Z H, M.mem Z C ∧ M.mem H C ∧ PtruthCheck_d T A n X E F L Z H := by
  let hKP := ZF.modelsKP hZF
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα hC
  obtain ⟨H,hHC,history⟩ := jh_ptruthHistory_l hZF hα hC amenable hω hωC hTC hnC hXC hEC hFC valid.graph L valid.finite
  obtain ⟨Z,hZC,range⟩ := rud.exists_l hKP .range hHC hHC hHC
  have fn : Fn0_d L Z H := fn0_of_function_l hKP ⟨history.1.2.1,history.1.2.2,fun r hr => by
    obtain ⟨Y,value⟩ := (history.1.2.2 r).mp hr
    exact ⟨Y,(range Y).mpr ⟨r,value⟩,value⟩⟩
  exact ⟨Z,H,hZC,hHC,ptruthCheck_of_eval_l hKP valid history fn⟩

theorem jh_pcertifiedTruth_within_l (hZF : M.Models ZF) (positive : Bool) {α C ω : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (ρ : Env M 7)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem (ρ.bound 6) C) (hnC : M.mem (ρ.bound 5) C) (hXC : M.mem (ρ.bound 4) C)
    (hEC : M.mem (ρ.bound 3) C) (hFC : M.mem (ρ.bound 2) C)
    (valid : PBoundedFormula_d (ρ.bound 6) ω (ρ.bound 5) (ρ.bound 1) (ρ.bound 2)) (r f : M.Domain) :
    Within_d (pcertifiedTruth_s positive) ρ r f C ↔
      PCertifiedTruth_d positive (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) r f := by
  constructor
  · intro hit
    exact (pcertifiedTruth_sat_l (ZF.modelsKP hZF) positive ρ r f).mp (within_toSchema_l _ _ hit)
  · intro truth
    let hKP := ZF.modelsKP hZF
    obtain ⟨Z,H,hZC,hHC,check⟩ := jh_ptruthCertificate_l hZF hα hC amenable hω hωC hTC hnC hXC hEC hFC valid
    have answer := (pcertifiedTruth_value_l hZF positive valid check).mp truth
    obtain ⟨w,pair⟩ := KP.exists_pair hKP Z H
    have hwC := jh_value_closed_l (ZF.models_kpi_l hZF) hα hC .pair Z H H hZC hHC hHC w pair
    exact ⟨w,hwC,(pcertifiedTruth_matrix_l hZF.1 positive ρ r f w).mpr
      ⟨Z,(pair Z).mpr (Or.inl rfl),H,(pair H).mpr (Or.inr rfl),check,answer⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
