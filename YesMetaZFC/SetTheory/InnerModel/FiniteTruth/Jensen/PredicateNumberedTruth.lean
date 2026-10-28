import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedTruthSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateProgramContainer
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFiniteTruthLocal

/-! # 双参数谓词数码真值的全部同层辅助预算

A 只须实际 amenable，可以在 C 外。程序和求值域从原数码及真实赋值图恢复。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pnumberedTruthCheck_l (hZF : M.Models ZF) (positive : Bool) {α C A ω e f : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (amenable : AmenableSet_d C A)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hfC : M.mem f C)
    (truth : PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive A ω e f) :
    ∃ T n L F r X P Q, M.mem T C ∧ M.mem n C ∧ M.mem L C ∧ M.mem F C ∧ M.mem r C ∧
      M.mem X C ∧ M.mem P C ∧ M.mem Q C ∧ PNumberedTruthCheck_d positive ω A e f T n L F r X P Q := by
  obtain ⟨T,n,L,F,r,X,hx,valid,code,truthX⟩ := truth
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  have hrC := trans L hLC r code.2.2.1
  have hFC := jh_pbounded_program_mem_l hZF hα h hω hωC valid
  obtain ⟨U,hUC,_,validU⟩ := jh_pboundedProgram_rebase_l hZF hα h hω hωC valid
  have hfX := pfiniteTruth_function_l hZF positive hω truthX
  obtain ⟨Y,hYC,hy,hfY⟩ := jh_assignmentDomain_l hZF hα h hfC hfX
  have truthU := (pfiniteTruth_container_choice_l (ZF.modelsKP hZF) positive valid validU).mp truthX
  have truthY := (pfiniteTruth_domain_choice_l hZF positive hω hx hy validU code.2.2.1 hfX hfY).mp truthU
  let ρP : Env M 5 := ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => U)))),fun _ => ω⟩
  obtain ⟨P,hPC,hP⟩ := (jh_pprogramCode_within_l hZF hα h ρP F e hω hωC).mpr ⟨validU,code⟩
  have pc : PProgramWitness_d U ω n L F r e P := (pprogramCode_matrix_sat_l (ZF.modelsKP hZF) ρP F e P).mp hP
  let ρQ : Env M 7 := ⟨Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases Y (Fin.cases n (Fin.cases ω (fun _ => U)))))),fun _ => ω⟩
  have hp : ∀ i : Fin 6, M.mem (ρQ.bound i.succ) C :=
    Fin.cases hLC (Fin.cases hFC (Fin.cases hYC (Fin.cases hnC (Fin.cases hωC (fun _ => hUC)))))
  obtain ⟨Q,hQC,hQ⟩ := (jh_pfiniteTruth_within_l hZF positive hα h ρQ amenable hp hω validU r f).mpr truthY
  have qc : PTruthWitness_d positive U A ω n Y F L r f Q := (pfiniteTruth_matrix_sat_l hZF.1 positive ρQ r f Q).mp hQ
  exact ⟨U,n,L,F,r,Y,P,Q,hUC,hnC,hLC,hFC,hrC,hYC,hPC,hQC,hy,pc,qc⟩

theorem jh_pnumberedTruth_within_l (hZF : M.Models ZF) (positive : Bool) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (e f : M.Domain)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1))
    (hωC : M.mem (ρ.bound 1) C) (hfC : M.mem f C) :
    Within_d (pnumberedTruth_s positive) ρ e f C ↔
      PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive (ρ.bound 0) (ρ.bound 1) e f := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨T,_,n,_,L,_,F,_,r,_,X,_,P,_,Q,_,cert⟩ := (pnumberedTruth_matrix_sat_l (ZF.modelsKP hZF) positive ρ e f w).mp hw
    exact pnumberedTruthCheck_sound_l hZF positive hω cert
  · intro truth
    obtain ⟨T,n,L,F,r,X,P,Q,hTC,hnC,hLC,hFC,hrC,hXC,hPC,hQC,cert⟩ :=
      jh_pnumberedTruthCheck_l hZF positive hα h amenable hω hωC hfC truth
    have all : ∀ v, v ∈ [T,n,L,F,r,X,P,Q] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [T,n,L,F,r,X,P,Q] all
    exact ⟨w,hwC,(pnumberedTruth_matrix_sat_l (ZF.modelsKP hZF) positive ρ e f w).mpr
      ⟨T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
        X,hw X (by simp),P,hw P (by simp),Q,hw Q (by simp),cert⟩⟩

/-- 任意完整局部见证本身推出输出 f 属于 C，未把它另作假设。 -/
theorem pnumberedTruth_within_output_l (hZF : M.Models ZF) (positive : Bool) {C : M.Domain}
    (trans : M.TransitiveSet C) (ρ : Env M 2) {e f : M.Domain}
    (hit : Within_d (pnumberedTruth_s positive) ρ e f C) : M.mem f C := by
  obtain ⟨w,hwC,body⟩ := hit
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,Q,hQw,cert⟩ :=
    (pnumberedTruth_matrix_sat_l (ZF.modelsKP hZF) positive ρ e f w).mp body
  obtain ⟨_,_,_,_,_,_,_,_,E,hEQ,_,_,_,_,_,hfE,_⟩ := cert.2.2
  exact trans E (trans Q (trans w hwC Q hQw) E hEQ) f hfE

/-- 局部图的准确范围：层内输出且背景数码真值成立。 -/
theorem jh_pnumberedTruth_exact_within_l (hZF : M.Models ZF) (positive : Bool) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (e f : M.Domain)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) :
    Within_d (pnumberedTruth_s positive) ρ e f C ↔ M.mem f C ∧
      PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive (ρ.bound 0) (ρ.bound 1) e f := by
  constructor
  · intro hit
    have hfC := pnumberedTruth_within_output_l hZF positive (jh_value_transitive_l (ZF.models_kpi_l hZF) h) ρ hit
    exact ⟨hfC,(jh_pnumberedTruth_within_l hZF positive hα h ρ e f amenable hω hωC hfC).mp hit⟩
  · rintro ⟨hfC,truth⟩
    exact (jh_pnumberedTruth_within_l hZF positive hα h ρ e f amenable hω hωC hfC).mpr truth

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
