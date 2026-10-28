import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedTruthSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramContainer

/-! # 数码操作真值的全部辅助参数和证书的同层预算 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_numberedTruthCheck_l (hZF : M.Models ZF) (positive : Bool) {α C ω e f : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) (hfC : M.mem f C)
    (truth : NumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive ω e f) :
    ∃ T n L F r X P Q, M.mem T C ∧ M.mem n C ∧ M.mem L C ∧ M.mem F C ∧ M.mem r C ∧
      M.mem X C ∧ M.mem P C ∧ M.mem Q C ∧ NumberedTruthCheck_d positive ω e f T n L F r X P Q := by
  obtain ⟨T,n,L,F,r,X,hx,valid,code,truthX⟩ := truth
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  have hrC := trans L hLC r code.2.2.1
  have hFC := jh_bounded_program_mem_l hZF hα h hω hωC valid
  obtain ⟨U,hUC,_,validU⟩ := jh_boundedProgram_rebase_l hZF hα h hω hωC valid
  have hfX := finiteTruth_function_l hZF positive hω truthX
  obtain ⟨Y,hYC,hy,hfY⟩ := jh_assignmentDomain_l hZF hα h hfC hfX
  have truthU := (finiteTruth_container_choice_l (ZF.modelsKP hZF) positive valid validU).mp truthX
  have truthY := (finiteTruth_domain_choice_l hZF positive hω hx hy hfX hfY validU code.2.2.1).mp truthU
  let ρP : Env M 5 := ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => U)))),fun _ => ω⟩
  obtain ⟨P,hPC,hP⟩ := (jh_programCode_within_l hZF hα h ρP F e hω hωC).mpr ⟨validU,code⟩
  have pc : ProgramWitness_d U ω n L F r e P := (programCode_matrix_sat_l (ZF.modelsKP hZF) ρP F e P).mp hP
  let ρQ : Env M 6 := ⟨Fin.cases L (Fin.cases F (Fin.cases Y (Fin.cases n (Fin.cases ω (fun _ => U))))),fun _ => ω⟩
  have hp : ∀ i, M.mem (ρQ.bound i) C :=
    Fin.cases hLC (Fin.cases hFC (Fin.cases hYC (Fin.cases hnC (Fin.cases hωC (fun _ => hUC)))))
  obtain ⟨Q,hQC,hQ⟩ := (jh_finiteTruth_within_l hZF hα h positive ρQ hp hω validU r f).mpr truthY
  have qc : TruthWitness_d positive U ω n Y F L r f Q := (finiteTruth_matrix_sat_l hZF.1 positive ρQ r f Q).mp hQ
  exact ⟨U,n,L,F,r,Y,P,Q,hUC,hnC,hLC,hFC,hrC,hYC,hPC,hQC,hy,pc,qc⟩

theorem jh_numberedTruth_within_l (hZF : M.Models ZF) (positive : Bool) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (e f : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hfC : M.mem f C) :
    Within_d (numberedTruth_s positive) ρ e f C ↔ NumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive (ρ.bound 0) e f := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨T,_,n,_,L,_,F,_,r,_,X,_,P,_,Q,_,cert⟩ := (numberedTruth_matrix_sat_l (ZF.modelsKP hZF) positive ρ e f w).mp hw
    exact numberedTruthCheck_sound_l hZF positive hω cert
  · intro truth
    obtain ⟨T,n,L,F,r,X,P,Q,hTC,hnC,hLC,hFC,hrC,hXC,hPC,hQC,cert⟩ := jh_numberedTruthCheck_l hZF positive hα h hω hωC hfC truth
    have all : ∀ v, v ∈ [T,n,L,F,r,X,P,Q] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [T,n,L,F,r,X,P,Q] all
    exact ⟨w,hwC,(numberedTruth_matrix_sat_l (ZF.modelsKP hZF) positive ρ e f w).mpr
      ⟨T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
        X,hw X (by simp),P,hw P (by simp),Q,hw Q (by simp),cert⟩⟩

/-- 原层中的实际 Σ₁ 解释与背景相同；不预设原层满足 KP。 -/
theorem jh_numberedTruth_local_l (hZF : M.Models ZF) (positive : Bool) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 1) (e f : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 0).val) :
    (numberedTruth_s positive).schema.denote ρ e f ↔ (numberedTruth_s positive).schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) e.val f.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC (numberedTruth_s positive) ρ e f).trans
    ((jh_numberedTruth_within_l hZF positive hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) e.val f.val
      hω (ρ.bound 0).property f.property).trans
        (numberedTruth_sat_l hZF positive (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
          e.val f.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
