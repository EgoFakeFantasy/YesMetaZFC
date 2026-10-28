import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NormalizedInputSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterAssignment

/-! # 唯一规范输入及完整编号证书的同层预算 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_normalizedInputCheck_l (hZF : M.Models ZF) {α C ω input packet : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) (hinC : M.mem input C)
    (graph : NormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) ω input packet) :
    M.mem packet C ∧ ∃ T n L F r X e k a z f P, M.mem T C ∧ M.mem n C ∧ M.mem L C ∧ M.mem F C ∧ M.mem r C ∧
      M.mem X C ∧ M.mem e C ∧ M.mem k C ∧ M.mem a C ∧ M.mem z C ∧ M.mem f C ∧ M.mem P C ∧
        NormalizedInputCheck_d ω input packet T n L F r X e k a z f P := by
  obtain ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩ := graph
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have details := outer
  obtain ⟨q,hq,hinput⟩ := details
  have ec := po_pair_bound_l trans hinC hinput
  have ka := po_pair_bound_l trans ec.2 hq
  have hzC := trans ω hωC z (num_mem_l hZF.1 hω parameters.zero)
  obtain ⟨Y,g,hYC,_,hgC,paramY⟩ := jh_parameterDomain_l hZF hα h hω hωC ka.2 valid.variables
    parameters.capacity parameters.zero parameters.parameters
  have eq := parameters.unique_l (ZF.modelsKP hZF) paramY
  subst g
  have hpC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e f z ec.1 hgC hzC packet (rd_triple_value_l hZF.1 inner)
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  have hrC := trans L hLC r code.2.2.1
  have hFC := jh_bounded_program_mem_l hZF hα h hω hωC valid
  obtain ⟨U,hUC,_,validU⟩ := jh_boundedProgram_rebase_l hZF hα h hω hωC valid
  let ρ : Env M 5 := ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => U)))),fun _ => ω⟩
  obtain ⟨P,hPC,hP⟩ := (jh_programCode_within_l hZF hα h ρ F e hω hωC).mpr ⟨validU,code⟩
  exact ⟨hpC,U,n,L,F,r,Y,e,k,a,z,f,P,hUC,hnC,hLC,hFC,hrC,hYC,ec.1,ka.1,ka.2,hzC,hgC,hPC,
    outer,inner,paramY,(programCode_matrix_sat_l (ZF.modelsKP hZF) ρ F e P).mp hP⟩

theorem jh_normalizedInput_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (input packet : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C) :
    Within_d normalizedInput_s ρ input packet C ↔ NormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input packet := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨T,_,n,_,L,_,F,_,r,_,X,_,e,_,k,_,a,_,z,_,f,_,P,_,cert⟩ := (normalizedInput_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mp hw
    exact normalizedInputCheck_sound_l hZF hω cert
  · intro graph
    obtain ⟨_,T,n,L,F,r,X,e,k,a,z,f,P,hTC,hnC,hLC,hFC,hrC,hXC,heC,hkC,haC,hzC,hfC,hPC,cert⟩ :=
      jh_normalizedInputCheck_l hZF hα h hω hωC hinC graph
    have all : ∀ v, v ∈ [T,n,L,F,r,X,e,k,a,z,f,P] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [T,n,L,F,r,X,e,k,a,z,f,P] all
    exact ⟨w,hwC,(normalizedInput_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mpr
      ⟨T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
        X,hw X (by simp),e,hw e (by simp),k,hw k (by simp),a,hw a (by simp),z,hw z (by simp),
          f,hw f (by simp),P,hw P (by simp),cert⟩⟩

theorem jh_normalizedInput_output_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (graph : normalizedInput_s.schema.denote ρ input packet) : M.mem packet C :=
  (jh_normalizedInputCheck_l hZF hα h hω hωC hinC ((normalizedInput_sat_l hZF ρ input packet hω).mp graph)).1

theorem jh_normalizedInput_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 1) (input packet : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 0).val) :
    normalizedInput_s.schema.denote ρ input packet ↔ normalizedInput_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val packet.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC normalizedInput_s ρ input packet).trans
    ((jh_normalizedInput_within_l hZF hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val packet.val hω (ρ.bound 0).property input.property).trans
        (normalizedInput_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val packet.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
