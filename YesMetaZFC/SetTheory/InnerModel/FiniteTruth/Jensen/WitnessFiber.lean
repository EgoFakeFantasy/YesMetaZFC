import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.WitnessFiberSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NumberedTruth

/-! # 实际见证槽更新及完整统一见证的同层预算 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 原赋值与给定新值有共同的同层传递求值域。 -/
theorem jh_assignmentDomain_withValue_l (hZF : M.Models ZF) {α C n f X y : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hfC : M.mem f C) (hyC : M.mem y C)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    ∃ Y, M.mem Y C ∧ M.TransitiveSet Y ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n Y ∧ M.mem y Y := by
  obtain ⟨A,hAC,ha,hfA⟩ := jh_assignmentDomain_l hZF hα h hfC hf
  obtain ⟨B,hBC,hb,hyB⟩ := jh_local_enclosure_l (ZF.models_kpi_l hZF) hα h y hyC
  obtain ⟨Y,hYC,hY⟩ := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h).union_l (ZF.modelsKP hZF) hAC hBC
  have sub : M.MemberSubset A Y := fun z hz => (hY z).mpr (Or.inl hz)
  have hy : M.TransitiveSet Y := fun z hz t ht => (hY t).mpr (((hY z).mp hz).elim
    (fun hz => Or.inl (ha z hz t ht)) (fun hz => Or.inr (hb z hz t ht)))
  exact ⟨Y,hYC,hy,function_codomain_mono_l (kp_pair_l (ZF.modelsKP hZF)) sub hfA,(hY y).mpr (Or.inr hyB)⟩

/-- 给定同层参数时，保留原解码与求值域装配完整数码真值证书。 -/
theorem jh_numberedTruthCheck_for_l (hZF : M.Models ZF) {α C T ω n L F r X e g : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hnC : M.mem n C) (hLC : M.mem L C) (hFC : M.mem F C) (hXC : M.mem X C)
    (hx : M.TransitiveSet X) (valid : BoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e)
    (truth : FiniteTruth_d true T ω n X F L r g) :
    ∃ P Q, M.mem P C ∧ M.mem Q C ∧ NumberedTruthCheck_d true ω e g T n L F r X P Q := by
  let ρP : Env M 5 := ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => T)))),fun _ => ω⟩
  obtain ⟨P,hPC,hP⟩ := (jh_programCode_within_l hZF hα h ρP F e hω hωC).mpr ⟨valid,code⟩
  let ρQ : Env M 6 := ⟨Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T))))),fun _ => ω⟩
  have hp : ∀ i, M.mem (ρQ.bound i) C := Fin.cases hLC (Fin.cases hFC (Fin.cases hXC (Fin.cases hnC (Fin.cases hωC (fun _ => hTC)))))
  obtain ⟨Q,hQC,hQ⟩ := (jh_finiteTruth_within_l hZF hα h true ρQ hp hω valid r g).mpr truth
  exact ⟨P,Q,hPC,hQC,hx,(programCode_matrix_sat_l (ZF.modelsKP hZF) ρP F e P).mp hP,
    (finiteTruth_matrix_sat_l hZF.1 true ρQ r g Q).mp hQ⟩

theorem jh_witnessFiberCheck_l (hZF : M.Models ZF) {α C ω input y : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hinC : M.mem input C) (hyC : M.mem y C)
    (fiber : WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) ω input y) :
    ∃ T n L F r X e f i g P Q, M.mem T C ∧ M.mem n C ∧ M.mem L C ∧ M.mem F C ∧ M.mem r C ∧
      M.mem X C ∧ M.mem e C ∧ M.mem f C ∧ M.mem i C ∧ M.mem g C ∧ M.mem P C ∧ M.mem Q C ∧
        WitnessFiberCheck_d ω input y T n L F r X e f i g P Q := by
  obtain ⟨T,n,L,F,r,X,e,f,i,g,packet,hx,valid,code,hi,hf,hy,update,truth⟩ := fiber
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have details := packet
  obtain ⟨q,hq,hpacket⟩ := details
  have coords := po_pair_bound_l trans hinC hpacket
  have fi := po_pair_bound_l trans coords.2 hq
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  have hrC := trans L hLC r code.2.2.1
  have hFC := jh_bounded_program_mem_l hZF hα h hω hωC valid
  obtain ⟨U,hUC,_,validU⟩ := jh_boundedProgram_rebase_l hZF hα h hω hωC valid
  obtain ⟨Y,hYC,hY,hfY,hyY⟩ := jh_assignmentDomain_withValue_l hZF hα h fi.1 hyC hf
  have hgY := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hfY hi hyY
  have hgC := jh_finite_function_mem_l hZF hα h hω hωC hYC valid.variables hgY
  have hgX := finiteTruth_function_l hZF true hω truth
  have truthU := (finiteTruth_container_choice_l (ZF.modelsKP hZF) true valid validU).mp truth
  have truthY := (finiteTruth_domain_choice_l hZF true hω hx hY hgX hgY validU code.2.2.1).mp truthU
  obtain ⟨P,Q,hPC,hQC,cert⟩ := jh_numberedTruthCheck_for_l hZF hα h hω hωC hUC hnC hLC hFC hYC hY validU code truthY
  exact ⟨U,n,L,F,r,Y,e,f,i,g,P,Q,hUC,hnC,hLC,hFC,hrC,hYC,coords.1,fi.1,fi.2,hgC,hPC,hQC,
    packet,hi,hyY,fn0_of_function_l (ZF.modelsKP hZF) hfY,fn0_of_function_l (ZF.modelsKP hZF) hgY,
    (updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF)) hfY hgY hi hyY).mpr update,cert⟩

theorem jh_witnessFiber_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (input y : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C) (hyC : M.mem y C) :
    Within_d witnessFiber_s ρ input y C ↔ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨T,_,n,_,L,_,F,_,r,_,X,_,e,_,f,_,i,_,g,_,P,_,Q,_,cert⟩ := (witnessFiber_matrix_sat_l (ZF.modelsKP hZF) ρ input y w).mp hw
    exact witnessFiberCheck_sound_l hZF hω cert
  · intro fiber
    obtain ⟨T,n,L,F,r,X,e,f,i,g,P,Q,hTC,hnC,hLC,hFC,hrC,hXC,heC,hfC,hiC,hgC,hPC,hQC,cert⟩ :=
      jh_witnessFiberCheck_l hZF hα h hω hωC hinC hyC fiber
    have all : ∀ v, v ∈ [T,n,L,F,r,X,e,f,i,g,P,Q] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [T,n,L,F,r,X,e,f,i,g,P,Q] all
    exact ⟨w,hwC,(witnessFiber_matrix_sat_l (ZF.modelsKP hZF) ρ input y w).mpr
      ⟨T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
        X,hw X (by simp),e,hw e (by simp),f,hw f (by simp),i,hw i (by simp),g,hw g (by simp),
          P,hw P (by simp),Q,hw Q (by simp),cert⟩⟩

theorem jh_witnessFiber_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 1) (input y : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 0).val) :
    witnessFiber_s.schema.denote ρ input y ↔ witnessFiber_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val y.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC witnessFiber_s ρ input y).trans
    ((jh_witnessFiber_within_l hZF hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val y.val hω
      (ρ.bound 0).property input.property y.property).trans
        (witnessFiber_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) input.val y.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
