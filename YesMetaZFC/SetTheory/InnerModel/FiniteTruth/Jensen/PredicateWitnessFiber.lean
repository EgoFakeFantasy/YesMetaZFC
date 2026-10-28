import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateWitnessFiberSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.WitnessFiber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedTruth

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

/-- 给定同层参数时，保留原解码与求值域装配完整数码真值证书。 -/
theorem jh_pnumberedTruthCheck_for_l (hZF : M.Models ZF) {α C A T ω n L F r X e g : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (amenable : AmenableSet_d C A) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hnC : M.mem n C) (hLC : M.mem L C) (hFC : M.mem F C) (hXC : M.mem X C)
    (hx : M.TransitiveSet X) (valid : PBoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e)
    (truth : PFiniteTruth_d true T A ω n X F L r g) :
    ∃ P Q, M.mem P C ∧ M.mem Q C ∧ PNumberedTruthCheck_d true ω A e g T n L F r X P Q := by
  let ρP : Env M 5 := ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => T)))),fun _ => ω⟩
  obtain ⟨P,hPC,hP⟩ := (jh_pprogramCode_within_l hZF hα h ρP F e hω hωC).mpr ⟨valid,code⟩
  let ρQ : Env M 7 := ⟨Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T)))))),fun _ => ω⟩
  have hp : ∀ i : Fin 6, M.mem (ρQ.bound i.succ) C := Fin.cases hLC (Fin.cases hFC (Fin.cases hXC (Fin.cases hnC (Fin.cases hωC (fun _ => hTC)))))
  obtain ⟨Q,hQC,hQ⟩ := (jh_pfiniteTruth_within_l hZF true hα h ρQ amenable hp hω valid r g).mpr truth
  exact ⟨P,Q,hPC,hQC,hx,(pprogramCode_matrix_sat_l (ZF.modelsKP hZF) ρP F e P).mp hP,
    (pfiniteTruth_matrix_sat_l hZF.1 true ρQ r g Q).mp hQ⟩

theorem jh_pwitnessFiberCheck_l (hZF : M.Models ZF) {α C A ω input y : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (amenable : AmenableSet_d C A) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hinC : M.mem input C) (hyC : M.mem y C)
    (fiber : PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) A ω input y) :
    ∃ T n L F r X e f i g P Q, M.mem T C ∧ M.mem n C ∧ M.mem L C ∧ M.mem F C ∧ M.mem r C ∧
      M.mem X C ∧ M.mem e C ∧ M.mem f C ∧ M.mem i C ∧ M.mem g C ∧ M.mem P C ∧ M.mem Q C ∧
        PWitnessFiberCheck_d A ω input y T n L F r X e f i g P Q := by
  obtain ⟨T,n,L,F,r,X,e,f,i,g,packet,hx,valid,code,hi,hf,hy,update,truth⟩ := fiber
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have details := packet
  obtain ⟨q,hq,hpacket⟩ := details
  have coords := po_pair_bound_l trans hinC hpacket
  have fi := po_pair_bound_l trans coords.2 hq
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  have hrC := trans L hLC r code.2.2.1
  have hFC := jh_pbounded_program_mem_l hZF hα h hω hωC valid
  obtain ⟨U,hUC,_,validU⟩ := jh_pboundedProgram_rebase_l hZF hα h hω hωC valid
  obtain ⟨Y,hYC,hY,hfY,hyY⟩ := jh_assignmentDomain_withValue_l hZF hα h fi.1 hyC hf
  have hgY := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hfY hi hyY
  have hgC := jh_finite_function_mem_l hZF hα h hω hωC hYC valid.variables hgY
  have hgX := pfiniteTruth_function_l hZF true hω truth
  have truthU := (pfiniteTruth_container_choice_l (ZF.modelsKP hZF) true valid validU).mp truth
  have truthY := (pfiniteTruth_domain_choice_l hZF true hω hx hY validU code.2.2.1 hgX hgY).mp truthU
  obtain ⟨P,Q,hPC,hQC,cert⟩ := jh_pnumberedTruthCheck_for_l hZF hα h amenable hω hωC hUC hnC hLC hFC hYC hY validU code truthY
  exact ⟨U,n,L,F,r,Y,e,f,i,g,P,Q,hUC,hnC,hLC,hFC,hrC,hYC,coords.1,fi.1,fi.2,hgC,hPC,hQC,
    packet,hi,hyY,fn0_of_function_l (ZF.modelsKP hZF) hfY,fn0_of_function_l (ZF.modelsKP hZF) hgY,
    (updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF)) hfY hgY hi hyY).mpr update,cert⟩

theorem jh_pwitnessFiber_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (input y : M.Domain)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C) (hyC : M.mem y C) :
    Within_d pwitnessFiber_s ρ input y C ↔ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨T,_,n,_,L,_,F,_,r,_,X,_,e,_,f,_,i,_,g,_,P,_,Q,_,cert⟩ := (pwitnessFiber_matrix_sat_l (ZF.modelsKP hZF) ρ input y w).mp hw
    exact pwitnessFiberCheck_sound_l hZF hω cert
  · intro fiber
    obtain ⟨T,n,L,F,r,X,e,f,i,g,P,Q,hTC,hnC,hLC,hFC,hrC,hXC,heC,hfC,hiC,hgC,hPC,hQC,cert⟩ :=
      jh_pwitnessFiberCheck_l hZF hα h amenable hω hωC hinC hyC fiber
    have all : ∀ v, v ∈ [T,n,L,F,r,X,e,f,i,g,P,Q] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [T,n,L,F,r,X,e,f,i,g,P,Q] all
    exact ⟨w,hwC,(pwitnessFiber_matrix_sat_l (ZF.modelsKP hZF) ρ input y w).mpr
      ⟨T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
        X,hw X (by simp),e,hw e (by simp),f,hw f (by simp),i,hw i (by simp),g,hw g (by simp),
          P,hw P (by simp),Q,hw Q (by simp),cert⟩⟩


/-- 完整局部证书本身给出输出在原层内。 -/
theorem pwitnessFiber_within_output_l (hZF : M.Models ZF) {C : M.Domain}
    (trans : M.TransitiveSet C) (ρ : Env M 2) {input y : M.Domain}
    (hit : Within_d pwitnessFiber_s ρ input y C) : M.mem y C := by
  obtain ⟨w,hwC,body⟩ := hit
  obtain ⟨_,_,_,_,_,_,_,_,_,_,X,hXw,_,_,_,_,_,_,_,_,_,_,_,_,cert⟩ :=
    (pwitnessFiber_matrix_sat_l (ZF.modelsKP hZF) ρ input y w).mp body
  exact trans X (trans w hwC X hXw) y cert.2.2.1

/-- 精确局部定义域只要求普通输入在层内，A 仍可在层外。 -/
theorem jh_pwitnessFiber_exact_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (input y : M.Domain)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1))
    (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C) :
    Within_d pwitnessFiber_s ρ input y C ↔ M.mem y C ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y := by
  constructor
  · intro hit
    have hyC := pwitnessFiber_within_output_l hZF (jh_value_transitive_l (ZF.models_kpi_l hZF) h) ρ hit
    exact ⟨hyC,(jh_pwitnessFiber_within_l hZF hα h ρ input y amenable hω hωC hinC hyC).mp hit⟩
  · rintro ⟨hyC,fiber⟩
    exact (jh_pwitnessFiber_within_l hZF hα h ρ input y amenable hω hωC hinC hyC).mpr fiber

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
