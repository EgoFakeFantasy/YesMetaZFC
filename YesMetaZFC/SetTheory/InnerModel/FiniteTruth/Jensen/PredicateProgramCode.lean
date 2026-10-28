import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramNumberSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedRows
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalSequence
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateProgramNumber

/-! # 原完整程序编号的同层证书与局部 Σ₁ 准确性

构造编号列、序列证书和两次末尾配对的全部见证；不预设小层 KP。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pprogramCheck_l (hZF : M.Models ZF) {α C T ω n L F r e : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (valid : PBoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e) :
    ∃ G c d R Q p q, M.mem G C ∧ M.mem c C ∧ M.mem d C ∧ M.mem R C ∧ M.mem Q C ∧ M.mem p C ∧ M.mem q C ∧
      PProgramCheck_d T ω n L F r e G c d R Q p q := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  obtain ⟨_,_,hr,_,G,c,d,rows,seq,pair1,pair2⟩ := code
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  have hd := oc_pair_natural_l I hZF hω valid.variables hc pair1
  have hrω := hω.transitive hZF L valid.finite r hr
  have hGC := jh_finite_function_mem_l hZF hα h hω hωC hωC valid.finite rows.1
  let ρR : Env M 4 := ⟨Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => T))),fun _ => ω⟩
  obtain ⟨R,hRC,hR⟩ := (jh_prowsCode_within_l hZF hα h ρR F G hω hωC).mpr ⟨valid,rows⟩
  have rcert : PRowsWitness_d T ω n L F G R := (prowsCode_matrix_sat_l hKP ρR F G R).mp hR
  let ρQ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  have input : NaturalSequence_d ω G := ⟨L,valid.finite,fn0_of_function_l hKP rows.1⟩
  obtain ⟨Q,hQC,hQ⟩ := (jh_sequenceCode_within_l hZF hα h ρQ G c hω hωC).mpr ⟨input,seq⟩
  have qcert : SequenceWitness_d ω G c Q := (sequenceCode_matrix_sat_l hKP ρQ G c Q).mp hQ
  have pairWithin {a b z : M.Domain} (ha : M.mem a ω) (hb : M.mem b ω) (pair : Oc_pair_d I a b z) :
      ∃ p, M.mem p C ∧ PairWitness_d ω a b z p := by
    let ρ : Env M 2 := ⟨Fin.cases b (fun _ => ω),fun _ => ω⟩
    obtain ⟨p,hpC,hp⟩ := (jh_naturalPair_within_l hZF hα h ρ a z hω hωC ha hb).mpr pair
    exact ⟨p,hpC,(naturalPair_matrix_sat_l hKP ρ a z p).mp hp⟩
  obtain ⟨p,hpC,pcert⟩ := pairWithin valid.variables hc pair1
  obtain ⟨q,hqC,lastCert⟩ := pairWithin hd hrω pair2
  exact ⟨G,c,d,R,Q,p,q,hGC,trans ω hωC c hc,trans ω hωC d hd,hRC,hQC,hpC,hqC,
    hc,hd,hr,rcert,qcert,pcert,lastCert⟩

theorem jh_pprogramCode_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 5) (F e : M.Domain)
    (hω : M.IsOmega (ρ.bound 3)) (hωC : M.mem (ρ.bound 3) C) :
    Within_d pprogramCode_s ρ F e C ↔ PBoundedFormula_d (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) F ∧
      ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) F (ρ.bound 0) e := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨G,_,c,_,d,_,R,_,Q,_,p,_,q,_,cert⟩ := (pprogramCode_matrix_sat_l (ZF.modelsKP hZF) ρ F e w).mp hw
    exact pprogramCheck_sound_l hZF hω cert
  · rintro ⟨valid,code⟩
    obtain ⟨G,c,d,R,Q,p,q,hGC,hcC,hdC,hRC,hQC,hpC,hqC,cert⟩ := jh_pprogramCheck_l hZF hα h hω hωC valid code
    have all : ∀ v, v ∈ [G,c,d,R,Q,p,q] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [G,c,d,R,Q,p,q] all
    exact ⟨w,hwC,(pprogramCode_matrix_sat_l (ZF.modelsKP hZF) ρ F e w).mpr
      ⟨G,hw G (by simp),c,hw c (by simp),d,hw d (by simp),R,hw R (by simp),Q,hw Q (by simp),
        p,hw p (by simp),q,hw q (by simp),cert⟩⟩

theorem jh_pprogramCode_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 5) (F e : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 3).val) :
    pprogramCode_s.schema.denote ρ F e ↔ pprogramCode_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val e.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC pprogramCode_s ρ F e).trans
    ((jh_pprogramCode_within_l hZF hα h (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
      F.val e.val hω (ρ.bound 3).property).trans
        (pprogramCode_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val e.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
