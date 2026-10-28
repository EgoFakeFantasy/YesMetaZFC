import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SequenceSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalFold

/-! # 原序列编号的同层证书与局部 Σ₁ 准确性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_sequenceCheck_l (hZF : M.Models ZF) {α C ω F c : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (input : NaturalSequence_d ω F) (code : Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) ω F c) :
    ∃ n b e s H V p, M.mem n C ∧ M.mem b C ∧ M.mem e C ∧ M.mem s C ∧ M.mem H C ∧ M.mem V C ∧ M.mem p C ∧
      SequenceCheck_d ω F c n b e s H V p := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  obtain ⟨n,b,hn,fn,hb,fold,pair⟩ := naturalSequence_decompose_l hZF hω input code
  obtain ⟨e,s,H,V,heC,hsC,hHC,hVC,cert⟩ := jh_foldCheck_l hZF hα h hω hωC hn fn fold
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => ω),fun _ => ω⟩
  obtain ⟨p,hpC,hp⟩ := (jh_naturalPair_within_l hZF hα h ρ n c hω hωC hn hb).mpr pair
  have pcert : PairWitness_d ω n b c p := (naturalPair_matrix_sat_l (ZF.modelsKP hZF) ρ n c p).mp hp
  exact ⟨n,b,e,s,H,V,p,trans ω hωC n hn,trans ω hωC b hb,heC,hsC,hHC,hVC,hpC,cert,pcert⟩

theorem jh_sequenceCode_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (F c : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) :
    Within_d sequenceCode_s ρ F c C ↔ NaturalSequence_d (ρ.bound 0) F ∧
      Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) F c := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨n,_,b,_,e,_,s,_,H,_,V,_,p,_,cert⟩ := (sequenceCode_matrix_sat_l (ZF.modelsKP hZF) ρ F c w).mp hw
    exact sequenceCheck_sound_l hZF hω cert
  · rintro ⟨input,code⟩
    obtain ⟨n,b,e,s,H,V,p,hnC,hbC,heC,hsC,hHC,hVC,hpC,cert⟩ := jh_sequenceCheck_l hZF hα h hω hωC input code
    have all : ∀ v, v ∈ [n,b,e,s,H,V,p] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [n,b,e,s,H,V,p] all
    exact ⟨w,hwC,(sequenceCode_matrix_sat_l (ZF.modelsKP hZF) ρ F c w).mpr
      ⟨n,hw n (by simp),b,hw b (by simp),e,hw e (by simp),s,hw s (by simp),
        H,hw H (by simp),V,hw V (by simp),p,hw p (by simp),cert⟩⟩

theorem jh_sequenceCode_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 1) (F c : (rt_model_l C hnC).Domain)
    (hω : M.IsOmega (ρ.bound 0).val) :
    sequenceCode_s.schema.denote ρ F c ↔ sequenceCode_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val c.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC sequenceCode_s ρ F c).trans
    ((jh_sequenceCode_within_l hZF hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val c.val
      hω (ρ.bound 0).property).trans
        (sequenceCode_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
          F.val c.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
