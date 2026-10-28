import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteWitnessCover
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalPair

/-! # 原完整有限折叠证书的同 J 层存在与局部准确性

完整历史由自然数值有限函数空间预算给出；逐步配对见证通过实际原模板的
内部有限见证覆盖一次装配到同层。小层不预设 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_foldCheck_l (hZF : M.Models ZF) {α C ω F n c : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hn : M.mem n ω) (input : Fn0_d n ω F)
    (fold : Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n c) :
    ∃ e s H V, M.mem e C ∧ M.mem s C ∧ M.mem H C ∧ M.mem V C ∧ FoldCheck_d ω F n c e s H V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  obtain ⟨e,s,H,run⟩ := foldRun_exists_l hZF hω hn input fold
  have heC := trans ω hωC e (num_mem_l hZF.1 hω run.zero)
  have hsC := trans ω hωC s run.successor_finite
  have hHC := jh_finite_function_mem_l hZF hα h hω hωC hωC run.successor_finite
    (fn0_function_l (ZF.modelsKP hZF) run.history)
  let ρ := foldRow_env_l ω F H s
  have total r (hr : M.mem r n) : ∃ w, M.mem w C ∧ foldRow_s.denote ρ r w := by
    obtain ⟨a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,pair⟩ := run.step r hr
    let η : Env M 2 := ⟨Fin.cases a (fun _ => ω),fun _ => ω⟩
    obtain ⟨w,hwC,hw⟩ := (jh_naturalPair_within_l hZF hα h η b d hω hωC hb ha).mpr pair
    have wit : PairWitness_d ω b a d w := (naturalPair_matrix_sat_l (ZF.modelsKP hZF) η b d w).mp hw
    exact ⟨w,hwC,(foldRow_schema_sat_l (ZF.modelsKP hZF) ω F H s r w).mpr
      ⟨a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,wit⟩⟩
  have finite : Finite_d I ω n := ⟨n,hn,ZF.exists_inclusionInjection hZF I (fun _ hi => hi)⟩
  obtain ⟨V,hVC,cover⟩ := jh_finite_witnessCover_l hZF foldRow_s ρ hα h hω hωC finite total
  exact ⟨e,s,H,V,heC,hsC,hHC,hVC,run.finite,run.successor_finite,run.successor,run.input,run.history,
    run.zero,run.initial,run.final,fun r hr => (cover r hr).imp fun w hw =>
      ⟨hw.1,(foldRow_schema_sat_l (ZF.modelsKP hZF) ω F H s r w).mp hw.2⟩⟩

theorem jh_naturalFold_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (F c : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) :
    Within_d naturalFold_s ρ F c C ↔ M.mem (ρ.bound 0) (ρ.bound 1) ∧ Fn0_d (ρ.bound 0) (ρ.bound 1) F ∧
      Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F (ρ.bound 0) c := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨e,_,s,_,H,_,V,_,cert⟩ := (naturalFold_matrix_sat_l (ZF.modelsKP hZF) ρ F c w).mp hw
    exact ⟨cert.1,cert.2.2.2.1,foldCheck_sound_l hZF hω cert⟩
  · rintro ⟨hn,input,fold⟩
    obtain ⟨e,s,H,V,heC,hsC,hHC,hVC,cert⟩ := jh_foldCheck_l hZF hα h hω hωC hn input fold
    have all : ∀ v, v ∈ [e,s,H,V] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [e,s,H,V] all
    exact ⟨w,hwC,(naturalFold_matrix_sat_l (ZF.modelsKP hZF) ρ F c w).mpr
      ⟨e,hw e (by simp),s,hw s (by simp),H,hw H (by simp),V,hw V (by simp),cert⟩⟩

theorem jh_naturalFold_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 2) (F c : (rt_model_l C hnC).Domain)
    (hω : M.IsOmega (ρ.bound 1).val) :
    naturalFold_s.schema.denote ρ F c ↔ naturalFold_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val c.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC naturalFold_s ρ F c).trans
    ((jh_naturalFold_within_l hZF hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val c.val
      hω (ρ.bound 1).property).trans
        (naturalFold_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
          F.val c.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
