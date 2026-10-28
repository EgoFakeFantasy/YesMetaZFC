import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NaturalPairSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteSubset
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruth

/-! # 原规范自然数配对的同层证书与局部 Σ₁ 准确性

方块、完整规范关系和整张塌缩图均在原 J 层内构造或证明属于该层。
仅假设该层包含内部 ω，不要求小层满足 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_naturalPairCheck_l (hZF : M.Models ZF) {α C ω a b c : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ha : M.mem a ω) (hb : M.mem b ω)
    (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c) :
    ∃ n X R Y F p, M.mem n C ∧ M.mem X C ∧ M.mem R C ∧ M.mem Y C ∧ M.mem F C ∧ M.mem p C ∧
      NaturalPairCheck_d ω a b c n X R Y F p := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  obtain ⟨n,X,R,Y,F,p,cert⟩ := naturalPairCheck_exists_l hZF hω ha hb pair
  have details := cert
  obtain ⟨hn,_,_,hy,_,order,_,hpX,collapse,_⟩ := details
  have hnC := trans ω hωC n hn
  have hyC := trans ω hωC Y hy
  have horder := (canonicalOrderCheck_correct_l (ZF.modelsKP hZF)).mp order
  have hXC := jh_product_mem_l hZF hα h hnC hnC horder.1
  have fx : Finite_d I ω X := ZF.cartesianSquare_bounded_in_omega hZF I hω hn horder.1
  obtain ⟨Q,hQ⟩ := ZF.exists_cartesianProduct hZF I X X
  have hQC := jh_product_mem_l hZF hα h hXC hXC hQ
  have fr := finite_relation_l hZF hω fx order.2.1
  have hRC := jh_finite_subset_mem_l hZF hα h hω hωC hQC fr (fun t ht => (hQ t).mpr (order.2.1 t ht))
  obtain ⟨W,hW⟩ := ZF.exists_cartesianProduct hZF I X Y
  have hWC := jh_product_mem_l hZF hα h hXC hyC hW
  have fy : Finite_d I ω Y := ⟨Y,hy,ZF.exists_inclusionInjection hZF I (fun _ ht => ht)⟩
  have ff := finite_function_graph_l hZF hω fx fy (fn0_function_l (ZF.modelsKP hZF) collapse.1)
  have hFC := jh_finite_subset_mem_l hZF hα h hω hωC hWC ff (fun t ht => (hW t).mpr (collapse.1.1 t ht))
  exact ⟨n,X,R,Y,F,p,hnC,hXC,hRC,hyC,hFC,trans X hXC p hpX,cert⟩

theorem jh_naturalPair_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (a c : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (ha : M.mem a (ρ.bound 1)) (hb : M.mem (ρ.bound 0) (ρ.bound 1)) :
    Within_d naturalPair_s ρ a c C ↔ Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a (ρ.bound 0) c := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨n,_,X,_,R,_,Y,_,F,_,p,_,cert⟩ := (naturalPair_matrix_sat_l (ZF.modelsKP hZF) ρ a c w).mp hw
    exact naturalPairCheck_sound_l hZF cert
  · intro pair
    obtain ⟨n,X,R,Y,F,p,hnC,hXC,hRC,hYC,hFC,hpC,cert⟩ := jh_naturalPairCheck_l hZF hα h hω hωC ha hb pair
    have all : ∀ v, v ∈ [n,X,R,Y,F,p] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [n,X,R,Y,F,p] all
    exact ⟨w,hwC,(naturalPair_matrix_sat_l (ZF.modelsKP hZF) ρ a c w).mpr
      ⟨n,hw n (by simp),X,hw X (by simp),R,hw R (by simp),Y,hw Y (by simp),
        F,hw F (by simp),p,hw p (by simp),cert⟩⟩

/-- 实际 Σ₁ 图在原 J 层和背景之间准确一致，未假设层内 KP。 -/
theorem jh_naturalPair_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 2) (a c : (rt_model_l C hnC).Domain)
    (hω : M.IsOmega (ρ.bound 1).val) (ha : M.mem a.val (ρ.bound 1).val)
    (hb : M.mem (ρ.bound 0).val (ρ.bound 1).val) :
    naturalPair_s.schema.denote ρ a c ↔ naturalPair_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) a.val c.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC naturalPair_s ρ a c).trans
    ((jh_naturalPair_within_l hZF hα h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) a.val c.val
      hω (ρ.bound 1).property ha hb).trans
        (naturalPair_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
          a.val c.val hω ha hb).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
