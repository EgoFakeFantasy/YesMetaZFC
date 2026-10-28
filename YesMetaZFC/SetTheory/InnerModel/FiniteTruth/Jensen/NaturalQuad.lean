import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.QuadSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalPair

/-! # 原四字段指令数码证书的同层存在与局部准确性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_quadCheck_l (hZF : M.Models ZF) {α C ω c z : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (input : NaturalQuad_d ω c) (code : QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z) :
    ∃ W, M.mem W C ∧ QuadCheck_d ω c z W := by
  let hKP := ZF.modelsKP hZF
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  obtain ⟨t,v,i,p,j,k,a,b,ht,hi,hj,hk,ha,hb,hc,hv,hp,p1,p2,p3⟩ := naturalQuad_decompose_l hZF hω input code
  have hpC := closed .opair j k j (trans ω hωC j hj) (trans ω hωC k hk) (trans ω hωC j hj)
    p (rd_opair_value_l hZF.1 hp)
  have hvC := closed .opair i p i (trans ω hωC i hi) hpC (trans ω hωC i hi) v (rd_opair_value_l hZF.1 hv)
  have choose {a b c : M.Domain} (ha : M.mem a ω) (hb : M.mem b ω)
      (pair : Oc_pair_d (kp_pair_l hKP) a b c) : ∃ w, M.mem w C ∧ PairWitness_d ω a b c w := by
    let ρ : Env M 2 := ⟨Fin.cases b (fun _ => ω),fun _ => ω⟩
    obtain ⟨w,hwC,hw⟩ := (jh_naturalPair_within_l hZF hα h ρ a c hω hωC ha hb).mpr pair
    exact ⟨w,hwC,(naturalPair_matrix_sat_l hKP ρ a c w).mp hw⟩
  obtain ⟨u,huC,hu⟩ := choose hj hk p1
  obtain ⟨x,hxC,hx⟩ := choose hi ha p2
  obtain ⟨y,hyC,hy⟩ := choose ht hb p3
  have all : ∀ q, q ∈ [v,p,u,x,y] → M.mem q C := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨W,hWC,cover⟩ := rd_finiteTruth_cover_l hKP closed hωC [v,p,u,x,y] all
  exact ⟨W,hWC,t,ht,v,cover v (by simp),i,hi,p,cover p (by simp),j,hj,k,hk,a,ha,b,hb,
    u,cover u (by simp),x,cover x (by simp),y,cover y (by simp),hc,hv,hp,hu,hx,hy⟩

theorem jh_quadCode_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (c z : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) :
    Within_d quadCode_s ρ c z C ↔ NaturalQuad_d (ρ.bound 0) c ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
  constructor
  · rintro ⟨W,_,cert⟩
    exact quadCheck_sound_l hZF ((quadCode_matrix_sat_l (ZF.modelsKP hZF) ρ c z W).mp cert)
  · rintro ⟨input,code⟩
    obtain ⟨W,hWC,cert⟩ := jh_quadCheck_l hZF hα h hω hωC input code
    exact ⟨W,hWC,(quadCode_matrix_sat_l (ZF.modelsKP hZF) ρ c z W).mpr cert⟩

theorem jh_quadCode_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 1) (c z : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 0).val) :
    quadCode_s.schema.denote ρ c z ↔ quadCode_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) c.val z.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC quadCode_s ρ c z).trans
    ((jh_quadCode_within_l hZF hα h (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
      c.val z.val hω (ρ.bound 0).property).trans
        (quadCode_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) c.val z.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
