import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedRowsSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalQuad
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteWitnessCover

/-! # 原逐行编号证书的同层覆盖与局部准确性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_prowsNumberCheck_l (hZF : M.Models ZF) {α C T ω n L F G : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (valid : PBoundedFormula_d T ω n L F) (rows : NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G) :
    ∃ V, M.mem V C ∧ PRowsNumberCheck_d T ω n L F G V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := numberedRowCheck_env_l T ω F G
  have total r (hr : M.mem r L) : ∃ W, M.mem W C ∧ numberedRowCheck_s.denote ρ r W := by
    obtain ⟨z,hz,hrz⟩ := rows.1.2.2 r hr
    obtain ⟨_,c,hrc,code⟩ := (rows.2 r z).mp hrz
    have input := pnode_naturalQuad_l hZF hω valid.variables (hω.transitive hZF L valid.finite r hr) (valid.at_l hrc).2.2
    obtain ⟨W,hWC,cert⟩ := jh_quadCheck_l hZF hα h hω hωC input code
    exact ⟨W,hWC,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mpr
      ⟨c,(valid.graph.bound_l hrc).2,z,hz,hrc,hrz,cert⟩⟩
  have finite : Finite_d I ω L := ⟨L,valid.finite,ZF.exists_inclusionInjection hZF I (fun _ hi => hi)⟩
  obtain ⟨V,hVC,cover⟩ := jh_finite_witnessCover_l hZF numberedRowCheck_s ρ hα h hω hωC finite total
  exact ⟨V,hVC,valid,fn0_of_function_l (ZF.modelsKP hZF) rows.1,fun r hr =>
    (cover r hr).imp fun W hW => ⟨hW.1,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mp hW.2⟩⟩

theorem jh_prowsCode_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 4) (F G : M.Domain)
    (hω : M.IsOmega (ρ.bound 2)) (hωC : M.mem (ρ.bound 2) C) :
    Within_d prowsCode_s ρ F G C ↔ PBoundedFormula_d (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) F ∧
      NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 2) (ρ.bound 0) F G := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨V,_,cert⟩ := (prowsCode_matrix_sat_l (ZF.modelsKP hZF) ρ F G w).mp hw
    exact prowsNumberCheck_sound_l hZF cert
  · rintro ⟨valid,rows⟩
    obtain ⟨V,hVC,cert⟩ := jh_prowsNumberCheck_l hZF hα h hω hωC valid rows
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [V] (fun x hx => by
        have eq : x = V := by simpa using hx
        exact eq ▸ hVC)
    exact ⟨w,hwC,(prowsCode_matrix_sat_l (ZF.modelsKP hZF) ρ F G w).mpr ⟨V,hw V (by simp),cert⟩⟩

theorem jh_prowsCode_local_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hnC : Nonempty {x : M.Domain // M.mem x C})
    (ρ : Env (rt_model_l C hnC) 4) (F G : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 2).val) :
    prowsCode_s.schema.denote ρ F G ↔ prowsCode_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val G.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC prowsCode_s ρ F G).trans
    ((jh_prowsCode_within_l hZF hα h (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
      F.val G.val hω (ρ.bound 2).property).trans
        (prowsCode_sat_l hZF (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) F.val G.val hω).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
