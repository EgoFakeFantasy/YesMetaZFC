import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateCodeConstruction
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthPrefix

/-! # 谓词程序的实际前缀、整张历史限制与正负真值保持 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem pnode_row_mono_l {T ω n r L c : M.Domain}
    (sub : M.MemberSubset r L) (node : Pnode_d T ω n r c) : Pnode_d T ω n L c :=
  node.elim (fun old => Or.inl (bnode_row_mono_l sub old)) Or.inr

/-- 限制新程序的完整证书，得到原程序的完整证书；不使用外部良基性。 -/
theorem ptruthCheck_prefix_l (hKP : M.Models KP) {T A ω n X E F L G K Z H P : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (sub : M.MemberSubset L K)
    (pref : Res0_d F G L T) (check : PtruthCheck_d T A n X E G K Z H)
    (hp : M.IsRestrictionOf (kp_pair_l hKP) P H L) :
    PtruthCheck_d T A n X E F L Z P := by
  refine ⟨fn0_restriction_l hKP check.1 hp sub,fun r hr c hc hrc Y hYZ hY => ?_⟩
  have hrcG := (pref.2.2 r hr c hc).mp hrc
  have hYH := ((hp.2 r Y).mp hY).2
  obtain ⟨bound,row⟩ := check.2 r (sub r hr) c hc hrcG Y hYZ hYH
  have node := pnode_row_mono_l (valid.ordinal.transitive r hr) (valid.row r hr c hc hrc)
  exact ⟨bound,fun f hf => (row f hf).trans (ptruthNode_restriction_l hKP hp node).symm⟩

/-- 任意两个完整历史在旧程序的全部行上吻合。 -/
theorem ptruthCertificate_prefix_l (hZF : M.Models ZF) {T A ω n X E F L G K V H Z J : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (sub : M.MemberSubset L K)
    (pref : Res0_d F G L T) (old : PtruthCheck_d T A n X E F L V H)
    (large : PtruthCheck_d T A n X E G K Z J) :
    M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) H J L := by
  obtain ⟨P,hp⟩ := ZF.exists_restriction hZF (kp_pair_l (ZF.modelsKP hZF)) J L
  have small := ptruthCheck_prefix_l (ZF.modelsKP hZF) valid sub pref large hp
  have eq := ptruthCertificate_unique_l hZF valid old small
  exact eq.symm ▸ hp

/-- 正负两个证书查询在实际程序前缀下保持。 -/
theorem pcertifiedTruth_prefix_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X E F L G K r f : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (extended : PBoundedFormula_d T ω n K G)
    (sub : M.MemberSubset L K) (pref : Res0_d F G L T) (hr : M.mem r L) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ PCertifiedTruth_d positive T A n X E G K r f := by
  obtain ⟨V,H,old⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) valid
  obtain ⟨Z,J,large⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) extended
  have hp := ptruthCertificate_prefix_l hZF valid sub pref old large
  rw [pcertifiedTruth_value_l hZF positive valid old,pcertifiedTruth_value_l hZF positive extended large]
  cases positive
  · exact not_congr (bhit_restriction_l (ZF.modelsKP hZF) hp hr)
  · exact bhit_restriction_l (ZF.modelsKP hZF) hp hr

/-- 消去自由空间参数后，原合法赋值条件与两个极性仍准确保持。 -/
theorem pfiniteTruth_prefix_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L G K r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (extended : PBoundedFormula_d T ω n K G)
    (sub : M.MemberSubset L K) (pref : Res0_d F G L T) (hr : M.mem r L) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive T A ω n X G K r f := by
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  rw [pfiniteTruth_space_l hZF positive hω valid.variables full,
    pfiniteTruth_space_l hZF positive hω extended.variables full]
  exact and_congr_right fun _ => pcertifiedTruth_prefix_l hZF positive valid extended sub pref hr

/-- 真实追加方程自动给出旧程序的有界限制证书。 -/
theorem snoc_predicate_prefix_l (hKP : M.Models KP) {T ω n F L c G : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (snoc : Snoc_d (kp_pair_l hKP) F L c G) :
    Res0_d F G L T := by
  have entries := ((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP valid.graph).1.1).mp snoc).2
  refine ⟨fun p hp => (snoc p).mpr (Or.inl hp),valid.graph.1,fun r hr d _ => ?_⟩
  constructor
  · exact fun h => (entries r d).mpr (Or.inl h)
  · intro h
    rcases (entries r d).mp h with old | ⟨eq,_⟩
    · exact old
    · subst r
      exact (KP.mem_irrefl_d hKP L hr).elim

/-- 实际追加保持旧行的两个极性，后继长度仍是内部对象。 -/
theorem pfiniteTruth_snoc_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L c G K r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (extended : PBoundedFormula_d T ω n K G) (succ : M.SuccessorOf K L)
    (snoc : Snoc_d (kp_pair_l (ZF.modelsKP hZF)) F L c G) (hr : M.mem r L) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive T A ω n X G K r f :=
  pfiniteTruth_prefix_l hZF positive hω valid extended
    (fun i hi => (succ i).mpr (Or.inl hi)) (snoc_predicate_prefix_l (ZF.modelsKP hZF) valid snoc) hr

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
