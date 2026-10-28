import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedCodeContainer

/-! # 实际程序前缀保持统一操作真值

前缀使用模型内的实际限制图，长度只要求内部包含。限制完整真值历史后，
合法旧指令的全部引用仍落在旧长度内，再由原递归历史唯一性识别旧结果。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 扩大合法指令的前驱行界，不改变代码或变量界。 -/
theorem bnode_row_mono_l {T ω n r L c : M.Domain}
    (sub : M.MemberSubset r L) (node : Bnode_d T ω n r c) : Bnode_d T ω n L c := by
  rcases node with node | node | node | node
  · exact Or.inl node
  · exact Or.inr (Or.inl node)
  · obtain ⟨i,hi,j,hj,k,hk,hop,hir,hjr,hkω⟩ := node
    exact Or.inr (Or.inr (Or.inl ⟨i,hi,j,hj,k,hk,hop,sub i hir,sub j hjr,hkω⟩))
  · obtain ⟨i,hi,j,hj,k,hk,hop,hin,hjn,hkr⟩ := node
    exact Or.inr (Or.inr (Or.inr ⟨i,hi,j,hj,k,hk,hop,hin,hjn,sub k hkr⟩))

/-- 实际限制图在任意内部子域上保持函数图和值域界。 -/
theorem fn0_restriction_l (hKP : M.Models KP) {L K Z H P : M.Domain}
    (fn : Fn0_d K Z H) (hp : M.IsRestrictionOf (kp_pair_l hKP) P H L)
    (sub : M.MemberSubset L K) : Fn0_d L Z P := by
  refine ⟨(res0_of_restriction_l hKP fn hp).2.1,?_,?_⟩
  · intro r hr
    obtain ⟨Y,hYZ,hY⟩ := fn.2.1 r (sub r hr)
    exact ⟨Y,hYZ,(hp.2 r Y).mpr ⟨hr,hY⟩⟩
  · intro r _ Y _ W _ hY hW
    exact (fn0_function_l hKP fn).1.2 r Y W ((hp.2 r Y).mp hY).2 ((hp.2 r W).mp hW).2

/-- 限制新程序的完整证书，得到原程序的完整证书；不使用外部良基性。 -/
theorem btruthCheck_prefix_l (hKP : M.Models KP) {T ω n X E F L G K Z H P : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (sub : M.MemberSubset L K)
    (pref : Res0_d F G L T) (check : BtruthCheck_d T n X E G K Z H)
    (hp : M.IsRestrictionOf (kp_pair_l hKP) P H L) :
    BtruthCheck_d T n X E F L Z P := by
  refine ⟨fn0_restriction_l hKP check.1 hp sub,fun r hr c hc hrc Y hYZ hY => ?_⟩
  have hrcG := (pref.2.2 r hr c hc).mp hrc
  have hYH := ((hp.2 r Y).mp hY).2
  obtain ⟨bound,row⟩ := check.2 r (sub r hr) c hc hrcG Y hYZ hYH
  have node := bnode_row_mono_l (valid.ordinal.transitive r hr) (valid.row r hr c hc hrc)
  exact ⟨bound,fun f hf => (row f hf).trans (btruthNode_restriction_l hKP hp node).symm⟩

/-- 任意两个完整历史在旧程序的全部行上吻合。 -/
theorem btruthCertificate_prefix_l (hZF : M.Models ZF) {T ω n X E F L G K V H Z J : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (sub : M.MemberSubset L K)
    (pref : Res0_d F G L T) (old : BtruthCheck_d T n X E F L V H)
    (large : BtruthCheck_d T n X E G K Z J) :
    M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) H J L := by
  obtain ⟨P,hp⟩ := ZF.exists_restriction hZF (kp_pair_l (ZF.modelsKP hZF)) J L
  have small := btruthCheck_prefix_l (ZF.modelsKP hZF) valid sub pref large hp
  have eq := btruthCertificate_unique_l hZF valid old small
  exact eq.symm ▸ hp

/-- 正负两个证书查询在实际程序前缀下保持。 -/
theorem certifiedTruth_prefix_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X E F L G K r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (extended : BoundedFormula_d T ω n K G)
    (sub : M.MemberSubset L K) (pref : Res0_d F G L T) (hr : M.mem r L) :
    CertifiedTruth_d positive T n X E F L r f ↔ CertifiedTruth_d positive T n X E G K r f := by
  obtain ⟨V,H,old⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) valid
  obtain ⟨Z,J,large⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) extended
  have hp := btruthCertificate_prefix_l hZF valid sub pref old large
  rw [certifiedTruth_value_l hZF positive valid old,certifiedTruth_value_l hZF positive extended large]
  cases positive
  · exact not_congr (bhit_restriction_l (ZF.modelsKP hZF) hp hr)
  · exact bhit_restriction_l (ZF.modelsKP hZF) hp hr

/-- 消去自由空间参数后，原合法赋值条件与两个极性仍准确保持。 -/
theorem finiteTruth_prefix_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L G K r f : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (extended : BoundedFormula_d T ω n K G)
    (sub : M.MemberSubset L K) (pref : Res0_d F G L T) (hr : M.mem r L) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive T ω n X G K r f := by
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  rw [finiteTruth_space_l hZF positive hω valid.variables full,
    finiteTruth_space_l hZF positive hω extended.variables full]
  exact and_congr_right fun _ => certifiedTruth_prefix_l hZF positive valid extended sub pref hr

/-- 真实追加方程自动给出旧程序的有界限制证书。 -/
theorem snoc_program_prefix_l (hKP : M.Models KP) {T ω n F L c G : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (snoc : Snoc_d (kp_pair_l hKP) F L c G) :
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
theorem finiteTruth_snoc_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L c G K r f : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (extended : BoundedFormula_d T ω n K G) (succ : M.SuccessorOf K L)
    (snoc : Snoc_d (kp_pair_l (ZF.modelsKP hZF)) F L c G) (hr : M.mem r L) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive T ω n X G K r f :=
  finiteTruth_prefix_l hZF positive hω valid extended
    (fun i hi => (succ i).mpr (Or.inl hi)) (snoc_program_prefix_l (ZF.modelsKP hZF) valid snoc) hr

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
