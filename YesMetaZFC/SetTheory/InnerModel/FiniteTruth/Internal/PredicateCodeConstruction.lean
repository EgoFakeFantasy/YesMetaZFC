import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedCodeContainer

/-! # 含谓词查询的实际代码扩张、追加及语法容器保持 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem pnode_mono_l {T U ω n r c : M.Domain} (sub : M.MemberSubset T U)
    (node : Pnode_d T ω n r c) : Pnode_d U ω n r c :=
  node.elim (fun old => Or.inl (bnode_mono_l sub old)) (fun query => Or.inr (bcase_mono_l sub 4 query))

theorem PBoundedFormula_d.container_mono_l (hKP : M.Models KP) {T U ω n r F : M.Domain}
    (valid : PBoundedFormula_d T ω n r F) (sub : M.MemberSubset T U) : PBoundedFormula_d U ω n r F := by
  refine ⟨valid.variables,valid.finite,valid.ordinal,
    fn0_of_function_l hKP (function_codomain_mono_l (kp_pair_l hKP) sub (fn0_function_l hKP valid.graph)),?_⟩
  intro i hi c _ hic
  exact pnode_mono_l sub (valid.row i hi c (valid.graph.bound_l hic).2 hic)

theorem PBoundedFormula_d.append_l (hKP : M.Models KP) {T ω arity length F c s : M.Domain}
    (h : PBoundedFormula_d T ω arity length F) (hc : M.mem c T)
    (hnew : Pnode_d T ω arity length c) (hsω : M.mem s ω)
    (hs : M.IsOrdinal s) (hls : M.SuccessorOf s length) :
    ∃ G, PBoundedFormula_d T ω arity s G ∧
      ∀ r d, Rd_entry_d r d G ↔ Rd_entry_d r d F ∨ (r = length ∧ d = c) := by
  let I := kp_pair_l hKP
  have hf := fn0_function_l hKP h.graph
  obtain ⟨G,hg,entries⟩ := Structure.IsSequenceOfLength.exists_append hKP I
    (show M.IsSequenceOfLength I F length from ⟨h.ordinal,hf.1,hf.2.1⟩) hs hls (value := c)
  have fn : M.IsSetFunctionFromTo I G s T := by
    refine ⟨hg.2.1,hg.2.2,?_⟩
    intro r hr
    obtain ⟨d,hd⟩ := (hg.2.2 r).mp hr
    exact ⟨d,((entries r d).mp hd).elim (fun old => (h.graph.bound_l old).2) (fun new => new.2 ▸ hc),hd⟩
  refine ⟨G,⟨h.variables,hsω,hs,fn0_of_function_l hKP fn,?_⟩,entries⟩
  intro r _ d hd hrd
  rcases (entries r d).mp hrd with old | ⟨rfl,rfl⟩
  · exact h.row r (h.graph.bound_l old).1 d hd old
  · exact hnew

theorem PBoundedFormula_d.snoc_l (hKP : M.Models KP) {T ω n L F c s G : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (hc : M.mem c T) (node : Pnode_d T ω n L c)
    (hsω : M.mem s ω) (hs : M.IsOrdinal s) (hls : M.SuccessorOf s L)
    (snoc : Snoc_d (kp_pair_l hKP) F L c G) : PBoundedFormula_d T ω n s G := by
  let I := kp_pair_l hKP
  obtain ⟨K,hK,entries⟩ := valid.append_l hKP hc node hsω hs hls
  obtain ⟨rel,ge⟩ := (snoc_iff_entries_l I (fn0_function_l hKP valid.graph).1.1).mp snoc
  have eq := rel.eq_of_pairMember_iff hKP.1 (fn0_function_l hKP hK.graph).1.1
    (fun r d => (ge r d).trans (entries r d).symm)
  exact eq.symm ▸ hK

theorem ptruthNode_container_l (hKP : M.Models KP) {T U A ω n r c X E H f : M.Domain}
    (sub : M.MemberSubset T U) (valid : Pnode_d T ω n r c) :
    PtruthNode_d T A n X E H c f ↔ PtruthNode_d U A n X E H c f := by
  rcases valid with old | query
  · exact (ptruthNode_legacy_l hKP old).trans ((btruthNode_container_l hKP sub old).trans
      (ptruthNode_legacy_l hKP (bnode_mono_l sub old)).symm)
  · obtain ⟨i,hi,j,hj,k,hk,code,_⟩ := query
    exact (ptruthNode_predicate_l hKP hi hj hk code).trans
      (ptruthNode_predicate_l hKP (sub i hi) (sub j hj) (sub k hk) (bop_mono_l sub 4 code)).symm

theorem ptruthCheck_container_l (hKP : M.Models KP) {T U A ω n X E F L Z H : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    PtruthCheck_d T A n X E F L Z H ↔ PtruthCheck_d U A n X E F L Z H := by
  constructor
  · rintro ⟨fn,check⟩
    refine ⟨fn,fun r hr c _ hrc Y hYZ hY => ?_⟩
    have hc := (valid.graph.bound_l hrc).2
    obtain ⟨bound,row⟩ := check r hr c hc hrc Y hYZ hY
    exact ⟨bound,fun f hf => (row f hf).trans (ptruthNode_container_l hKP sub (valid.row r hr c hc hrc))⟩
  · rintro ⟨fn,check⟩
    refine ⟨fn,fun r hr c hc hrc Y hYZ hY => ?_⟩
    obtain ⟨bound,row⟩ := check r hr c (sub c hc) hrc Y hYZ hY
    exact ⟨bound,fun f hf => (row f hf).trans (ptruthNode_container_l hKP sub (valid.row r hr c hc hrc)).symm⟩

theorem pfiniteTruth_container_l (hKP : M.Models KP) (positive : Bool) {T U A ω n X F L r f : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive U A ω n X F L r f := by
  constructor
  · rintro ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩
    exact ⟨e,s,Z,S,E,V,H,space,hf,(ptruthCheck_container_l hKP valid sub).mp truth,answer⟩
  · rintro ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩
    exact ⟨e,s,Z,S,E,V,H,space,hf,(ptruthCheck_container_l hKP valid sub).mpr truth,answer⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
