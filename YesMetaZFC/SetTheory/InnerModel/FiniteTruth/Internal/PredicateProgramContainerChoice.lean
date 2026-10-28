import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateCodeConstruction
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramContainerChoice

/-! # 五类程序复用通用自然数字段容器的准确运输 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem pnode_rebase_l (hZF : M.Models ZF) {T U ω n r c : M.Domain}
    (hω : M.IsOmega ω) (bound : NaturalInstructionBound_d ω U) (hn : M.mem n ω) (hr : M.mem r ω)
    (node : Pnode_d T ω n r c) : M.mem c U ∧ Pnode_d U ω n r c := by
  rcases node with old | query
  · obtain ⟨hc,rebased⟩ := bnode_rebase_l hZF hω bound hn hr old
    exact ⟨hc,Or.inl rebased⟩
  · obtain ⟨hc,rebased⟩ := bcase_rebase_l hZF hω bound (hω.transitive hZF n hn)
      (fun _ h => h) (fun _ h => h) query
    exact ⟨hc,Or.inr rebased⟩

theorem PBoundedFormula_d.rebase_l (hZF : M.Models ZF) {T U ω n L F : M.Domain}
    (hω : M.IsOmega ω) (bound : NaturalInstructionBound_d ω U)
    (valid : PBoundedFormula_d T ω n L F) : PBoundedFormula_d U ω n L F := by
  have node r c (hrc : Rd_entry_d r c F) := pnode_rebase_l hZF hω bound valid.variables
    (hω.transitive hZF L valid.finite r (valid.graph.bound_l hrc).1) (valid.at_l hrc).2.2
  have fn := fn0_function_l (ZF.modelsKP hZF) valid.graph
  refine ⟨valid.variables,valid.finite,valid.ordinal,fn0_of_function_l (ZF.modelsKP hZF) ⟨fn.1,fn.2.1,?_⟩,?_⟩
  · intro r hr
    obtain ⟨c,_,entry⟩ := fn.2.2 r hr
    exact ⟨c,(node r c entry).1,entry⟩
  · intro r _ c _ entry
    exact (node r c entry).2

theorem pfiniteTruth_container_choice_l (hKP : M.Models KP) (positive : Bool) {T U A ω n X F L r f : M.Domain}
    (validT : PBoundedFormula_d T ω n L F) (validU : PBoundedFormula_d U ω n L F) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive U A ω n X F L r f := by
  obtain ⟨W,hW⟩ := KP.exists_unionOfTwo hKP T U
  have tW : M.MemberSubset T W := fun x hx => (hW x).mpr (Or.inl hx)
  have uW : M.MemberSubset U W := fun x hx => (hW x).mpr (Or.inr hx)
  exact (pfiniteTruth_container_l hKP positive validT tW).trans (pfiniteTruth_container_l hKP positive validU uW).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
