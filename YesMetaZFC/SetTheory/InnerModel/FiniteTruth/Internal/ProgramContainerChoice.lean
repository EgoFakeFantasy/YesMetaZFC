import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedCodeContainer

/-! # 原程序合法性和操作真值的容器选择独立性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 对全部自然数字段的原四字段指令提供共同界；仅作语义构造辅助。 -/
def NaturalInstructionBound_d (ω U : M.Domain) : Prop :=
  M.MemberSubset ω U ∧ ∀ t i j k v c, M.mem t ω → M.mem i ω → M.mem j ω → M.mem k ω →
    Rd_triple_d v i j k → KPair_d M c t v → M.mem v U ∧ M.mem c U

theorem bcase_rebase_l (hZF : M.Models ZF) {T U ω c A B D : M.Domain} {tag : Nat}
    (hω : M.IsOmega ω) (bound : NaturalInstructionBound_d ω U)
    (ha : M.MemberSubset A ω) (hb : M.MemberSubset B ω) (hd : M.MemberSubset D ω)
    (node : Bcase_d T tag c A B D) : M.mem c U ∧ Bcase_d U tag c A B D := by
  obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,trip,pair⟩,hi,hj,hk⟩ := node
  have ti := num_mem_l hZF.1 hω ht
  obtain ⟨hv,hc⟩ := bound.2 t i j k v c ti (ha i hi) (hb j hj) (hd k hk) trip pair
  exact ⟨hc,i,bound.1 i (ha i hi),j,bound.1 j (hb j hj),k,bound.1 k (hd k hk),
    ⟨t,bound.1 t ti,v,hv,ht,trip,pair⟩,hi,hj,hk⟩

theorem bnode_rebase_l (hZF : M.Models ZF) {T U ω n r c : M.Domain}
    (hω : M.IsOmega ω) (bound : NaturalInstructionBound_d ω U) (hn : M.mem n ω) (hr : M.mem r ω)
    (node : Bnode_d T ω n r c) : M.mem c U ∧ Bnode_d U ω n r c := by
  have nn := hω.transitive hZF n hn
  have rr := hω.transitive hZF r hr
  rcases node with node | node | node | node
  · obtain ⟨hc,node⟩ := bcase_rebase_l hZF hω bound nn nn (fun _ h => h) node
    exact ⟨hc,Or.inl node⟩
  · obtain ⟨hc,node⟩ := bcase_rebase_l hZF hω bound nn nn (fun _ h => h) node
    exact ⟨hc,Or.inr (Or.inl node)⟩
  · obtain ⟨hc,node⟩ := bcase_rebase_l hZF hω bound rr rr (fun _ h => h) node
    exact ⟨hc,Or.inr (Or.inr (Or.inl node))⟩
  · obtain ⟨hc,node⟩ := bcase_rebase_l hZF hω bound nn nn rr node
    exact ⟨hc,Or.inr (Or.inr (Or.inr node))⟩

theorem BoundedFormula_d.rebase_l (hZF : M.Models ZF) {T U ω n L F : M.Domain}
    (hω : M.IsOmega ω) (bound : NaturalInstructionBound_d ω U)
    (valid : BoundedFormula_d T ω n L F) : BoundedFormula_d U ω n L F := by
  have node r c (hrc : Rd_entry_d r c F) := bnode_rebase_l hZF hω bound valid.variables
    (hω.transitive hZF L valid.finite r (valid.graph.bound_l hrc).1) (valid.at_l hrc).2.2
  have ff := fn0_function_l (ZF.modelsKP hZF) valid.graph
  refine ⟨valid.variables,valid.finite,valid.ordinal,fn0_of_function_l (ZF.modelsKP hZF) ⟨ff.1,ff.2.1,?_⟩,?_⟩
  · intro r hr
    obtain ⟨c,_,hrc⟩ := ff.2.2 r hr
    exact ⟨c,(node r c hrc).1,hrc⟩
  · intro r _ c _ hrc
    exact (node r c hrc).2

/-- 两个互不包含的合法语法容器也给出相同的正负操作真值。 -/
theorem finiteTruth_container_choice_l (hKP : M.Models KP) (positive : Bool) {T U ω n X F L r f : M.Domain}
    (validT : BoundedFormula_d T ω n L F) (validU : BoundedFormula_d U ω n L F) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive U ω n X F L r f := by
  obtain ⟨W,hW⟩ := KP.exists_unionOfTwo hKP T U
  have tW : M.MemberSubset T W := fun x hx => (hW x).mpr (Or.inl hx)
  have uW : M.MemberSubset U W := fun x hx => (hW x).mpr (Or.inr hx)
  exact (finiteTruth_container_l hKP positive validT tW).trans (finiteTruth_container_l hKP positive validU uW).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
