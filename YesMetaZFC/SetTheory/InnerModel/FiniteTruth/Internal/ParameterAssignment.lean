import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignmentSyntax
import YesMetaZFC.SetTheory.Descriptive.TreeCons

/-! # 规范参数赋值的存在、唯一性与域无关性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem parameterSlot_range_l {k X a z r y : M.Domain} (ha : Fn0_d k X a) (hz : M.mem z X)
    (slot : ParameterSlot_d k a z r y) : M.mem y X := by
  rcases slot with ⟨j,_,_,entry⟩ | ⟨_,rfl⟩
  · exact (ha.bound_l entry).2
  · exact hz

theorem parameterSlot_total_l (hKP : M.Models KP) {k X a z : M.Domain}
    (ha : Fn0_d k X a) (hz : M.mem z X) (r : M.Domain) : ∃ y, M.mem y X ∧ ParameterSlot_d k a z r y := by
  classical
  by_cases index : ParameterIndex_d k r
  · obtain ⟨j,hj,hs⟩ := index
    obtain ⟨y,hy,entry⟩ := (fn0_function_l hKP ha).2.2 j hj
    exact ⟨y,hy,Or.inl ⟨j,hj,hs,entry⟩⟩
  · exact ⟨z,hz,Or.inr ⟨index,rfl⟩⟩

theorem parameterSlot_unique_l (hKP : M.Models KP) {k X a z r y t : M.Domain}
    (hk : M.IsOrdinal k) (ha : Fn0_d k X a) (hy : ParameterSlot_d k a z r y) (ht : ParameterSlot_d k a z r t) : y = t := by
  rcases hy with ⟨j,hj,hs,entry⟩ | ⟨none,eq⟩ <;> rcases ht with ⟨j',hj',hs',entry'⟩ | ⟨none',eq'⟩
  · have eq := Structure.SuccessorOf.predecessor_eq hKP.1 (hk.mem hj) hs hs'
    subst j'
    exact (fn0_function_l hKP ha).1.2 j y t entry entry'
  · exact (none' ⟨j,hj,hs⟩).elim
  · exact (none ⟨j',hj',hs'⟩).elim
  · exact eq.trans eq'.symm

theorem parameterCheck_exists_l (hZF : M.Models ZF) {ω k n X a z : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (kn : M.mem k n) (zero : Num_d 0 z)
    (hz : M.mem z X) (ha : Fn0_d k X a) : ∃ f, ParameterCheck_d ω k n X a z f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases a (fun _ => k)),fun _ => z⟩
  let φ : BinarySchema 3 := { body := parameterSlot_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp r y : φ.denote ρ r y ↔ ParameterSlot_d k a z r y := by
    simp only [φ,BinarySchema.denote,parameterSlot_sat_l hZF.1]
    rfl
  have hk := (hω.members_areOrdinals hZF n hn).mem kn
  obtain ⟨f,hf,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := X)
    (fun r _ => by
      obtain ⟨y,_,slot⟩ := parameterSlot_total_l (ZF.modelsKP hZF) ha hz r
      exact ⟨y,(hp r y).mpr slot⟩)
    (fun r _ y t hy ht => parameterSlot_unique_l (ZF.modelsKP hZF) hk ha ((hp r y).mp hy) ((hp r t).mp ht))
    (fun r y _ hy => parameterSlot_range_l ha hz ((hp r y).mp hy))
  exact ⟨f,hn,kn,zero,hz,ha,fn0_of_function_l (ZF.modelsKP hZF) hf,fun r hr y _ =>
    (entries r y).trans ⟨fun h => (hp r y).mp h.2,fun slot => ⟨hr,(hp r y).mpr slot⟩⟩⟩

/-- 完整规范图在两个任意容器中唯一相同，包括所有占位和闲置槽。 -/
theorem ParameterCheck_d.unique_l (hKP : M.Models KP) {ω k n X Y a z z' f g : M.Domain}
    (left : ParameterCheck_d ω k n X a z f) (right : ParameterCheck_d ω k n Y a z' g) : f = g := by
  have eq := num_unique_l hKP.1 left.zero right.zero
  subst z'
  have ff := fn0_function_l hKP left.full
  have gg := fn0_function_l hKP right.full
  apply ff.1.1.eq_of_pairMember_iff hKP.1 gg.1.1
  intro r y
  constructor
  · intro entry
    have hr := ff.input_mem_of_pairMember entry
    have slot := (left.row r hr y (ff.output_mem_of_pairMember entry)).mp entry
    exact (right.row r hr y (parameterSlot_range_l right.parameters right.inhabited slot)).mpr slot
  · intro entry
    have hr := gg.input_mem_of_pairMember entry
    have slot := (right.row r hr y (gg.output_mem_of_pairMember entry)).mp entry
    exact (left.row r hr y (parameterSlot_range_l left.parameters left.inhabited slot)).mpr slot

/-- 更换包含同一参数值及空值的任意容器，原完整赋值图保持不变。 -/
theorem ParameterCheck_d.domain_l (hKP : M.Models KP) {ω k n X Y a z f : M.Domain}
    (cert : ParameterCheck_d ω k n X a z f) (parameters : Fn0_d k Y a) (hz : M.mem z Y) :
    ParameterCheck_d ω k n Y a z f := by
  have ff := fn0_function_l hKP cert.full
  have fullY : M.IsSetFunctionFromTo (kp_pair_l hKP) f n Y := by
    refine ⟨ff.1,ff.2.1,fun r hr => ?_⟩
    obtain ⟨y,hy,entry⟩ := ff.2.2 r hr
    exact ⟨y,parameterSlot_range_l parameters hz ((cert.row r hr y hy).mp entry),entry⟩
  refine ⟨cert.finite,cert.capacity,cert.zero,hz,parameters,fn0_of_function_l hKP fullY,fun r hr y _ => ?_⟩
  constructor
  · intro entry
    exact (cert.row r hr y (ff.output_mem_of_pairMember entry)).mp entry
  · intro slot
    exact (cert.row r hr y (parameterSlot_range_l cert.parameters cert.inhabited slot)).mpr slot

theorem ParameterCheck_d.zero_l (hZF : M.Models ZF) {ω k n X a z f : M.Domain}
    (hω : M.IsOmega ω) (cert : ParameterCheck_d ω k n X a z f) : M.mem z n ∧ Rd_entry_d z z f := by
  have hz := Structure.IsOrdinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
    (hω.members_areOrdinals hZF n cert.finite) ⟨k,cert.capacity⟩ cert.zero
  exact ⟨hz,(cert.row z hz z cert.inhabited).mpr (Or.inr ⟨fun ⟨j,_,hs⟩ => cert.zero j hs.predecessor_mem,rfl⟩)⟩

theorem ParameterCheck_d.shift_l (hZF : M.Models ZF) {ω k n X a z f j r y : M.Domain}
    (hω : M.IsOmega ω) (cert : ParameterCheck_d ω k n X a z f)
    (hj : M.mem j k) (hs : M.SuccessorOf r j) (entry : Rd_entry_d j y a) : M.mem r n ∧ Rd_entry_d r y f := by
  have hkω := hω.transitive hZF n cert.finite k cert.capacity
  have hr : M.mem r n := (Descriptive.tree_successor_le_l hZF hω hkω hj hs).elim
    (fun eq => eq.symm ▸ cert.capacity)
    (fun h => (hω.members_areOrdinals hZF n cert.finite).transitive k cert.capacity r h)
  exact ⟨hr,(cert.row r hr y (cert.parameters.bound_l entry).2).mpr (Or.inl ⟨j,hj,hs,entry⟩)⟩

theorem ParameterCheck_d.idle_l {ω k n X a z f r : M.Domain}
    (cert : ParameterCheck_d ω k n X a z f) (hr : M.mem r n) (idle : ¬ ParameterIndex_d k r) : Rd_entry_d r z f :=
  (cert.row r hr z cert.inhabited).mpr (Or.inr ⟨idle,rfl⟩)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
