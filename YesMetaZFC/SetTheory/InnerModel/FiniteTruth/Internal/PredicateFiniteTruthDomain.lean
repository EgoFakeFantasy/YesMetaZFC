import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruth

/-! # 谓词真值的传递域选择独立性及准确函数赋值域 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem pcertifiedTruth_domain_choice_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X Y E G F L r f : M.Domain} (hx : M.TransitiveSet X) (hy : M.TransitiveSet Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : PBoundedFormula_d T ω n L F) (hr : M.mem r L) (hfE : M.mem f E) (hfG : M.mem f G) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ PCertifiedTruth_d positive T A n Y G F L r f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Z,hZ⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) X Y
  obtain ⟨Q,hQ⟩ := ZF.exists_functionSpace hZF I n Z
  have xz : M.MemberSubset X Z := fun x hx => (hZ x).mpr (Or.inl hx)
  have yz : M.MemberSubset Y Z := fun y hy => (hZ y).mpr (Or.inr hy)
  exact (pcertifiedTruth_domain_l hZF positive hx xz he hQ valid hr hfE).trans
    (pcertifiedTruth_domain_l hZF positive hy yz hg hQ valid hr hfG).symm

theorem pfiniteTruth_value_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X E F L Z H r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (full : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (check : PtruthCheck_d T A n X E F L Z H) (hf : M.mem f E) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ BtruthAnswer_d positive H r f := by
  exact (pfiniteTruth_space_l hZF positive hω valid.variables full).trans
    ((and_congr_right fun _ => pcertifiedTruth_value_l hZF positive valid check).trans (and_iff_right hf))

theorem pfiniteTruth_domain_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X Y F L r f : M.Domain}
    (hω : M.IsOmega ω) (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (valid : PBoundedFormula_d T ω n L F) (hr : M.mem r L)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive T A ω n Y F L r f := by
  obtain ⟨E,he⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  obtain ⟨G,hg⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n Y
  have hfE := (he f).mpr fn
  have hfG := functionSpace_inclusion_l (kp_pair_l (ZF.modelsKP hZF)) sub he hg f hfE
  rw [pfiniteTruth_space_l hZF positive hω valid.variables he,pfiniteTruth_space_l hZF positive hω valid.variables hg]
  simpa only [hfE,hfG,true_and] using pcertifiedTruth_domain_l hZF positive hx sub he hg valid hr hfE

theorem pfiniteTruth_domain_choice_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X Y F L r f : M.Domain}
    (hω : M.IsOmega ω) (hx : M.TransitiveSet X) (hy : M.TransitiveSet Y)
    (valid : PBoundedFormula_d T ω n L F) (hr : M.mem r L)
    (fx : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (fy : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n Y) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive T A ω n Y F L r f := by
  obtain ⟨E,he⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  obtain ⟨G,hg⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n Y
  have hfE := (he f).mpr fx
  have hfG := (hg f).mpr fy
  rw [pfiniteTruth_space_l hZF positive hω valid.variables he,pfiniteTruth_space_l hZF positive hω valid.variables hg]
  simpa only [hfE,hfG,true_and] using pcertifiedTruth_domain_choice_l hZF positive hx hy he hg valid hr hfE hfG

/-- 正负源的并域恰为真实函数赋值，不把载体成员当作函数。 -/
theorem pfiniteTruth_assignment_iff_l (hZF : M.Models ZF) {T A ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F) :
    (PFiniteTruth_d true T A ω n X F L r f ∨ PFiniteTruth_d false T A ω n X F L r f) ↔
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X := by
  constructor
  · exact fun hit => hit.elim (pfiniteTruth_function_l hZF true hω) (pfiniteTruth_function_l hZF false hω)
  · intro fn
    classical
    by_cases pos : PFiniteTruth_d true T A ω n X F L r f
    · exact Or.inl pos
    · exact Or.inr ((pfiniteTruth_complement_l hZF hω valid fn).mpr pos)

theorem pfiniteTruth_not_both_l (hZF : M.Models ZF) {T A ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F) :
    ¬ (PFiniteTruth_d true T A ω n X F L r f ∧ PFiniteTruth_d false T A ω n X F L r f) := by
  rintro ⟨pos,neg⟩
  exact (pfiniteTruth_complement_l hZF hω valid (pfiniteTruth_function_l hZF true hω pos)).mp neg pos

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
