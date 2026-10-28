import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomainObjectTheorems

/-! # 传递求值域选择的独立性

两个传递域可以互不包含。取二元并及其完整赋值空间作为公共扩张，只比较同一
旧赋值的操作真值。这不把完整赋值空间的存在规格自动转为有界证书。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 同一合法行和赋值的正负真值不依赖所选的传递求值域。 -/
theorem certifiedTruth_domain_choice_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X Y E G F L r f : M.Domain} (hx : M.TransitiveSet X) (hy : M.TransitiveSet Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) (hfE : M.mem f E) (hfG : M.mem f G) :
    CertifiedTruth_d positive T n X E F L r f ↔ CertifiedTruth_d positive T n Y G F L r f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Z, hZ⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) X Y
  obtain ⟨Q, hQ⟩ := ZF.exists_functionSpace hZF I n Z
  have xz : M.MemberSubset X Z := fun x hx => (hZ x).mpr (Or.inl hx)
  have yz : M.MemberSubset Y Z := fun y hy => (hZ y).mpr (Or.inr hy)
  exact (certifiedTruth_domain_l hZF positive hx xz he hQ valid hr hfE).trans
    (certifiedTruth_domain_l hZF positive hy yz hg hQ valid hr hfG).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
