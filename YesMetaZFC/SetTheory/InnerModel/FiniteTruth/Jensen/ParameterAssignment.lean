import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignment
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.WitnessFiber

/-! # 规范完整参数赋值的原 J 层预算 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_parameterCheck_l (hZF : M.Models ZF) {α C ω k n X a z : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) (hXC : M.mem X C)
    (hn : M.mem n ω) (kn : M.mem k n) (zero : Num_d 0 z) (hz : M.mem z X) (ha : Fn0_d k X a) :
    ∃ f, M.mem f C ∧ ParameterCheck_d ω k n X a z f := by
  obtain ⟨f,cert⟩ := parameterCheck_exists_l hZF hω hn kn zero hz ha
  exact ⟨f,jh_finite_function_mem_l hZF hα h hω hωC hXC hn (fn0_function_l (ZF.modelsKP hZF) cert.full),cert⟩

/-- 旧求值域不必在层内；给定层内参数列即可重新选择同层公共传递域。 -/
theorem jh_parameterDomain_l (hZF : M.Models ZF) {α C ω k n X a z : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) (haC : M.mem a C)
    (hn : M.mem n ω) (kn : M.mem k n) (zero : Num_d 0 z) (ha : Fn0_d k X a) :
    ∃ Y f, M.mem Y C ∧ M.TransitiveSet Y ∧ M.mem f C ∧ ParameterCheck_d ω k n Y a z f := by
  have hzC := jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC z (num_mem_l hZF.1 hω zero)
  obtain ⟨Y,hYC,hy,haY,hzY⟩ := jh_assignmentDomain_withValue_l hZF hα h haC hzC (fn0_function_l (ZF.modelsKP hZF) ha)
  obtain ⟨f,hfC,cert⟩ := jh_parameterCheck_l hZF hα h hω hωC hYC hn kn zero hzY (fn0_of_function_l (ZF.modelsKP hZF) haY)
  exact ⟨Y,f,hYC,hy,hfC,cert⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
