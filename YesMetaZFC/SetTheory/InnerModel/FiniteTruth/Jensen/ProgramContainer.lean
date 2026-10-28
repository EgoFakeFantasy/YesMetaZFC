import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramContainerChoice
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramCode
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruth

/-! # 同一 J 层中的统一语法容器及赋值求值域 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 仅由内部 ω 构造一个同层容器，同时容纳所有内部合法四字段指令。 -/
theorem jh_naturalInstructionBound_l (hZF : M.Models ZF) {α C ω : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ NaturalInstructionBound_d ω U := by
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  obtain ⟨A,hAC,ha,oa,pa⟩ := rd_kpair_bound_l (ZF.modelsKP hZF) closed hωC (hω.isOrdinal hZF).transitive
  obtain ⟨B,hBC,hb,ab,pb⟩ := rd_kpair_bound_l (ZF.modelsKP hZF) closed hAC ha
  obtain ⟨U,hUC,hu,bu,pu⟩ := rd_kpair_bound_l (ZF.modelsKP hZF) closed hBC hb
  refine ⟨U,hUC,hu,fun x hx => bu x (ab x (oa x hx)),?_⟩
  intro t i j k v c ht hi hj hk trip pair
  obtain ⟨q,hq,hv⟩ := trip
  have hqA := pa j k q hj hk hq
  have hvB := pb i q v (oa i hi) hqA hv
  exact ⟨bu v hvB,pu t v c (ab t (oa t ht)) hvB pair⟩

/-- 任意合法原程序可迁入上述同层容器，旧语法容器无需属于该层。 -/
theorem jh_boundedProgram_rebase_l (hZF : M.Models ZF) {α C T ω n L F : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (valid : BoundedFormula_d T ω n L F) :
    ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ BoundedFormula_d U ω n L F := by
  obtain ⟨U,hUC,hu,bound⟩ := jh_naturalInstructionBound_l hZF hα h hω hωC
  exact ⟨U,hUC,hu,valid.rebase_l hZF hω bound⟩

/-- 层内实际赋值有层内传递求值域；先取真实值域，再取该值域的包络。 -/
theorem jh_assignmentDomain_l (hZF : M.Models ZF) {α C n f X : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hfC : M.mem f C)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    ∃ Y, M.mem Y C ∧ M.TransitiveSet Y ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n Y := by
  obtain ⟨A,hAC,hA⟩ := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h).exists_l (ZF.modelsKP hZF) .range hfC hfC hfC
  obtain ⟨Y,hYC,hy,hAY⟩ := jh_local_enclosure_l (ZF.models_kpi_l hZF) hα h A hAC
  refine ⟨Y,hYC,hy,hf.1,hf.2.1,?_⟩
  intro r hr
  obtain ⟨x,_,hrx⟩ := hf.2.2 r hr
  exact ⟨x,hy A hAY x ((hA x).mpr ⟨r,hrx⟩),hrx⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
