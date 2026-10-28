import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramContainerChoice
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateProgramCode
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramContainer

/-! # 五类程序在同一原 J 层中的统一容器 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pboundedProgram_rebase_l (hZF : M.Models ZF) {α C T ω n L F : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (valid : PBoundedFormula_d T ω n L F) :
    ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ PBoundedFormula_d U ω n L F := by
  obtain ⟨U,hUC,hu,bound⟩ := jh_naturalInstructionBound_l hZF hα h hω hωC
  exact ⟨U,hUC,hu,valid.rebase_l hZF hω bound⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
