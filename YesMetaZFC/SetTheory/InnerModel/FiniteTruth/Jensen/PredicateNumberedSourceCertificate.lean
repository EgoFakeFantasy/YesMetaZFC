import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFiniteTruthSourceCertificate

/-! # 数码真值双参数源的正式谓词证书及同一规范选择器 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem pnumberedTruth_predicate_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 5) (pnumberedTruth_s positive).matrix.body := by
  apply predicateUseCheck_sound_l (pnumberedTruth_s positive).matrix.delta0 (3 : Fin 5)
  cases positive <;> rfl

theorem predicateNumberedUniformization_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 5) (canonicalPick_s (pnumberedTruth_s positive)).matrix.body ∧
      (canonicalPick_s (pnumberedTruth_s positive)).schema.body.IsSigma1 ∧
        YesMetaZFC.SetTheory.Definitional.Project.Derives ZF
          (canonicalWithinUniformizationSentence (pnumberedTruth_s positive)) :=
  predicateSigma1Uniformization_l (pnumberedTruth_s positive) (pnumberedTruth_predicate_l positive)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
