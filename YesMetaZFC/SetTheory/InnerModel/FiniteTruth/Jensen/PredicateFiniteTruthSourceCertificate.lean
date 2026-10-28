import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFiniteTruthObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTruthSourceCertificate

/-! # 消去自由空间参数后的实际谓词证书与同一原选择器 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem pfiniteTruth_predicate_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 10) (pfiniteTruth_s positive).matrix.body := by
  apply predicateUseCheck_sound_l (pfiniteTruth_s positive).matrix.delta0 (3 : Fin 10)
  cases positive <;> rfl

theorem predicateFiniteUniformization_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 10) (canonicalPick_s (pfiniteTruth_s positive)).matrix.body ∧
      (canonicalPick_s (pfiniteTruth_s positive)).schema.body.IsSigma1 ∧
        YesMetaZFC.SetTheory.Definitional.Project.Derives ZF
          (canonicalWithinUniformizationSentence (pfiniteTruth_s positive)) :=
  predicateSigma1Uniformization_l (pfiniteTruth_s positive) (pfiniteTruth_predicate_l positive)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
