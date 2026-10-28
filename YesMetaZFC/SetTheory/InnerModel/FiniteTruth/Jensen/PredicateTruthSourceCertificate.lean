import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.PredicateSourceCheck
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTruthObjectTheorems

/-! # 统一内部谓词程序之同一原 Σ₁ 源的正式谓词证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem pcertifiedTruth_predicate_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 10) (pcertifiedTruth_s positive).matrix.body := by
  apply predicateUseCheck_sound_l (pcertifiedTruth_s positive).matrix.delta0 (3 : Fin 10)
  cases positive <;> rfl

theorem predicateProgramUniformization_l (positive : Bool) :
    PredicateDelta0 (3 : Fin 10) (canonicalPick_s (pcertifiedTruth_s positive)).matrix.body ∧
      (canonicalPick_s (pcertifiedTruth_s positive)).schema.body.IsSigma1 ∧
        YesMetaZFC.SetTheory.Definitional.Project.Derives ZF
          (canonicalWithinUniformizationSentence (pcertifiedTruth_s positive)) :=
  predicateSigma1Uniformization_l (pcertifiedTruth_s positive) (pcertifiedTruth_predicate_l positive)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
