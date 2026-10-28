import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumericSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedSourceCertificate

/-! # 实际带参数见证源及同一规范函数的正式谓词证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem pwitnessFiber_predicate_l :
    PredicateDelta0 (3 : Fin 5) pwitnessFiber_s.matrix.body := by
  apply predicateUseCheck_sound_l pwitnessFiber_s.matrix.delta0 (3 : Fin 5)
  rfl

theorem predicateWitnessUniformization_l :
    PredicateDelta0 (3 : Fin 5) predicateNumericSkolem_s.matrix.body ∧
      predicateNumericSkolem_s.schema.body.IsSigma1 ∧
        YesMetaZFC.SetTheory.Definitional.Project.Derives ZF
          (canonicalWithinUniformizationSentence pwitnessFiber_s) :=
  predicateSigma1Uniformization_l pwitnessFiber_s pwitnessFiber_predicate_l

theorem predicateNumericSkolemSpecification_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPickSpecification pwitnessFiber_s) :=
  canonicalPickSpecification_derives pwitnessFiber_s

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
