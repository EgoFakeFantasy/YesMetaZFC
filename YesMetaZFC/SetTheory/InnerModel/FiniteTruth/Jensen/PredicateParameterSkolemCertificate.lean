import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateWitnessSourceCertificate

/-! # 唯一规范化和实际复合函数的正式谓词及 Σ₁ 证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem pnormalizedInput_predicate_l : PredicateDelta0 (3 : Fin 5) pnormalizedInput_s.matrix.body := by
  apply predicateUseCheck_sound_l pnormalizedInput_s.matrix.delta0 (3 : Fin 5)
  rfl

theorem predicateParameterSkolem_predicate_l :
    PredicateDelta0 (3 : Fin 5) predicateParameterSkolem_s.matrix.body :=
  comp_predicate_l pnormalizedInput_s predicateNumericSkolem_s pnormalizedInput_predicate_l predicateWitnessUniformization_l.1

theorem predicateParameterSkolem_sigma1_l : predicateParameterSkolem_s.schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
