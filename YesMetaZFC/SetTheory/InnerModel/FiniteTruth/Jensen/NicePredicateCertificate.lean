import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolemCertificate

/-! # 标准索引实际函数的正式谓词及 Σ₁ 证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

theorem indexPacket_predicate_l : PredicateDelta0 (3 : Fin 5) indexPacket_s.matrix.body := by
  apply predicateUseCheck_sound_l indexPacket_s.matrix.delta0 (3 : Fin 5)
  rfl

theorem nicePredicateSkolem_predicate_l : PredicateDelta0 (3 : Fin 5) nicePredicateSkolem_s.matrix.body :=
  comp_predicate_l indexPacket_s predicateParameterSkolem_s indexPacket_predicate_l predicateParameterSkolem_predicate_l

theorem nicePredicateSkolem_sigma1_l : nicePredicateSkolem_s.schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
