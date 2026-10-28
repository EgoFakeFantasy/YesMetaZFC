import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 无自由空间参数真值解释器的原对象规格

完整空间 E 只出现在与旧解释器比较的规格中，不是新解释器的参数。两个极性
分别有原 ZF 推导；合法赋值的成员条件显式保留在规格里。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

private def truthSpaceIndex (unified : Bool) : Fin 6 → Fin 9 :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases (if unified then 5 else 4)
    (Fin.cases (if unified then 6 else 5) (Fin.cases (if unified then 7 else 6) (fun _ => 8)))))
private def truthSpaceParams (unified : Bool) (i : Fin 6) : Term 9 := .bound (truthSpaceIndex unified i)

private def finiteTruthSpecificationBody (positive : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (Formula.isOmega (.bound 7)) <| .imp (.mem (.bound 6) (.bound 7)) <|
      .imp (Formula.isFunctionSpace kpair_convention_l (.bound 4) (.bound 6) (.bound 5)) <|
        .iff (binary_pred_m (finiteTruth_s positive).schema (truthSpaceParams true) (.bound 1) .newest)
          (.conj (.mem .newest (.bound 4))
            (binary_pred_m (certifiedTruth_s positive).schema (truthSpaceParams false) (.bound 1) .newest))

def finiteTruthSpecification (positive : Bool) : Sentence := .ofFormula (finiteTruthSpecificationBody positive)
  (by simp -implicitDefEqProofs [finiteTruthSpecificationBody,truthSpaceParams,Definitional.Formula.FreeClosed])

theorem finiteTruthSpecification_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (finiteTruthSpecification positive) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (finiteTruthSpecificationBody positive)
  simp only [finiteTruthSpecificationBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_iff_iff,Formula.satisfies_conj_iff,binary_pred_sat_l,
    finiteTruth_sat_l (ZF.modelsKP hZF),certifiedTruth_sat_l (ZF.modelsKP hZF),truthSpaceParams,truthSpaceIndex]
  intro T ω n X E F L r f hω hn full
  exact finiteTruth_space_l hZF positive hω hn full

theorem finiteTruthSpecification_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (finiteTruthSpecification positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => finiteTruthSpecification_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
