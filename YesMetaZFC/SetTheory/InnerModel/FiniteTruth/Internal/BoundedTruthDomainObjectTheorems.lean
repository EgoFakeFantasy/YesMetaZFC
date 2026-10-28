import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 跨传递求值域语义保持的原对象推导

闭句统一量化全部内部程序、完整赋值空间及历史图。小域传递且包含于大域，
即可保持旧赋值上全部合法行的真值；不使用外部标准长度限制。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

private def boundedTruthDomainBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
      .imp (Formula.isTransitive (.bound 9)) <| .imp (Formula.subset (.bound 9) (.bound 8)) <|
        .imp (Formula.isFunctionSpace kpair_convention_l (.bound 7) (.bound 10) (.bound 9)) <|
          .imp (Formula.isFunctionSpace kpair_convention_l (.bound 6) (.bound 10) (.bound 8)) <|
            .imp (boundedFormula_m (.bound 12) (.bound 11) (.bound 10) (.bound 4) (.bound 5)) <|
              .imp (btruthCheck_m (.bound 12) (.bound 10) (.bound 9) (.bound 7) (.bound 5) (.bound 4) (.bound 3) (.bound 2)) <|
                .imp (btruthCheck_m (.bound 12) (.bound 10) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest) <|
                  Formula.forallMem (.bound 4) (btruthAgreement_m (.bound 8) (.bound 3) (.bound 1) .newest)

/-- 整张原历史在旧完整赋值空间上的跨域保值。 -/
def boundedTruthDomain : Sentence := .ofFormula boundedTruthDomainBody
  (by simp -implicitDefEqProofs [boundedTruthDomainBody, Definitional.Formula.FreeClosed])

theorem boundedTruthDomain_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence boundedTruthDomain := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0, envFree⟩ : Env M 0) boundedTruthDomainBody
  simp only [boundedTruthDomainBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    boundedFormula_sat_l (ZF.modelsKP hZF), btruthCheck_sat_l hZF.1,
    Formula.satisfies_forallMem_iff, btruthAgreement_sat_l hZF.1]
  intro T ω n X Y E G F L Z H W J hx sub he hg valid hH hJ
  exact btruthCertificate_domain_l hZF hx sub he hg valid hH hJ

theorem boundedTruthDomain_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF boundedTruthDomain :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => boundedTruthDomain_models M hM)

private def domainTruthIndex (large : Bool) : Fin 6 → Fin 11 :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases (if large then 4 else 5)
    (Fin.cases (if large then 6 else 7) (Fin.cases 8 (fun _ => 10)))))

private def domainTruthParams (large : Bool) (i : Fin 6) : Term 11 :=
  .bound (domainTruthIndex large i)

private def certifiedTruthDomainBody (positive : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
      .imp (Formula.isTransitive (.bound 7)) <| .imp (Formula.subset (.bound 7) (.bound 6)) <|
        .imp (Formula.isFunctionSpace kpair_convention_l (.bound 5) (.bound 8) (.bound 7)) <|
          .imp (Formula.isFunctionSpace kpair_convention_l (.bound 4) (.bound 8) (.bound 6)) <|
            .imp (boundedFormula_m (.bound 10) (.bound 9) (.bound 8) (.bound 2) (.bound 3)) <|
              .imp (.mem (.bound 1) (.bound 2)) <| .imp (.mem .newest (.bound 5)) <|
                .iff (binary_pred_m (certifiedTruth_s positive).schema (domainTruthParams false) (.bound 1) .newest)
                  (binary_pred_m (certifiedTruth_s positive).schema (domainTruthParams true) (.bound 1) .newest)

/-- 正负两个统一操作真值模板各自的跨域准确性句子。 -/
def certifiedTruthDomain (positive : Bool) : Sentence := .ofFormula (certifiedTruthDomainBody positive)
  (by simp -implicitDefEqProofs [certifiedTruthDomainBody, domainTruthParams, Definitional.Formula.FreeClosed])

theorem certifiedTruthDomain_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (certifiedTruthDomain positive) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0, envFree⟩ : Env M 0) (certifiedTruthDomainBody positive)
  simp only [certifiedTruthDomainBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    boundedFormula_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    binary_pred_sat_l, certifiedTruth_sat_l (ZF.modelsKP hZF), domainTruthParams, domainTruthIndex]
  intro T ω n X Y E G F L r f hx sub he hg valid hr hf
  exact certifiedTruth_domain_l hZF positive hx sub he hg valid hr hf

theorem certifiedTruthDomain_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (certifiedTruthDomain positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => certifiedTruthDomain_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
