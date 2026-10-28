import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthDomain
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

private def predicateTruthDomainBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
      .imp (Formula.isTransitive (.bound 9)) <| .imp (Formula.subset (.bound 9) (.bound 8)) <|
        .imp (Formula.isFunctionSpace kpair_convention_l (.bound 7) (.bound 10) (.bound 9)) <|
          .imp (Formula.isFunctionSpace kpair_convention_l (.bound 6) (.bound 10) (.bound 8)) <|
            .imp (pboundedFormula_m (.bound 13) (.bound 11) (.bound 10) (.bound 4) (.bound 5)) <|
              .imp (ptruthCheck_m (.bound 13) (.bound 12) (.bound 10) (.bound 9) (.bound 7) (.bound 5) (.bound 4) (.bound 3) (.bound 2)) <|
                .imp (ptruthCheck_m (.bound 13) (.bound 12) (.bound 10) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest) <|
                  Formula.forallMem (.bound 4) (btruthAgreement_m (.bound 8) (.bound 3) (.bound 1) .newest)

/-- 整张原历史在旧完整赋值空间上的跨域保值。 -/
def predicateTruthDomain : Sentence := .ofFormula predicateTruthDomainBody
  (by simp -implicitDefEqProofs [predicateTruthDomainBody, Definitional.Formula.FreeClosed])

theorem predicateTruthDomain_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateTruthDomain := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0, envFree⟩ : Env M 0) predicateTruthDomainBody
  simp only [predicateTruthDomainBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    pboundedFormula_sat_l (ZF.modelsKP hZF), ptruthCheck_sat_l hZF.1,
    Formula.satisfies_forallMem_iff, btruthAgreement_sat_l hZF.1]
  intro T A ω n X Y E G F L Z H W J hx sub he hg valid hH hJ
  exact ptruthCertificate_domain_l hZF hx sub he hg valid hH hJ

theorem predicateTruthDomain_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateTruthDomain :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => predicateTruthDomain_models M hM)


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
