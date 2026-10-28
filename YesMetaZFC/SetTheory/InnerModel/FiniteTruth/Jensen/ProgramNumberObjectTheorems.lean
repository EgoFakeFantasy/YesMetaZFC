import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramNumber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 任意合法内部程序及编号的同 J 层对象推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def jensenProgramNumberingBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <|
      .imp (KP.ord0_m (.bound 7)) <| .imp (jh_value_m (.bound 7) (.bound 6)) <|
        .imp (Formula.isOmega (.bound 5)) <| .imp (.mem (.bound 5) (.bound 6)) <|
          .imp (boundedFormula_m (.bound 4) (.bound 5) (.bound 3) (.bound 2) (.bound 1)) <|
            .imp (.mem .newest (.bound 2)) <|
              .conj (.mem (.bound 1) (.bound 6)) <| .existsE <| .existsE <|
                .conj (.mem (.bound 1) (.bound 7)) <|
                  .conj (.mem (.bound 1) (.bound 8)) <| .conj (.mem .newest (.bound 8)) <|
                    .conj (programNumber_m (𝒞 := kpair_convention_l) (.bound 7) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1))
                      (numberedRows_m (𝒞 := kpair_convention_l) (.bound 7) (.bound 4) (.bound 3) .newest)

def jensenProgramNumberingSentence : Sentence := .ofFormula jensenProgramNumberingBody
  (by simp -implicitDefEqProofs [jensenProgramNumberingBody,Definitional.Formula.FreeClosed])

theorem jensenProgramNumbering_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenProgramNumberingSentence := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenProgramNumberingBody
  simp only [jensenProgramNumberingBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,boundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    numberedRows_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1]
  intro a C ω T n L F r ha h hω hωC valid hr
  exact jh_programNumber_l hZF ha h hω hωC valid hr

theorem jensenProgramNumbering_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenProgramNumberingSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenProgramNumbering_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
