import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateUniformization
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.LevySubstitution

/-! # 原 ZF 中同一规范选择器的完整局部统一选择模式

源只携带原参数；C 只出现于背景规格，不充当自身层内参数。
谓词解释由实际原矩阵的 PredicateDelta0 证书另行核验。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

private def uniformizationParams (n offset : Nat) : Fin n → Term (n+offset) :=
  fun i => .bound ⟨i.val+offset,by omega⟩

private def canonicalWithinUniformizationBody {n} (φ : S1_binary n) : Formula 1 n :=
  .forallE <| .forallE <| .imp (KP.ord0_m (.bound 1)) <| .imp (jh_value_m (.bound 1) .newest)
    (localUniformizes_m φ (canonicalPick_s φ) (uniformizationParams n 2) .newest)

def canonicalWithinUniformizationSentence {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (canonicalWithinUniformizationBody φ)
    (by simp -implicitDefEqProofs [canonicalWithinUniformizationBody,Definitional.Formula.FreeClosed,uniformizationParams])

theorem canonicalWithinUniformization_models {n} (φ : S1_binary n)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalWithinUniformizationSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0)
    (Formula.forallClosure n (canonicalWithinUniformizationBody φ))
  apply (Formula.satisfies_forallClosure_iff free (canonicalWithinUniformizationBody φ)).mpr
  intro b
  let ρ : Env M n := ⟨b,free⟩
  change Formula.satisfies ρ (canonicalWithinUniformizationBody φ)
  simp only [canonicalWithinUniformizationBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,localUniformizes_sat_l hZF.1]
  intro α C hα hC
  change LocalUniformizes_d φ (canonicalPick_s φ) ρ C
  exact jh_canonicalPick_uniformizes_l (ZF.models_kpi_l hZF) hα hC φ ρ

theorem canonicalWithinUniformization_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalWithinUniformizationSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalWithinUniformization_models φ M hM)

theorem predicateSigma1Uniformization_l {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (3 : Fin (p+4)) φ.matrix.body) :
    PredicateDelta0 (3 : Fin (p+4)) (canonicalPick_s φ).matrix.body ∧
      (canonicalPick_s φ).schema.body.IsSigma1 ∧
        YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalWithinUniformizationSentence φ) :=
  ⟨canonicalPick_predicate_l φ useCert,YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _,canonicalWithinUniformization_derives φ⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
