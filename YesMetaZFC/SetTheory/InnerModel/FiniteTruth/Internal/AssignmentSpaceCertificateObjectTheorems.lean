import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 完整赋值空间证书及 Σ₁ 正规形的原对象推导

存在性、完整性和正规形等价性分别回到原 ZF 推导核。证书的传递层绝对性
不假设小层 KP；整张空间表及其证书对象的同 J 层存在性仍须另证。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

/-- 完整有界核验在任意内部传递子结构中准确。 -/
theorem assignmentSpaceCert_local_l {M : SetTheory.Structure.{u}} (hE : Extensional M)
    {C : M.Domain} (hc : M.TransitiveSet C) (hn : Nonempty {x : M.Domain // M.mem x C})
    (ω n X e s Z S E : (rt_model_l C hn).Domain) :
    AssignmentSpaceCert_d ω n X e s Z S E ↔
      AssignmentSpaceCert_d ω.val n.val X.val e.val s.val Z.val S.val E.val := by
  let ρ : Env (rt_model_l C hn) 8 :=
    ⟨Fin.cases ω (Fin.cases n (Fin.cases X (Fin.cases e (Fin.cases s
      (Fin.cases Z (Fin.cases S (fun _ => E))))))), fun _ => ω⟩
  exact (assignmentSpaceCert_sat_l (rt_model_ext_l hE hc hn) ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).symm.trans
    ((rt_model_delta_l hc hn (assignmentSpaceCert_delta_l _ _ _ _ _ _ _ _) ρ).trans
      (assignmentSpaceCert_sat_l hE (image_env_l Subtype.val ρ)
        (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)))

private def assignmentSpaceCertifiedBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .imp (Formula.isOmega (.bound 2)) <|
    .imp (.mem (.bound 1) (.bound 2)) <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
      assignmentSpaceCert_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

def assignmentSpaceCertified : Sentence := .ofFormula assignmentSpaceCertifiedBody
  (by simp -implicitDefEqProofs [assignmentSpaceCertifiedBody, Definitional.Formula.FreeClosed])

theorem assignmentSpaceCertified_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence assignmentSpaceCertified := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) assignmentSpaceCertifiedBody
  simp only [assignmentSpaceCertifiedBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    assignmentSpaceCert_sat_l hZF.1]
  exact fun ω n X hω hn => assignmentSpaceCert_exists_l hZF hω hn X

theorem assignmentSpaceCertified_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF assignmentSpaceCertified :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => assignmentSpaceCertified_models M hM)

private def assignmentSpaceSoundBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (Formula.isOmega (.bound 7)) <|
      .imp (assignmentSpaceCert_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
        (Formula.isFunctionSpace kpair_convention_l .newest (.bound 6) (.bound 5))

def assignmentSpaceCertificateSound : Sentence := .ofFormula assignmentSpaceSoundBody
  (by simp -implicitDefEqProofs [assignmentSpaceSoundBody, Definitional.Formula.FreeClosed])

theorem assignmentSpaceCertificateSound_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence assignmentSpaceCertificateSound := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) assignmentSpaceSoundBody
  simp only [assignmentSpaceSoundBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isOmega_iff, assignmentSpaceCert_sat_l hZF.1,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1]
  exact fun ω n X e s Z S E hω cert => assignmentSpaceCert_sound_l hZF hω cert

theorem assignmentSpaceCertificateSound_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF assignmentSpaceCertificateSound :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => assignmentSpaceCertificateSound_models M hM)

private def spaceNormIndices : Fin 2 → Fin 4 := Fin.cases 1 (fun _ => 3)
private def spaceNormParams (i : Fin 2) : Term 4 := .bound (spaceNormIndices i)

private def finiteFunctionSpaceSigma1Body : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .imp (Formula.isOmega (.bound 3)) <|
    .imp (.mem (.bound 2) (.bound 3)) <|
      .iff (Formula.isFunctionSpace kpair_convention_l .newest (.bound 2) (.bound 1))
        (binary_pred_m assignmentSpace_s.schema spaceNormParams (.bound 2) .newest)

def finiteFunctionSpaceSigma1 : Sentence := .ofFormula finiteFunctionSpaceSigma1Body
  (by simp -implicitDefEqProofs [finiteFunctionSpaceSigma1Body, spaceNormParams, Definitional.Formula.FreeClosed])

theorem finiteFunctionSpaceSigma1_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence finiteFunctionSpaceSigma1 := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) finiteFunctionSpaceSigma1Body
  simp only [finiteFunctionSpaceSigma1Body, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    binary_pred_sat_l, assignmentSpace_sat_l (ZF.modelsKP hZF), spaceNormParams, spaceNormIndices]
  intro ω n X E hω hn
  exact ⟨assignmentSpaceCert_for_space_l hZF hω hn,
    fun ⟨_,_,_,_,cert⟩ => assignmentSpaceCert_sound_l hZF hω cert⟩

theorem finiteFunctionSpaceSigma1_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF finiteFunctionSpaceSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => finiteFunctionSpaceSigma1_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
