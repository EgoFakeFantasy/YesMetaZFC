import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteAssignmentSpace
import YesMetaZFC.SetTheory.InnerModel.Order.Global

/-! # 原 Jensen 层中的统一有限赋值空间

原层的有序微层覆盖直接给出共同传递容器，消去抽象 rud 闭包定理中的额外
容器前提。只要求原 J 层包含所用的内部 ω 和字母表，不要求它可容许。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

/-- 已包含内部 ω 与对象域的原 J 层包含所有内部有限赋值空间。 -/
theorem jh_finite_functionSpace_l (hZF : M.Models ZF) {a C ω X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hXC : M.mem X C) :
    ∀ n, M.mem n ω → ∃ E, M.mem E C ∧
      M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X := by
  let hM := ZF.models_kpi_l hZF
  have hC := jh_value_closed_l hM ha h
  have access := js_rep_access_l hM hC (jh_order_rep_l hM ha h)
  obtain ⟨b, A, R, hb, hAR, hAC, hωA, hXA⟩ :=
    js_access_pair_l hM (access ω hωC) (access X hXC)
  exact YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.rd_finite_functionSpace_l hZF hC (jh_value_transitive_l hM h)
    hAC (js_coherence_l hM hb hAR).1 hω hωA hXA

private def jensenFiniteSpaceBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 3)) <| .imp (jh_value_m (.bound 3) (.bound 2)) <|
      .imp (Formula.isOmega (.bound 1)) <| .imp (.mem (.bound 1) (.bound 2)) <|
        .imp (.mem .newest (.bound 2)) <| Formula.forallMem (.bound 1) <|
          YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.finiteSpace_m (.bound 3) .newest (.bound 1)

/-- 统一量化全部内部自然数的原 Jensen 层对象句子。 -/
def jensenFiniteAssignmentSpaces : Sentence := .ofFormula jensenFiniteSpaceBody
  (by simp -implicitDefEqProofs [jensenFiniteSpaceBody, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed])

theorem jensenFiniteAssignmentSpaces_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenFiniteAssignmentSpaces := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0) jensenFiniteSpaceBody
  simp only [jensenFiniteSpaceBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forallMem_iff, KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.finiteSpace_sat_l (ZF.modelsKP hZF)]
  intro a C ω X ha h hω hωC hXC n hn
  exact jh_finite_functionSpace_l hZF ha h hω hωC hXC n hn

/-- 原 ZF 推导核中的 J 层统一有限赋值空间定理。 -/
theorem jensenFiniteAssignmentSpaces_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenFiniteAssignmentSpaces :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenFiniteAssignmentSpaces_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
