import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomainChoice

/-! # 消去 E 后的统一真值域保持

保值结论只要求旧赋值的实际函数图，不再把完整空间作为自由参数。正负两个
模板的域扩张保持分别回到原对象推导；原公式编译仍不由此自动完成。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem finiteTruth_domain_l (hZF : M.Models ZF) (positive : Bool) {T ω n X Y F L r f : M.Domain}
    (hω : M.IsOmega ω) (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive T ω n Y F L r f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨E,he⟩ := ZF.exists_functionSpace hZF I n X
  obtain ⟨G,hg⟩ := ZF.exists_functionSpace hZF I n Y
  have hfE := (he f).mpr hf
  have hfG := (hg f).mpr (function_codomain_mono_l I sub hf)
  rw [finiteTruth_space_l hZF positive hω valid.variables he,finiteTruth_space_l hZF positive hω valid.variables hg]
  simpa only [hfE,hfG,true_and] using (certifiedTruth_domain_l hZF positive hx sub he hg valid hr hfE)

/-- 同一赋值在两个任意传递求值域中合法时，新模板也不依赖域的选择。 -/
theorem finiteTruth_domain_choice_l (hZF : M.Models ZF) (positive : Bool) {T ω n X Y F L r f : M.Domain}
    (hω : M.IsOmega ω) (hx : M.TransitiveSet X) (hy : M.TransitiveSet Y)
    (hfX : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (hfY : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n Y)
    (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive T ω n Y F L r f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨E,he⟩ := ZF.exists_functionSpace hZF I n X
  obtain ⟨G,hg⟩ := ZF.exists_functionSpace hZF I n Y
  have hfE := (he f).mpr hfX
  have hfG := (hg f).mpr hfY
  rw [finiteTruth_space_l hZF positive hω valid.variables he,finiteTruth_space_l hZF positive hω valid.variables hg]
  simpa only [hfE,hfG,true_and] using (certifiedTruth_domain_choice_l hZF positive hx hy he hg valid hr hfE hfG)

private def finiteDomainIndex (large : Bool) : Fin 6 → Fin 9 :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases (if large then 4 else 5) (Fin.cases 6 (Fin.cases 7 (fun _ => 8)))))
private def finiteDomainParams (large : Bool) (i : Fin 6) : Term 9 := .bound (finiteDomainIndex large i)

private def finiteTruthDomainBody (positive : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (Formula.isOmega (.bound 7)) <| .imp (Formula.isTransitive (.bound 5)) <|
      .imp (Formula.subset (.bound 5) (.bound 4)) <| .imp (fn0_m (.bound 6) (.bound 5) .newest) <|
        .imp (boundedFormula_m (.bound 8) (.bound 7) (.bound 6) (.bound 2) (.bound 3)) <|
          .imp (.mem (.bound 1) (.bound 2)) <|
            .iff (binary_pred_m (finiteTruth_s positive).schema (finiteDomainParams false) (.bound 1) .newest)
              (binary_pred_m (finiteTruth_s positive).schema (finiteDomainParams true) (.bound 1) .newest)

def finiteTruthDomain (positive : Bool) : Sentence := .ofFormula (finiteTruthDomainBody positive)
  (by simp -implicitDefEqProofs [finiteTruthDomainBody,finiteDomainParams,Definitional.Formula.FreeClosed])

theorem finiteTruthDomain_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (finiteTruthDomain positive) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (finiteTruthDomainBody positive)
  simp only [finiteTruthDomainBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isOmega_iff,Formula.satisfies_isTransitive_iff,Formula.satisfies_subset_iff,
    fn0_sat_l hZF.1,boundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_mem_iff,Formula.satisfies_iff_iff,
    binary_pred_sat_l,finiteTruth_sat_l (ZF.modelsKP hZF),finiteDomainParams,finiteDomainIndex]
  intro T ω n X Y F L r f hω hx sub hf valid hr
  exact finiteTruth_domain_l hZF positive hω hx sub (fn0_function_l (ZF.modelsKP hZF) hf) valid hr

theorem finiteTruthDomain_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (finiteTruthDomain positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => finiteTruthDomain_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
