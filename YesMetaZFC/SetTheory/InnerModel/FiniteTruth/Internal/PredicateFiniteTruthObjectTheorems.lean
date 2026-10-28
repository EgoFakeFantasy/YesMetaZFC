import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 实际完整赋值资格和传递域选择独立性的原 ZF 推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

private def pfiniteParams {d} (A L F X n ω T : Term d) : Fin 7 → Term d :=
  Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T))))))

@[simp] private theorem pfiniteParams_closed_l {d} (A L F X n ω T : Term d)
    (hA : A.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) (hX : X.freeSupport = [])
    (hn : n.freeSupport = []) (hω : ω.freeSupport = []) (hT : T.freeSupport = []) :
    ∀ i, (pfiniteParams A L F X n ω T i).freeSupport = [] :=
  Fin.cases hA (Fin.cases hL (Fin.cases hF (Fin.cases hX (Fin.cases hn (Fin.cases hω (fun _ => hT))))))

private def predicateFiniteAssignmentBody : Formula 1 9 :=
  .imp (Formula.isOmega (.bound 2)) <|
    .imp (pboundedFormula_m (.bound 0) (.bound 2) (.bound 3) (.bound 6) (.bound 5)) <|
      .iff (.disj
        (binary_pred_m (pfiniteTruth_s true).schema
          (pfiniteParams (.bound 1) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0)) (.bound 7) (.bound 8))
        (binary_pred_m (pfiniteTruth_s false).schema
          (pfiniteParams (.bound 1) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 0)) (.bound 7) (.bound 8)))
        (fn0_m (.bound 3) (.bound 4) (.bound 8))

def predicateFiniteAssignmentSentence : Sentence := Sentence.forallClosure predicateFiniteAssignmentBody
  (by simp -implicitDefEqProofs [predicateFiniteAssignmentBody,Definitional.Formula.FreeClosed])

theorem predicateFiniteAssignment_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateFiniteAssignmentSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 9 predicateFiniteAssignmentBody)
  apply (Formula.satisfies_forallClosure_iff free predicateFiniteAssignmentBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 9) predicateFiniteAssignmentBody
  simp only [predicateFiniteAssignmentBody,Formula.satisfies_imp_iff,Formula.satisfies_isOmega_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_iff_iff,Formula.satisfies_disj_iff,
    binary_pred_sat_l,pfiniteTruth_sat_l (ZF.modelsKP hZF),fn0_sat_l hZF.1,pfiniteParams,Term.eval_bound]
  intro hω valid
  exact (pfiniteTruth_assignment_iff_l hZF hω valid).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF),fn0_function_l (ZF.modelsKP hZF)⟩

theorem predicateFiniteAssignment_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateFiniteAssignmentSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateFiniteAssignment_models M hM)

private def predicateFiniteDomainBody (positive : Bool) : Formula 1 10 :=
  .imp (Formula.isOmega (.bound 2)) <| .imp (Formula.isTransitive (.bound 4)) <|
    .imp (Formula.isTransitive (.bound 5)) <|
      .imp (pboundedFormula_m (.bound 0) (.bound 2) (.bound 3) (.bound 7) (.bound 6)) <|
        .imp (.mem (.bound 8) (.bound 7)) <| .imp (fn0_m (.bound 3) (.bound 4) (.bound 9)) <|
          .imp (fn0_m (.bound 3) (.bound 5) (.bound 9)) <|
            .iff (binary_pred_m (pfiniteTruth_s positive).schema
              (pfiniteParams (.bound 1) (.bound 7) (.bound 6) (.bound 4) (.bound 3) (.bound 2) (.bound 0)) (.bound 8) (.bound 9))
              (binary_pred_m (pfiniteTruth_s positive).schema
                (pfiniteParams (.bound 1) (.bound 7) (.bound 6) (.bound 5) (.bound 3) (.bound 2) (.bound 0)) (.bound 8) (.bound 9))

def predicateFiniteDomainSentence (positive : Bool) : Sentence := Sentence.forallClosure (predicateFiniteDomainBody positive)
  (by simp -implicitDefEqProofs [predicateFiniteDomainBody,Definitional.Formula.FreeClosed])

theorem predicateFiniteDomain_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (predicateFiniteDomainSentence positive) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 10 (predicateFiniteDomainBody positive))
  apply (Formula.satisfies_forallClosure_iff free (predicateFiniteDomainBody positive)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 10) (predicateFiniteDomainBody positive)
  simp only [predicateFiniteDomainBody,Formula.satisfies_imp_iff,Formula.satisfies_isOmega_iff,
    Formula.satisfies_isTransitive_iff,pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_mem_iff,
    fn0_sat_l hZF.1,Formula.satisfies_iff_iff,binary_pred_sat_l,
    pfiniteTruth_sat_l (ZF.modelsKP hZF),pfiniteParams,Term.eval_bound]
  intro hω hx hy valid hr fx fy
  exact pfiniteTruth_domain_choice_l hZF positive hω hx hy valid hr
    (fn0_function_l (ZF.modelsKP hZF) fx) (fn0_function_l (ZF.modelsKP hZF) fy)

theorem predicateFiniteDomain_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (predicateFiniteDomainSentence positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateFiniteDomain_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
