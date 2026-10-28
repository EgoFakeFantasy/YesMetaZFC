import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolemCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSkolemQuery

/-! # 固定原谓词模板的实际见证函数对象查询 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

def sourceMask_m {n d} (a : Fin d) (empty : Term n) (values : Fin d → Term n) : Fin d → Term n :=
  fun j => if j = a then empty else values j

theorem sourceMask_closed_l {n d} (a : Fin d) (empty : Term n) (values : Fin d → Term n)
    (he : empty.freeSupport = []) (hv : ∀ j, (values j).freeSupport = []) :
    ∀ j, (sourceMask_m a empty values j).freeSupport = [] := by
  intro j
  unfold sourceMask_m
  split
  · exact he
  · exact hv j

theorem sourceMask_eval_l {n d} (ρ : Env M n) (a : Fin d) (empty : Term n) (values : Fin d → Term n) (j : Fin d) :
    (sourceMask_m a empty values j).eval ρ = if j = a then empty.eval ρ else (values j).eval ρ := by
  unfold sourceMask_m
  split <;> rfl

private def sourceQueryOld_m {n d} (t : Term n) : Term ((n+2)+d) := oldTerm_m t.weaken.weaken
private def sourceQueryInput_m {n d} : Term ((n+2)+d) := oldTerm_m .newest
private def sourceQueryArray_m {n d} : Term ((n+2)+d) := oldTerm_m (.bound 1)

def predicateSourceSkolemQuery_m {n d} (a : Fin d) (φ : Formula 1 (d+1)) (ω e k C empty : Term n) : Formula 1 n :=
  .forallE <| .forallE <| forallBlock_m d <|
    .imp (rd_triple0_m sourceQueryInput_m (sourceQueryOld_m e) (sourceQueryOld_m k) sourceQueryArray_m) <|
      .imp (sourceParameterMatch_m (sourceQueryOld_m k) sourceQueryArray_m (sourceMask_m a (sourceQueryOld_m empty) (sourceTerm_m (n+2)))) <|
        .conj (.forallE (.imp
          (binary_pred_m predicateParameterSkolem_s.schema (predicatePairParams_m (sourceTerm_m (n+2) a).weaken (sourceQueryOld_m ω).weaken) sourceQueryInput_m.weaken .newest)
          (sourceWitnessBody_m (n+2) φ))) <|
          .imp (amenableSet_m (sourceQueryOld_m C) (sourceTerm_m (n+2) a)) <|
          .imp (.mem sourceQueryInput_m (sourceQueryOld_m C)) <|
            .imp (.existsE (fn0_m (sourceQueryOld_m k).weaken .newest sourceQueryArray_m.weaken)) <|
              .imp (Formula.existsMem (sourceQueryOld_m C) (sourceWitnessBody_m (n+2) φ)) <|
                Formula.existsMem (sourceQueryOld_m C) <|
                  .conj (within_m predicateParameterSkolem_s (predicatePairParams_m (sourceTerm_m (n+2) a).weaken (sourceQueryOld_m ω).weaken) sourceQueryInput_m.weaken .newest (sourceQueryOld_m C).weaken) <|
                    .conj (sourceWitnessBody_m (n+2) φ) <|
                      .forallE (.imp
                        (binary_pred_m predicateParameterSkolem_s.schema (predicatePairParams_m (sourceTerm_m (n+2) a).weaken.weaken (sourceQueryOld_m ω).weaken.weaken) sourceQueryInput_m.weaken.weaken .newest)
                        (Formula.extensionalEq .newest (.bound 1)))

theorem predicateSourceSkolemQuery_closed_l {n d} (a : Fin d) (φ : Formula 1 (d+1)) (ω e k C empty : Term n)
    (hc : φ.FreeClosed) (hω : ω.freeSupport = []) (he : e.freeSupport = []) (hk : k.freeSupport = []) (hC : C.freeSupport = []) (hEmpty : empty.freeSupport = []) :
    (predicateSourceSkolemQuery_m a φ ω e k C empty).FreeClosed := by
  simp -implicitDefEqProofs [predicateSourceSkolemQuery_m,sourceQueryOld_m,sourceQueryInput_m,sourceQueryArray_m,
    sourceParameterMatch_closed_l,sourceWitnessBody_closed_l,sourceTerm_m,Definitional.Formula.FreeClosed,hc,hω,he,hk,hC,hEmpty,sourceMask_closed_l]

theorem predicateSourceSkolemQuery_sat_l (hE : Extensional M) {n d} (ρ : Env M n) (a : Fin d) (φ : Formula 1 (d+1)) (ω e k C empty : Term n) :
    Formula.satisfies ρ (predicateSourceSkolemQuery_m a φ ω e k C empty) ↔
      ∀ params input (values : Fin d → M.Domain), Rd_triple_d input (e.eval ρ) (k.eval ρ) params →
        BoundedSourceParameter_d (k.eval ρ) (fun j => if j = a then empty.eval ρ else values j) params →
          (∀ y, predicateParameterSkolem_s.schema.denote (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input y →
            Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) ∧
          (AmenableSet_d (C.eval ρ) (values a) → M.mem input (C.eval ρ) → (∃ X, Fn0_d (k.eval ρ) X params) →
            (∃ y, M.mem y (C.eval ρ) ∧ Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) →
              ∃ z, M.mem z (C.eval ρ) ∧ Within_d predicateParameterSkolem_s (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input z (C.eval ρ) ∧
                Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push z) φ ∧
                  ∀ t, predicateParameterSkolem_s.schema.denote (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input t → t = z) := by
  simp only [predicateSourceSkolemQuery_m,Formula.satisfies_forall_iff,forallBlock_sat_l,Formula.satisfies_imp_iff,rd_triple0_sat_l hE,
    sourceParameterMatch_sat_l hE,Formula.satisfies_conj_iff,binary_pred_sat_l,predicatePairParams_env_l,amenableSet_sat_l,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_existsMem_iff,fn0_sat_l hE,within_sat_l,
    Formula.satisfies_extensionalEq_iff_eq hE,sourceWitnessBody_sat_l,sourceQueryOld_m,sourceQueryInput_m,sourceQueryArray_m,
    Definitional.Term.eval_weaken,oldTerm_eval_l,sourceTerm_eval_l,sourceMask_eval_l]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
