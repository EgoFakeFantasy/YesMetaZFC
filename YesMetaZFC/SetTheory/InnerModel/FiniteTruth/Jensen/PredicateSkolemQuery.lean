import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSkolemCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolemSourceQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProtectedAssignmentQuery

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

def predicatePairParams_m {k} (A ω : Term k) : Fin 2 → Term k := Fin.cases A (fun _ => ω)

@[simp] theorem predicatePairParams_closed_l {k} (A ω : Term k)
    (hA : A.freeSupport = []) (hω : ω.freeSupport = []) :
    ∀ i, (predicatePairParams_m A ω i).freeSupport = [] := Fin.cases hA (fun _ => hω)

theorem predicatePairParams_env_l {k} (ρ : Env M k) (A ω : Term k) :
    (⟨fun i => (predicatePairParams_m A ω i).eval ρ,ρ.free⟩ : Env M 2) =
      ⟨Fin.cases (A.eval ρ) (fun _ => ω.eval ρ),ρ.free⟩ := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)),rfl⟩

private def skQueryOld_m {n d} (t : Term n) : Term ((n+2)+d) := oldTerm_m t.weaken.weaken
private def skQueryInput_m {n d} : Term ((n+2)+d) := oldTerm_m .newest
private def skQueryArray_m {n d} : Term ((n+2)+d) := oldTerm_m (.bound 1)

def predicateSkolemQuery_m {n d} (a : Fin d) (φ : Formula 1 (d+1))
    (v : Fin (d+1) → Term n) (ω arity e C : Term n) : Formula 1 n :=
  .forallE <| .forallE <| forallBlock_m d <|
    .imp (rd_triple0_m skQueryInput_m (skQueryOld_m e) skQueryArray_m (skQueryOld_m (v 0))) <|
    .imp (protectedConj_m a (fun j => rd_entry0_m (skQueryOld_m (v j.succ)) (sourceTerm_m (n+2) j) skQueryArray_m)) <|
    .conj (.forallE (.imp
      (binary_pred_m predicateNumericSkolem_s.schema
        (predicatePairParams_m (sourceTerm_m (n+2) a).weaken (skQueryOld_m ω).weaken) skQueryInput_m.weaken .newest)
      (sourceWitnessBody_m (n+2) φ))) <|
    .imp (amenableSet_m (skQueryOld_m C) (sourceTerm_m (n+2) a)) <|
    .imp (.mem skQueryInput_m (skQueryOld_m C)) <|
    .imp (.existsE (fn0_m (skQueryOld_m arity).weaken .newest skQueryArray_m.weaken)) <|
    .imp (Formula.existsMem (skQueryOld_m C) (sourceWitnessBody_m (n+2) φ)) <|
      Formula.existsMem (skQueryOld_m C) <|
        .conj (within_m predicateNumericSkolem_s
          (predicatePairParams_m (sourceTerm_m (n+2) a).weaken (skQueryOld_m ω).weaken)
          skQueryInput_m.weaken .newest (skQueryOld_m C).weaken) <|
        .conj (sourceWitnessBody_m (n+2) φ) <|
          .forallE (.imp (binary_pred_m predicateNumericSkolem_s.schema
            (predicatePairParams_m (sourceTerm_m (n+2) a).weaken.weaken (skQueryOld_m ω).weaken.weaken)
            skQueryInput_m.weaken.weaken .newest) (Formula.extensionalEq .newest (.bound 1)))

theorem predicateSkolemQuery_closed_l {n d} (a : Fin d) (φ : Formula 1 (d+1))
    (v : Fin (d+1) → Term n) (ω arity e C : Term n) (hc : φ.FreeClosed)
    (hv : ∀ i, (v i).freeSupport = []) (hω : ω.freeSupport = []) (hn : arity.freeSupport = [])
    (he : e.freeSupport = []) (hC : C.freeSupport = []) :
    (predicateSkolemQuery_m a φ v ω arity e C).FreeClosed := by
  simp -implicitDefEqProofs [predicateSkolemQuery_m,skQueryOld_m,skQueryInput_m,skQueryArray_m,
    sourceWitnessBody_closed_l,sourceTerm_m,Definitional.Formula.FreeClosed,hc,hv,hω,hn,he,hC]

theorem predicateSkolemQuery_sat_l (hE : Extensional M) {n d} (ρ : Env M n) (a : Fin d)
    (φ : Formula 1 (d+1)) (v : Fin (d+1) → Term n) (ω arity e C : Term n) :
    Formula.satisfies ρ (predicateSkolemQuery_m a φ v ω arity e C) ↔
      ∀ f input (values : Fin d → M.Domain), Rd_triple_d input (e.eval ρ) f ((v 0).eval ρ) →
        (∀ j, j ≠ a → Rd_entry_d ((v j.succ).eval ρ) (values j) f) →
          (∀ y, predicateNumericSkolem_s.schema.denote
            (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input y →
              Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) ∧
          (AmenableSet_d (C.eval ρ) (values a) → M.mem input (C.eval ρ) → (∃ X, Fn0_d (arity.eval ρ) X f) →
            (∃ y, M.mem y (C.eval ρ) ∧ Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) →
              ∃ z, M.mem z (C.eval ρ) ∧ Within_d predicateNumericSkolem_s
                (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input z (C.eval ρ) ∧
                Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push z) φ ∧
                ∀ t, predicateNumericSkolem_s.schema.denote
                  (predicateSkolem_env_l a (ω.eval ρ) (⟨values,ρ.free⟩ : Env M d)) input t → t = z) := by
  simp only [predicateSkolemQuery_m,Formula.satisfies_forall_iff,forallBlock_sat_l,Formula.satisfies_imp_iff,
    rd_triple0_sat_l hE,protectedConj_sat_l,rd_entry0_sat_l hE,Formula.satisfies_conj_iff,
    binary_pred_sat_l,predicatePairParams_env_l,amenableSet_sat_l,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_existsMem_iff,fn0_sat_l hE,within_sat_l,
    Formula.satisfies_extensionalEq_iff_eq hE,sourceWitnessBody_sat_l,skQueryOld_m,skQueryInput_m,skQueryArray_m,
    Definitional.Term.eval_weaken,oldTerm_eval_l,sourceTerm_eval_l]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
