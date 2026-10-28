import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Compiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateSourceRealization

/-! # 固定原 Σ₁ 源的原输出及完整见证对象查询 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

private def sigOld_m {n p} (t : Term n) : Term ((n+3)+(p+1)) := oldTerm_m t.weaken.weaken.weaken
private def sigX_m {n p} : Term ((n+3)+(p+1)) := oldTerm_m (.bound 2)
private def sigParams_m {n p} : Term ((n+3)+(p+1)) := oldTerm_m (.bound 1)
private def sigInput_m {n p} : Term ((n+3)+(p+1)) := oldTerm_m .newest
private def sigTail_m {n p} : Fin (p+2) → Term ((n+3)+(p+1)) := Fin.cases sigX_m (sourceTerm_m (n+3))

@[simp] private theorem sigTail_closed_l {n p} : ∀ i, (sigTail_m (n := n) (p := p) i).freeSupport = [] :=
  Fin.cases rfl (fun _ => rfl)

private theorem sigTail_eval_l {n p} (ρ : Env M n) (x params input : M.Domain)
    (values : Fin (p+1) → M.Domain) (j : Fin (p+2)) :
    (sigTail_m j).eval (blockEnv_l (((ρ.push x).push params).push input) values) = Fin.cases x values j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact oldTerm_eval_l (((ρ.push x).push params).push input) values (.bound 2)
  · exact sourceTerm_eval_l (((ρ.push x).push params).push input) values i

def indexedSigma1Query_m {n p} (φ : S1_binary (p+1)) (ω c k C empty : Term n) : Formula 1 n :=
  .forallE <| .forallE <| .forallE <| forallBlock_m (p+1) <|
    .imp (kpair0_m sigInput_m (sigOld_m c) sigParams_m) <|
    .imp (sourceParameterMatch_m (sigOld_m k) sigParams_m
      (sourceMask_m (sigma1SourceSlot_l p) (sigOld_m empty) sigTail_m)) <|
    .conj (.forallE (.imp
      (binary_pred_m indexedPredicateWitness_s.schema
        (predicatePairParams_m (sourceTerm_m (n+3) (0 : Fin (p+1))).weaken (sigOld_m ω).weaken)
        sigInput_m.weaken .newest)
      (binary_pred_m φ.schema (fun i => (sourceTerm_m (n+3) i).weaken) sigX_m.weaken .newest))) <|
    .conj (.forallE (.imp
      (within_m indexedPredicateWitness_s
        (predicatePairParams_m (sourceTerm_m (n+3) (0 : Fin (p+1))).weaken (sigOld_m ω).weaken)
        sigInput_m.weaken .newest (sigOld_m C).weaken)
      (within_m φ (fun i => (sourceTerm_m (n+3) i).weaken) sigX_m.weaken .newest (sigOld_m C).weaken))) <|
    .imp (amenableSet_m (sigOld_m C) (sourceTerm_m (n+3) (0 : Fin (p+1)))) <|
    .imp (.mem sigInput_m (sigOld_m C)) <|
    .imp (.existsE (fn0_m (sigOld_m k).weaken .newest sigParams_m.weaken)) <|
    .imp (Formula.existsMem (sigOld_m C)
      (within_m φ (fun i => (sourceTerm_m (n+3) i).weaken) sigX_m.weaken .newest (sigOld_m C).weaken)) <|
    Formula.existsMem (sigOld_m C) <|
      .conj (within_m indexedPredicateWitness_s
        (predicatePairParams_m (sourceTerm_m (n+3) (0 : Fin (p+1))).weaken (sigOld_m ω).weaken)
        sigInput_m.weaken .newest (sigOld_m C).weaken) <|
      .conj (within_m φ (fun i => (sourceTerm_m (n+3) i).weaken) sigX_m.weaken .newest (sigOld_m C).weaken) <|
      .forallE (.imp (binary_pred_m indexedPredicateWitness_s.schema
        (predicatePairParams_m (sourceTerm_m (n+3) (0 : Fin (p+1))).weaken.weaken (sigOld_m ω).weaken.weaken)
        sigInput_m.weaken.weaken .newest) (Formula.extensionalEq .newest (.bound 1)))

theorem indexedSigma1Query_closed_l {n p} (φ : S1_binary (p+1)) (ω c k C empty : Term n)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hk : k.freeSupport = [])
    (hC : C.freeSupport = []) (he : empty.freeSupport = []) :
    (indexedSigma1Query_m φ ω c k C empty).FreeClosed := by
  simp -implicitDefEqProofs [indexedSigma1Query_m,sigOld_m,sigX_m,sigParams_m,sigInput_m,
    sourceParameterMatch_closed_l,sourceMask_closed_l,sourceTerm_m,Definitional.Formula.FreeClosed,hω,hc,hk,hC,he]

theorem indexedSigma1Query_sat_l (hE : Extensional M) {n p} (ρ : Env M n) (φ : S1_binary (p+1)) (ω c k C empty : Term n) :
    Formula.satisfies ρ (indexedSigma1Query_m φ ω c k C empty) ↔
      ∀ x params input (values : Fin (p+1) → M.Domain), KPair_d M input (c.eval ρ) params →
        BoundedSourceParameter_d (k.eval ρ)
          (fun j => if j = sigma1SourceSlot_l p then empty.eval ρ else Fin.cases x values j) params →
        (∀ y, indexedPredicateWitness_s.schema.denote (indexedSource_env_l (⟨values,ρ.free⟩ : Env M (p+1)) (ω.eval ρ)) input y →
          φ.schema.denote (⟨values,ρ.free⟩ : Env M (p+1)) x y) ∧
        (∀ y, Within_d indexedPredicateWitness_s (indexedSource_env_l (⟨values,ρ.free⟩ : Env M (p+1)) (ω.eval ρ)) input y (C.eval ρ) →
          Within_d φ (⟨values,ρ.free⟩ : Env M (p+1)) x y (C.eval ρ)) ∧
        (AmenableSet_d (C.eval ρ) (values 0) → M.mem input (C.eval ρ) → (∃ X, Fn0_d (k.eval ρ) X params) →
          (∃ y, M.mem y (C.eval ρ) ∧ Within_d φ (⟨values,ρ.free⟩ : Env M (p+1)) x y (C.eval ρ)) →
          ∃ y, M.mem y (C.eval ρ) ∧ Within_d indexedPredicateWitness_s
            (indexedSource_env_l (⟨values,ρ.free⟩ : Env M (p+1)) (ω.eval ρ)) input y (C.eval ρ) ∧
            Within_d φ (⟨values,ρ.free⟩ : Env M (p+1)) x y (C.eval ρ) ∧
            ∀ t, indexedPredicateWitness_s.schema.denote
              (indexedSource_env_l (⟨values,ρ.free⟩ : Env M (p+1)) (ω.eval ρ)) input t → t = y) := by
  simp only [indexedSigma1Query_m,Formula.satisfies_forall_iff,forallBlock_sat_l,Formula.satisfies_imp_iff,
    kpair0_sat_l hE,sourceParameterMatch_sat_l hE,Formula.satisfies_conj_iff,binary_pred_sat_l,within_sat_l,
    predicatePairParams_env_l,amenableSet_sat_l,Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_existsMem_iff,fn0_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,
    sigOld_m,sigX_m,sigParams_m,sigInput_m,Definitional.Term.eval_weaken,oldTerm_eval_l,sourceTerm_eval_l,sourceMask_eval_l,sigTail_eval_l]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
