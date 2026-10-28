import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateSourceQuery

/-! # 原源参数的实际输入存在及跨域唯一对象查询 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

def niceSourceInputRealization_m {n d} (a : Fin d) (ω c k C empty : Term n) : Formula 1 n :=
  forallBlock_m d <|
    .imp (protectedConj_m a (fun j => .mem (sourceTerm_m n j) (oldTerm_m C))) <|
      .existsE <| .existsE <| .existsE <|
        .conj (.mem (.bound 2) (oldTerm_m C).weaken.weaken.weaken) <|
          .conj (Formula.isTransitive (.bound 2)) <|
            .conj (.mem (.bound 1) (oldTerm_m C).weaken.weaken.weaken) <|
              .conj (.mem .newest (oldTerm_m C).weaken.weaken.weaken) <|
                .conj (fn0_m (oldTerm_m k).weaken.weaken.weaken (.bound 2) (.bound 1)) <|
                  .conj (sourceParameterMatch_m (oldTerm_m k).weaken.weaken.weaken (.bound 1)
                    (sourceMask_m a (oldTerm_m empty).weaken.weaken.weaken (fun j => (sourceTerm_m n j).weaken.weaken.weaken))) <|
                    .conj (kpair0_m .newest (oldTerm_m c).weaken.weaken.weaken (.bound 1)) <|
                      .conj (niceInput_m (oldTerm_m ω).weaken.weaken.weaken (oldTerm_m C).weaken.weaken.weaken .newest) <|
                      .forallE <| .forallE <|
                        .imp (fn0_m (oldTerm_m k).weaken.weaken.weaken.weaken.weaken .newest (.bound 1)) <|
                          .imp (sourceParameterMatch_m (oldTerm_m k).weaken.weaken.weaken.weaken.weaken (.bound 1)
                            (sourceMask_m a (oldTerm_m empty).weaken.weaken.weaken.weaken.weaken (fun j => (sourceTerm_m n j).weaken.weaken.weaken.weaken.weaken)))
                            (Formula.extensionalEq (.bound 1) (.bound 3))

theorem niceSourceInputRealization_closed_l {n d} (a : Fin d) (ω c k C empty : Term n)
    (hω : ω.freeSupport = []) (hcIndex : c.freeSupport = []) (hk : k.freeSupport = []) (hC : C.freeSupport = []) (hEmpty : empty.freeSupport = []) :
    (niceSourceInputRealization_m a ω c k C empty).FreeClosed := by
  simp -implicitDefEqProofs [niceSourceInputRealization_m,sourceParameterMatch_closed_l,
    sourceTerm_m,Definitional.Formula.FreeClosed,hω,hcIndex,hk,hC,hEmpty,sourceMask_closed_l]

theorem niceSourceInputRealization_sat_l (hE : Extensional M) {n d} (a : Fin d) (ρ : Env M n) (ω c k C empty : Term n) :
    Formula.satisfies ρ (niceSourceInputRealization_m a ω c k C empty) ↔
      ∀ values : Fin d → M.Domain, (∀ j, j ≠ a → M.mem (values j) (C.eval ρ)) →
        ∃ X params input, M.mem X (C.eval ρ) ∧ M.TransitiveSet X ∧ M.mem params (C.eval ρ) ∧ M.mem input (C.eval ρ) ∧
          Fn0_d (k.eval ρ) X params ∧ BoundedSourceParameter_d (k.eval ρ) (fun j => if j = a then empty.eval ρ else values j) params ∧ KPair_d M input (c.eval ρ) params ∧ NiceInput_d (ω.eval ρ) (C.eval ρ) input ∧
            ∀ b Y, Fn0_d (k.eval ρ) Y b → BoundedSourceParameter_d (k.eval ρ) (fun j => if j = a then empty.eval ρ else values j) b → b = params := by
  simp only [niceSourceInputRealization_m,forallBlock_sat_l,Formula.satisfies_imp_iff,protectedConj_sat_l,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,fn0_sat_l hE,
    sourceParameterMatch_sat_l hE,kpair0_sat_l hE,niceInput_sat_l hE,Formula.satisfies_forall_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken,oldTerm_eval_l,sourceTerm_eval_l,sourceMask_eval_l]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
