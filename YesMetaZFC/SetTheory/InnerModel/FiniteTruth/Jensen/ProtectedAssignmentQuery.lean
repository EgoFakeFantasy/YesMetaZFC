import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProtectedBlocks
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RegisterAssignmentObjectTheorems

/-! # 指定谓词槽排除后的原完整空间赋值实现规格 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

def protectedAssignmentQuery_m {m d} (a : Fin d) (v : Fin d → Term m) (C E n X : Term m) : Formula 1 m :=
  forallBlock_m d <| .imp (protectedConj_m a (fun i => .mem (sourceTerm_m m i) (oldTerm_m X))) <|
    .existsE <| .conj (.mem .newest (oldTerm_m E).weaken) <|
      .conj (.mem .newest (oldTerm_m C).weaken) <|
        .conj (fn0_m (oldTerm_m n).weaken (oldTerm_m X).weaken .newest)
          (protectedConj_m a (fun i => rd_entry0_m (oldTerm_m (v i)).weaken (sourceTerm_m m i).weaken .newest))

theorem protectedAssignmentQuery_closed_l {m d} (a : Fin d) (v : Fin d → Term m) (C E n X : Term m)
    (hv : ∀ i, (v i).freeSupport = []) (hC : C.freeSupport = []) (hE : E.freeSupport = [])
    (hn : n.freeSupport = []) (hX : X.freeSupport = []) : (protectedAssignmentQuery_m a v C E n X).FreeClosed := by
  simp -implicitDefEqProofs [protectedAssignmentQuery_m,sourceTerm_m,Definitional.Formula.FreeClosed,hv,hC,hE,hn,hX]

theorem protectedAssignmentQuery_sat_l (hE : Extensional M) {m d} (ρ : Env M m) (a : Fin d) (v : Fin d → Term m) (C E n X : Term m) :
    Formula.satisfies ρ (protectedAssignmentQuery_m a v C E n X) ↔
      ∀ σ : Fin d → M.Domain, (∀ i, i ≠ a → M.mem (σ i) (X.eval ρ)) →
        ∃ f, M.mem f (E.eval ρ) ∧ M.mem f (C.eval ρ) ∧ Fn0_d (n.eval ρ) (X.eval ρ) f ∧
          ∀ i, i ≠ a → Rd_entry_d ((v i).eval ρ) (σ i) f := by
  simp only [protectedAssignmentQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,protectedConj_sat_l,
    Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fn0_sat_l hE,rd_entry0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,
    sourceTerm_eval_l,oldTerm_eval_l]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
