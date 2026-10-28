import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RegisterFrame
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 同一原 J 层内所有源赋值的实际实现

对全部内部有限变量域，只选择一次同层完整空间 E；随后每个域内源值向量
都有 E 中且仍在原层内的真实函数图。小层不承担 KP 或 Collection 假设。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

def assignmentInSpaceQuery_m {m d} (v : Fin d → Term m) (C E n X : Term m) : Formula 1 m :=
  forallBlock_m d <| .imp (finConj_m d (fun i => .mem (sourceTerm_m m i) (oldTerm_m X))) <|
    .existsE <| .conj (.mem .newest (oldTerm_m E).weaken) <|
      .conj (.mem .newest (oldTerm_m C).weaken) <|
        .conj (fn0_m (oldTerm_m n).weaken (oldTerm_m X).weaken .newest)
          (finConj_m d (fun i => rd_entry0_m (oldTerm_m (v i)).weaken (sourceTerm_m m i).weaken .newest))

theorem assignmentInSpaceQuery_closed_l {m d} (v : Fin d → Term m) (C E n X : Term m)
    (hv : ∀ i, (v i).freeSupport = []) (hC : C.freeSupport = []) (hE : E.freeSupport = [])
    (hn : n.freeSupport = []) (hX : X.freeSupport = []) : (assignmentInSpaceQuery_m v C E n X).FreeClosed := by
  simp -implicitDefEqProofs [assignmentInSpaceQuery_m,sourceTerm_m,Definitional.Formula.FreeClosed,hv,hC,hE,hn,hX]

theorem assignmentInSpaceQuery_sat_l (hE : Extensional M) {m d} (ρ : Env M m) (v : Fin d → Term m) (C E n X : Term m) :
    Formula.satisfies ρ (assignmentInSpaceQuery_m v C E n X) ↔
      ∀ σ : Fin d → M.Domain, (∀ i, M.mem (σ i) (X.eval ρ)) →
        ∃ f, M.mem f (E.eval ρ) ∧ M.mem f (C.eval ρ) ∧ Fn0_d (n.eval ρ) (X.eval ρ) f ∧
          ∀ i, Rd_entry_d ((v i).eval ρ) (σ i) f := by
  simp only [assignmentInSpaceQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,finConj_sat_l,
    Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fn0_sat_l hE,rd_entry0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,
    sourceTerm_eval_l,oldTerm_eval_l]

private def layerAssignmentParam_m (d : Nat) (i : Fin 6) : Term (6+d) := .bound ⟨d+i.val,by omega⟩
private def layerAssignmentRegister_m (d : Nat) (i : Fin d) : Term (6+d) := .bound ⟨i.val,by omega⟩

private def jensenAssignmentRealizationBody (d : Nat) : Formula 1 (6+d) :=
  .imp (KP.ord0_m (layerAssignmentParam_m d 5)) <|
    .imp (jh_value_m (layerAssignmentParam_m d 5) (layerAssignmentParam_m d 4)) <|
      .imp (Formula.isOmega (layerAssignmentParam_m d 3)) <|
        .imp (.mem (layerAssignmentParam_m d 3) (layerAssignmentParam_m d 4)) <|
          .imp (.mem (layerAssignmentParam_m d 1) (layerAssignmentParam_m d 4)) <|
            .imp (.mem (layerAssignmentParam_m d 2) (layerAssignmentParam_m d 3)) <|
              .imp (registersBound_m (layerAssignmentRegister_m d) (layerAssignmentParam_m d 2)) <|
                .imp (registersInjective_m (layerAssignmentRegister_m d)) <|
                  .imp (.mem (layerAssignmentParam_m d 0) (layerAssignmentParam_m d 1)) <|
                    .existsE <| .conj (.mem .newest (layerAssignmentParam_m d 4).weaken) <|
                      .conj (Formula.isFunctionSpace kpair_convention_l .newest
                        (layerAssignmentParam_m d 2).weaken (layerAssignmentParam_m d 1).weaken)
                        (assignmentInSpaceQuery_m (fun i => (layerAssignmentRegister_m d i).weaken)
                          (layerAssignmentParam_m d 4).weaken .newest (layerAssignmentParam_m d 2).weaken (layerAssignmentParam_m d 1).weaken)

def jensenAssignmentRealization (d : Nat) : Sentence := Sentence.forallClosure (jensenAssignmentRealizationBody d)
  (by simp -implicitDefEqProofs [jensenAssignmentRealizationBody,layerAssignmentParam_m,layerAssignmentRegister_m,
    registersBound_closed_l,registersInjective_closed_l,assignmentInSpaceQuery_closed_l,Definitional.Formula.FreeClosed])

theorem jensenAssignmentRealization_models (d : Nat) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenAssignmentRealization d) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0)
    (Formula.forallClosure (6+d) (jensenAssignmentRealizationBody d))
  rw [Formula.satisfies_forallClosure_iff]
  intro bound
  let η : Env M (6+d) := ⟨bound,envFree⟩
  change Formula.satisfies η (jensenAssignmentRealizationBody d)
  simp only [jensenAssignmentRealizationBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    registersBound_sat_l,registersInjective_sat_l hZF.1,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    assignmentInSpaceQuery_sat_l hZF.1,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,
    layerAssignmentParam_m,layerAssignmentRegister_m]
  intro ha h hω hωC hXC hn hv injective inhabited
  exact jh_assignment_realize_l hZF (fun i : Fin d => η.bound ⟨i.val,by omega⟩)
    ha h hω hωC hXC hn hv injective inhabited

theorem jensenAssignmentRealization_derives (d : Nat) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenAssignmentRealization d) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenAssignmentRealization_models d M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
