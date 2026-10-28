import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolemSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.VariableBlocks

/-! # 原源模板的规范 Skolem 对象查询

固定外部模板的变量块只装配原公式；内部程序长度与参数图仍为模型对象。
-/
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

def BoundedSourceParameter_d {d} (k : M.Domain) (values : Fin d → M.Domain) (a : M.Domain) : Prop :=
  ∀ j, ∃ t, M.mem t k ∧ Num_d j.val t ∧ Rd_entry_d t (values j) a

theorem boundedSourceParameter_forget_l {d} {k a : M.Domain} {values : Fin d → M.Domain}
    (corr : BoundedSourceParameter_d k values a) : SourceParameter_d values a := by
  intro j
  obtain ⟨t,_,ht,entry⟩ := corr j
  exact ⟨t,ht,entry⟩

theorem boundedSourceParameter_of_l (hE : Extensional M) {d} {k a : M.Domain} {values : Fin d → M.Domain}
    (hk : Num_d d k) (corr : SourceParameter_d values a) : BoundedSourceParameter_d k values a := by
  intro j
  obtain ⟨t,ht,entry⟩ := corr j
  exact ⟨t,num_lt_l hE ht hk j.isLt,ht,entry⟩

def sourceParameterMatch_m {n d} (k a : Term n) (values : Fin d → Term n) : Formula 1 n :=
  finConj_m d (fun j => Formula.existsMem k (.conj (pc_num_m j.val .newest) (rd_entry0_m .newest (values j).weaken a.weaken)))

theorem sourceParameterMatch_closed_l {n d} (k a : Term n) (values : Fin d → Term n)
    (hk : k.freeSupport = []) (ha : a.freeSupport = []) (hv : ∀ j, (values j).freeSupport = []) :
    (sourceParameterMatch_m k a values).FreeClosed := by
  simp -implicitDefEqProofs [sourceParameterMatch_m,Definitional.Formula.FreeClosed,hk,ha,hv]

theorem sourceParameterMatch_delta_l {n d} (k a : Term n) (values : Fin d → Term n) : (sourceParameterMatch_m k a values).IsDelta0 :=
  finConj_delta_l _ (fun _ => .existsMem _ (.conj (pc_num_delta_l ..) (rd_entry0_delta_l ..)))

theorem sourceParameterMatch_sat_l (hE : Extensional M) {n d} (ρ : Env M n) (k a : Term n) (values : Fin d → Term n) :
    Formula.satisfies ρ (sourceParameterMatch_m k a values) ↔
      BoundedSourceParameter_d (k.eval ρ) (fun j => (values j).eval ρ) (a.eval ρ) := by
  simp only [sourceParameterMatch_m,BoundedSourceParameter_d,finConj_sat_l,Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff,pc_num_sat_l hE,rd_entry0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def sourceWitnessBody_m (n : Nat) {d} (φ : Formula 1 (d+1)) : Formula 1 ((n+d)+1) :=
  φ.rename (sourceIndex_l n (d+1))

theorem sourceWitnessBody_closed_l (n : Nat) {d} (φ : Formula 1 (d+1)) (hc : φ.FreeClosed) :
    (sourceWitnessBody_m n φ).FreeClosed := by
  simpa -implicitDefEqProofs [sourceWitnessBody_m,Definitional.Formula.FreeClosed] using hc

theorem sourceWitnessBody_sat_l {n d} (ρ : Env M n) (values : Fin d → M.Domain) (y : M.Domain) (φ : Formula 1 (d+1)) :
    Formula.satisfies ((blockEnv_l ρ values).push y) (sourceWitnessBody_m n φ) ↔
      Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ := by
  rw [← blockEnv_succ_l]
  exact sourceRename_sat_l ρ (Fin.cases y values) φ

private def sourceQueryOld_m {n d} (t : Term n) : Term ((n+2)+d) := oldTerm_m t.weaken.weaken
private def sourceQueryInput_m {n d} : Term ((n+2)+d) := oldTerm_m .newest
private def sourceQueryArray_m {n d} : Term ((n+2)+d) := oldTerm_m (.bound 1)

def sourceSkolemQuery_m {n d} (φ : Formula 1 (d+1)) (ω e k C : Term n) : Formula 1 n :=
  .forallE <| .forallE <| forallBlock_m d <|
    .imp (rd_triple0_m sourceQueryInput_m (sourceQueryOld_m e) (sourceQueryOld_m k) sourceQueryArray_m) <|
      .imp (sourceParameterMatch_m (sourceQueryOld_m k) sourceQueryArray_m (sourceTerm_m (n+2))) <|
        .conj (.forallE (.imp
          (binary_pred_m parameterSkolem_s.schema (fun _ => (sourceQueryOld_m ω).weaken) sourceQueryInput_m.weaken .newest)
          (sourceWitnessBody_m (n+2) φ))) <|
          .imp (.mem sourceQueryInput_m (sourceQueryOld_m C)) <|
            .imp (.existsE (fn0_m (sourceQueryOld_m k).weaken .newest sourceQueryArray_m.weaken)) <|
              .imp (Formula.existsMem (sourceQueryOld_m C) (sourceWitnessBody_m (n+2) φ)) <|
                Formula.existsMem (sourceQueryOld_m C) <|
                  .conj (within_m parameterSkolem_s (fun _ => (sourceQueryOld_m ω).weaken) sourceQueryInput_m.weaken .newest (sourceQueryOld_m C).weaken) <|
                    .conj (sourceWitnessBody_m (n+2) φ) <|
                      .forallE (.imp
                        (binary_pred_m parameterSkolem_s.schema (fun _ => (sourceQueryOld_m ω).weaken.weaken) sourceQueryInput_m.weaken.weaken .newest)
                        (Formula.extensionalEq .newest (.bound 1)))

theorem sourceSkolemQuery_closed_l {n d} (φ : Formula 1 (d+1)) (ω e k C : Term n)
    (hc : φ.FreeClosed) (hω : ω.freeSupport = []) (he : e.freeSupport = []) (hk : k.freeSupport = []) (hC : C.freeSupport = []) :
    (sourceSkolemQuery_m φ ω e k C).FreeClosed := by
  simp -implicitDefEqProofs [sourceSkolemQuery_m,sourceQueryOld_m,sourceQueryInput_m,sourceQueryArray_m,
    sourceParameterMatch_closed_l,sourceWitnessBody_closed_l,sourceTerm_m,Definitional.Formula.FreeClosed,hc,hω,he,hk,hC]

theorem sourceSkolemQuery_sat_l (hE : Extensional M) {n d} (ρ : Env M n) (φ : Formula 1 (d+1)) (ω e k C : Term n) :
    Formula.satisfies ρ (sourceSkolemQuery_m φ ω e k C) ↔
      ∀ a input (values : Fin d → M.Domain), Rd_triple_d input (e.eval ρ) (k.eval ρ) a →
        BoundedSourceParameter_d (k.eval ρ) values a →
          (∀ y, parameterSkolem_s.schema.denote (⟨fun _ => ω.eval ρ,ρ.free⟩ : Env M 1) input y →
            Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) ∧
          (M.mem input (C.eval ρ) → (∃ X, Fn0_d (k.eval ρ) X a) →
            (∃ y, M.mem y (C.eval ρ) ∧ Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push y) φ) →
              ∃ z, M.mem z (C.eval ρ) ∧ Within_d parameterSkolem_s (⟨fun _ => ω.eval ρ,ρ.free⟩ : Env M 1) input z (C.eval ρ) ∧
                Formula.satisfies ((⟨values,ρ.free⟩ : Env M d).push z) φ ∧
                  ∀ t, parameterSkolem_s.schema.denote (⟨fun _ => ω.eval ρ,ρ.free⟩ : Env M 1) input t → t = z) := by
  simp only [sourceSkolemQuery_m,Formula.satisfies_forall_iff,forallBlock_sat_l,Formula.satisfies_imp_iff,rd_triple0_sat_l hE,
    sourceParameterMatch_sat_l hE,Formula.satisfies_conj_iff,binary_pred_sat_l,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_existsMem_iff,fn0_sat_l hE,within_sat_l,
    Formula.satisfies_extensionalEq_iff_eq hE,sourceWitnessBody_sat_l,sourceQueryOld_m,sourceQueryInput_m,sourceQueryArray_m,
    Definitional.Term.eval_weaken,oldTerm_eval_l,sourceTerm_eval_l]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
