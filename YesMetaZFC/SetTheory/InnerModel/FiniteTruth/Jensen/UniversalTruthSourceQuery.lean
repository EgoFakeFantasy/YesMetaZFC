import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolemSourceQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolemQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RestrictedTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Compiler

/-! # 同一通用真值表的固定原源查询

代码和源模板固定后，量化全部源参数、任意给定通用表及同层输入。
参数图匹配保留内部数码域上的有界证书；查询不重新构造表。
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

private def universalSourceTail_m {p d} (e : Fin (p+1) → Term d) (x : Term d) : Fin (p+2) → Term d :=
  Fin.cases x e

@[simp] private theorem universalSourceTail_closed_l {p d} (e : Fin (p+1) → Term d) (x : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hx : x.freeSupport = []) :
    ∀ j, (universalSourceTail_m e x j).freeSupport = [] := Fin.cases hx he

private theorem universalSourceTail_eval_l {p d} (ρ : Env M d) (e : Fin (p+1) → Term d) (x : Term d)
    (j : Fin (p+2)) : (universalSourceTail_m e x j).eval ρ =
      Fin.cases (x.eval ρ) (fun i => (e i).eval ρ) j := Fin.cases rfl (fun _ => rfl) j

def universalTruthSourceRealization_m {p d} (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d)
    (C c k empty T x : Term d) : Formula 1 d :=
  .existsE <| .existsE <| .existsE <|
    .conj (.mem (.bound 2) C.weaken.weaken.weaken) <|
    .conj (Formula.isTransitive (.bound 2)) <|
    .conj (.mem (.bound 1) C.weaken.weaken.weaken) <|
    .conj (.mem .newest C.weaken.weaken.weaken) <|
    .conj (fn0_m k.weaken.weaken.weaken (.bound 2) (.bound 1)) <|
    .conj (sourceParameterMatch_m k.weaken.weaken.weaken (.bound 1)
      (sourceMask_m (sigma1SourceSlot_l p) empty.weaken.weaken.weaken
        (universalSourceTail_m (fun i => (e i).weaken.weaken.weaken) x.weaken.weaken.weaken))) <|
    .conj (kpair0_m .newest c.weaken.weaken.weaken (.bound 1)) <|
      .iff (.mem .newest T.weaken.weaken.weaken)
        (restrictedTruthDomain_m φ (fun i => (e i).weaken.weaken.weaken)
          C.weaken.weaken.weaken x.weaken.weaken.weaken)

@[simp] theorem universalTruthSourceRealization_closed_l {p d} (φ : S1_binary (p+1))
    (e : Fin (p+1) → Term d) (C c k empty T x : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = [])
    (hc : c.freeSupport = []) (hk : k.freeSupport = []) (hEmpty : empty.freeSupport = [])
    (hT : T.freeSupport = []) (hx : x.freeSupport = []) :
    (universalTruthSourceRealization_m φ e C c k empty T x).FreeClosed := by
  have hmatchClosed : (sourceParameterMatch_m k.weaken.weaken.weaken (.bound 1 : Term (d+3))
      (sourceMask_m (sigma1SourceSlot_l p) empty.weaken.weaken.weaken
        (universalSourceTail_m (fun i => (e i).weaken.weaken.weaken) x.weaken.weaken.weaken))).FreeClosed := by
    apply sourceParameterMatch_closed_l
    · simpa only [Definitional.Term.freeSupport_weaken] using hk
    · rfl
    · apply sourceMask_closed_l
      · simpa only [Definitional.Term.freeSupport_weaken] using hEmpty
      · apply universalSourceTail_closed_l
        · intro i
          simpa only [Definitional.Term.freeSupport_weaken] using he i
        · simpa only [Definitional.Term.freeSupport_weaken] using hx
  simp -implicitDefEqProofs [universalTruthSourceRealization_m,hmatchClosed,he,hC,hc,hk,hT,hx,
    Definitional.Formula.FreeClosed]

theorem universalTruthSourceRealization_sat_l (hE : Extensional M) {p d} (ρ : Env M d)
    (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d) (C c k empty T x : Term d) :
    Formula.satisfies ρ (universalTruthSourceRealization_m φ e C c k empty T x) ↔
      ∃ X params input, M.mem X (C.eval ρ) ∧ M.TransitiveSet X ∧
        M.mem params (C.eval ρ) ∧ M.mem input (C.eval ρ) ∧ Fn0_d (k.eval ρ) X params ∧
        BoundedSourceParameter_d (k.eval ρ)
          (fun j => if j = sigma1SourceSlot_l p then empty.eval ρ
            else Fin.cases (x.eval ρ) (fun i => (e i).eval ρ) j) params ∧
        KPair_d M input (c.eval ρ) params ∧
        (M.mem input (T.eval ρ) ↔ RestrictedTruthDomain_d φ
          (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M (p+1)) (C.eval ρ) (x.eval ρ)) := by
  simp only [universalTruthSourceRealization_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_isTransitive_iff,fn0_sat_l hE,
    sourceParameterMatch_sat_l hE,sourceMask_eval_l,universalSourceTail_eval_l,kpair0_sat_l hE,
    Formula.satisfies_iff_iff,restrictedTruthDomain_sat_l,Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest,Term.eval_bound] <;> rfl

def universalTruthSourceQuery_m {p n} (φ : S1_binary (p+1)) (C ω c k empty : Term n) : Formula 1 n :=
  forallBlock_m (p+1) <|
    .imp (amenableSet_m (oldTerm_m C) (sourceTerm_m n 0)) <|
    .imp (finConj_m p (fun i => .mem (sourceTerm_m n i.succ) (oldTerm_m C))) <|
    .forallE <|
      .imp (universalTruthTable_m (sourceTerm_m n 0).weaken (oldTerm_m ω).weaken
        (oldTerm_m C).weaken .newest) <|
      Formula.forallMem (oldTerm_m C).weaken <|
        universalTruthSourceRealization_m φ (fun i => (sourceTerm_m n i).weaken.weaken)
          (oldTerm_m C).weaken.weaken (oldTerm_m c).weaken.weaken (oldTerm_m k).weaken.weaken
          (oldTerm_m empty).weaken.weaken (.bound 1) .newest

@[simp] theorem universalTruthSourceQuery_closed_l {p n} (φ : S1_binary (p+1)) (C ω c k empty : Term n)
    (hC : C.freeSupport = []) (hω : ω.freeSupport = []) (hc : c.freeSupport = [])
    (hk : k.freeSupport = []) (hEmpty : empty.freeSupport = []) :
    (universalTruthSourceQuery_m φ C ω c k empty).FreeClosed := by
  simp -implicitDefEqProofs [universalTruthSourceQuery_m,sourceTerm_m,
    Definitional.Formula.FreeClosed,hC,hω,hc,hk,hEmpty]

theorem universalTruthSourceQuery_sat_l (hE : Extensional M) {p n} (ρ : Env M n)
    (φ : S1_binary (p+1)) (C ω c k empty : Term n) :
    Formula.satisfies ρ (universalTruthSourceQuery_m φ C ω c k empty) ↔
      ∀ values : Fin (p+1) → M.Domain, AmenableSet_d (C.eval ρ) (values 0) →
        (∀ i : Fin p, M.mem (values i.succ) (C.eval ρ)) →
        ∀ T, UniversalTruthTable_d (⟨Fin.cases (values 0) (fun _ => ω.eval ρ),ρ.free⟩ : Env M 2)
          (C.eval ρ) T →
        ∀ x, M.mem x (C.eval ρ) →
          ∃ X params input, M.mem X (C.eval ρ) ∧ M.TransitiveSet X ∧
            M.mem params (C.eval ρ) ∧ M.mem input (C.eval ρ) ∧ Fn0_d (k.eval ρ) X params ∧
            BoundedSourceParameter_d (k.eval ρ)
              (fun j => if j = sigma1SourceSlot_l p then empty.eval ρ else Fin.cases x values j) params ∧
            KPair_d M input (c.eval ρ) params ∧
            (M.mem input T ↔ RestrictedTruthDomain_d φ (⟨values,ρ.free⟩ : Env M (p+1)) (C.eval ρ) x) := by
  simp only [universalTruthSourceQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,
    amenableSet_sat_l,finConj_sat_l,Formula.satisfies_mem_iff,Formula.satisfies_forall_iff,
    universalTruthTable_sat_l hE,Formula.satisfies_forallMem_iff,universalTruthSourceRealization_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound,
    oldTerm_eval_l,sourceTerm_eval_l] <;> rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
