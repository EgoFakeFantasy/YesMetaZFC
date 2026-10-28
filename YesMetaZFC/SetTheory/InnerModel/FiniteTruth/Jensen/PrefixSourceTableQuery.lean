import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixQuerySyntax
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RestrictedTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolemSourceQuery

/-! # 全部普通参数的实际前缀与固定原源真值表规格

源模板保持为外部固定模式索引。参数匹配仍核验原内部有限图的全部普通源槽，
实际 A 只作查询源的独立只读背景参数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def prefixSourceTable_m {p d} (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d)
    (C ω U c P T : Term d) : Formula 1 d :=
  .conj (restrictedTruthTable_m prefixIndexedWitness_s (prefixParams_m (e 0) ω P) ω U C T) <|
    Formula.forallMem U <| .forallE <|
      .imp (kpair0_m .newest c.weaken.weaken (.bound 1)) <|
        .iff (.mem .newest T.weaken.weaken)
          (restrictedTruthDomain_m φ (fun i => (e i).weaken.weaken) C.weaken.weaken (.bound 1))

@[simp] theorem prefixSourceTable_closed_l {p d} (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d)
    (C ω U c P T : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hC : C.freeSupport = []) (hω : ω.freeSupport = []) (hU : U.freeSupport = [])
    (hc : c.freeSupport = []) (hP : P.freeSupport = []) (hT : T.freeSupport = []) :
    (prefixSourceTable_m φ e C ω U c P T).FreeClosed := by
  simp -implicitDefEqProofs [prefixSourceTable_m,he,hC,hω,hU,hc,hP,hT,Definitional.Formula.FreeClosed]

theorem prefixSourceTable_sat_l (hE : Extensional M) {p d} (ρ : Env M d)
    (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d) (C ω U c P T : Term d) :
    Formula.satisfies ρ (prefixSourceTable_m φ e C ω U c P T) ↔
      RestrictedTruthTable_d prefixIndexedWitness_s
        (⟨Fin.cases ((e 0).eval ρ) (Fin.cases (ω.eval ρ) (fun _ => P.eval ρ)),ρ.free⟩ : Env M 3)
        (ω.eval ρ) (U.eval ρ) (C.eval ρ) (T.eval ρ) ∧
      ∀ x, M.mem x (U.eval ρ) → ∀ input, KPair_d M input (c.eval ρ) x →
        (M.mem input (T.eval ρ) ↔
          RestrictedTruthDomain_d φ (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M (p+1)) (C.eval ρ) x) := by
  simp only [prefixSourceTable_m,Formula.satisfies_conj_iff,restrictedTruthTable_sat_l hE,
    prefixParams_env_l,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,kpair0_sat_l hE,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    restrictedTruthDomain_sat_l,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound] <;> rfl

def prefixSourceRealization_m {p d} (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d)
    (C ω U c : Term d) : Formula 1 d :=
  .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (pc_num_m p (.bound 3)) <|
    .conj (.mem (.bound 2) C.weaken.weaken.weaken.weaken) <|
    .conj (Formula.isTransitive (.bound 2)) <|
    .conj (.mem (.bound 1) C.weaken.weaken.weaken.weaken) <|
    .conj (fn0_m (.bound 3) (.bound 2) (.bound 1)) <|
    .conj (sourceParameterMatch_m (.bound 3) (.bound 1)
      (fun i : Fin p => (e i.succ).weaken.weaken.weaken.weaken)) <|
      prefixSourceTable_m φ (fun i => (e i).weaken.weaken.weaken.weaken)
        C.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken
        U.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken (.bound 1) .newest

@[simp] theorem prefixSourceRealization_closed_l {p d} (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d)
    (C ω U c : Term d) (he : ∀ i, (e i).freeSupport = [])
    (hC : C.freeSupport = []) (hω : ω.freeSupport = []) (hU : U.freeSupport = []) (hc : c.freeSupport = []) :
    (prefixSourceRealization_m φ e C ω U c).FreeClosed := by
  simp -implicitDefEqProofs [prefixSourceRealization_m,sourceParameterMatch_closed_l,
    he,hC,hω,hU,hc,Definitional.Formula.FreeClosed]

theorem prefixSourceRealization_sat_l (hE : Extensional M) {p d} (ρ : Env M d)
    (φ : S1_binary (p+1)) (e : Fin (p+1) → Term d) (C ω U c : Term d) :
    Formula.satisfies ρ (prefixSourceRealization_m φ e C ω U c) ↔
      ∃ l X P T, Num_d p l ∧ M.mem X (C.eval ρ) ∧ M.TransitiveSet X ∧ M.mem P (C.eval ρ) ∧
        Fn0_d l X P ∧ BoundedSourceParameter_d l (fun i : Fin p => (e i.succ).eval ρ) P ∧
        RestrictedTruthTable_d prefixIndexedWitness_s
          (⟨Fin.cases ((e 0).eval ρ) (Fin.cases (ω.eval ρ) (fun _ => P)),ρ.free⟩ : Env M 3)
          (ω.eval ρ) (U.eval ρ) (C.eval ρ) T ∧
        ∀ x, M.mem x (U.eval ρ) → ∀ input, KPair_d M input (c.eval ρ) x →
          (M.mem input T ↔ RestrictedTruthDomain_d φ
            (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M (p+1)) (C.eval ρ) x) := by
  simp only [prefixSourceRealization_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    pc_num_sat_l hE,Formula.satisfies_mem_iff,Formula.satisfies_isTransitive_iff,fn0_sat_l hE,
    sourceParameterMatch_sat_l hE,prefixSourceTable_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound] <;> rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
