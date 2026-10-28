import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RestrictedTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 实际受限真值集合的原 ZF 对象推导模式

固定源作为外部模式索引保留。内部量词只量化原集合、完整乘积与真值集合，
不量化任意 Lean 公式，也不提供目标层内的分离或主编码性质。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u

private def restrictedTruthTableExistsBody {n} (φ : S1_binary n) : Formula 1 (n+3) :=
  .existsE <| .existsE <|
    .conj (Formula.isCartesianProduct kpair_convention_l (.bound 1) (.bound 3) (.bound 4)) <|
    .conj (restrictedTruthTable_m φ (fun i => .bound i.succ.succ.succ.succ.succ)
      (.bound 3) (.bound 4) (.bound 2) .newest) <|
    .conj (Formula.subset .newest (.bound 1)) <|
      .forallE <| .imp (restrictedTruthTable_m φ (fun i => .bound i.succ.succ.succ.succ.succ.succ)
        (.bound 4) (.bound 5) (.bound 3) .newest) (Formula.extensionalEq .newest (.bound 1))

theorem restrictedTruthTableExistsBody_closed_l {n} (φ : S1_binary n) :
    (restrictedTruthTableExistsBody φ).FreeClosed := by
  simp -implicitDefEqProofs [restrictedTruthTableExistsBody,Definitional.Formula.FreeClosed]

def restrictedTruthTableExistsSentence {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (restrictedTruthTableExistsBody φ) (restrictedTruthTableExistsBody_closed_l φ)

theorem restrictedTruthTableExists_models {n} (φ : S1_binary n) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (restrictedTruthTableExistsSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0)
    (Formula.forallClosure (n+3) (restrictedTruthTableExistsBody φ))
  apply (Formula.satisfies_forallClosure_iff free (restrictedTruthTableExistsBody φ)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M (n+3)) (restrictedTruthTableExistsBody φ)
  simp only [restrictedTruthTableExistsBody,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isCartesianProduct_iff (kp_pair_l (ZF.modelsKP hZF)),restrictedTruthTable_sat_l hZF.1,
    Formula.satisfies_subset_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Term.eval_bound]
  let ρ : Env M n := ⟨fun i => b i.succ.succ.succ,free⟩
  obtain ⟨D,T,product,table,subset⟩ := restrictedTruthTable_exists_l hZF φ ρ (b 1) (b 2) (b 0)
  refine ⟨D,T,product,table,subset,?_⟩
  intro V other
  exact restrictedTruthTable_unique_l (M := M) hZF.1 other table

theorem restrictedTruthTableExists_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (restrictedTruthTableExistsSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => restrictedTruthTableExists_models φ M hM)

private def restrictedTruthTableEntryBody {n} (φ : S1_binary n) : Formula 1 (n+7) :=
  .imp (restrictedTruthTable_m φ (fun i => .bound i.succ.succ.succ.succ.succ.succ.succ)
    (.bound 1) (.bound 2) (.bound 0) (.bound 3)) <|
  .imp (.mem (.bound 4) (.bound 1)) <| .imp (.mem (.bound 5) (.bound 2)) <|
  .imp (kpair0_m (.bound 6) (.bound 4) (.bound 5)) <|
    .iff (.mem (.bound 6) (.bound 3))
      (restrictedTruthDomain_m φ (fun i => .bound i.succ.succ.succ.succ.succ.succ.succ) (.bound 0) (.bound 6))

theorem restrictedTruthTableEntryBody_closed_l {n} (φ : S1_binary n) :
    (restrictedTruthTableEntryBody φ).FreeClosed := by
  simp -implicitDefEqProofs [restrictedTruthTableEntryBody,Definitional.Formula.FreeClosed]

def restrictedTruthTableEntrySentence {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (restrictedTruthTableEntryBody φ) (restrictedTruthTableEntryBody_closed_l φ)

theorem restrictedTruthTableEntry_models {n} (φ : S1_binary n) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (restrictedTruthTableEntrySentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0)
    (Formula.forallClosure (n+7) (restrictedTruthTableEntryBody φ))
  apply (Formula.satisfies_forallClosure_iff free (restrictedTruthTableEntryBody φ)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M (n+7)) (restrictedTruthTableEntryBody φ)
  simp only [restrictedTruthTableEntryBody,Formula.satisfies_imp_iff,restrictedTruthTable_sat_l hZF.1,
    Formula.satisfies_mem_iff,kpair0_sat_l hZF.1,Formula.satisfies_iff_iff,
    restrictedTruthDomain_sat_l,Term.eval_bound]
  intro table hc hx pair
  exact table.pair_l hc hx pair

theorem restrictedTruthTableEntry_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (restrictedTruthTableEntrySentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => restrictedTruthTableEntry_models φ M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
