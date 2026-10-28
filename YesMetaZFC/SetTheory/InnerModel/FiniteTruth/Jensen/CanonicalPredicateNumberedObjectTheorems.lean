import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CompiledPredicateNumberedQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProtectedAssignmentQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 全原谓词模板的同一通用数码与双参数真值的原 ZF 模式

同一个 e 先于全部源值和求值域选择。原程序/编号见证和普通赋值实现显式保留。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u

private def numOld_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 4) : Term (4+deltaSourceWidth_l p reserve) := oldTerm_m (.bound i : Term 4)
private def numSlot_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin (deltaSourceWidth_l p reserve)) : Term (4+deltaSourceWidth_l p reserve) := sourceTerm_m 4 i
private def numSource_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin d) : Term (4+deltaSourceWidth_l p reserve) := sourceTerm_m 4 ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def numResult_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 5) : Term ((4+deltaSourceWidth_l p reserve)+5) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def numQuery_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 7) : Term ((4+deltaSourceWidth_l p reserve)+7) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def numProgramParams {k} (T ω n L r : Term k) : Fin 5 → Term k :=
  Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => T))))

@[simp] private theorem numProgramParams_at0_l {k} (T ω n L r : Term k) :
    numProgramParams T ω n L r (0 : Fin 5) = r := rfl

@[simp] private theorem numProgramParams_at1_l {k} (T ω n L r : Term k) :
    numProgramParams T ω n L r (1 : Fin 5) = L := rfl

@[simp] private theorem numProgramParams_at2_l {k} (T ω n L r : Term k) :
    numProgramParams T ω n L r (2 : Fin 5) = n := rfl

@[simp] private theorem numProgramParams_at3_l {k} (T ω n L r : Term k) :
    numProgramParams T ω n L r (3 : Fin 5) = ω := rfl

@[simp] private theorem numProgramParams_at4_l {k} (T ω n L r : Term k) :
    numProgramParams T ω n L r (4 : Fin 5) = T := rfl

@[simp] private theorem numProgramParams_closed_l {k} (T ω n L r : Term k)
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : n.freeSupport = []) (hL : L.freeSupport = []) (hr : r.freeSupport = []) :
    ∀ i, (numProgramParams T ω n L r i).freeSupport = [] :=
  Fin.cases hr (Fin.cases hL (Fin.cases hn (Fin.cases hω (fun _ => hT))))

private def canonicalPredicateNumberedResult_m {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 (4+deltaSourceWidth_l p reserve) :=
  .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (.mem (numResult_m p reserve 4) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (Formula.isTransitive (numResult_m p reserve 4)) <|
    .conj (.mem (numResult_m p reserve 3) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (.mem (numResult_m p reserve 2) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (.mem (numResult_m p reserve 1) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (.mem (numResult_m p reserve 0) (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken) <|
    .conj (.mem (numResult_m p reserve 0) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (pboundedFormula_m (numResult_m p reserve 4) (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken (numResult_m p reserve 2) (numResult_m p reserve 3)) <|
    .conj (.mem (numResult_m p reserve 1) (numResult_m p reserve 2)) <|
    .conj (programNumber_m (𝒞 := kpair_convention_l) (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken (numResult_m p reserve 2) (numResult_m p reserve 3) (numResult_m p reserve 1) (numResult_m p reserve 0)) <|
    .conj (within_m pprogramCode_s (numProgramParams (numResult_m p reserve 4) (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken (numResult_m p reserve 2) (numResult_m p reserve 1)) (numResult_m p reserve 3) (numResult_m p reserve 0) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
    .conj (.forallE <| .forallE <| .imp (Formula.isTransitive (numQuery_m p reserve 1)) <|
      .conj (compiledPredicateNumberedQuery_m a true φ (fun i => (numSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken.weaken)
        (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken.weaken (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (numQuery_m p reserve 1) (numQuery_m p reserve 2) (numQuery_m p reserve 0))
        (compiledPredicateNumberedQuery_m a false φ (fun i => (numSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken.weaken)
          (numOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken.weaken (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (numQuery_m p reserve 1) (numQuery_m p reserve 2) (numQuery_m p reserve 0))) <|
    (.forallE <| .forallE <| .imp (.mem (numQuery_m p reserve 1) (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken) <|
      .imp (Formula.isTransitive (numQuery_m p reserve 1)) <| .imp (.mem (numQuery_m p reserve 0) (numQuery_m p reserve 1)) <|
        .existsE <| .conj (.mem .newest (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken) <|
          .conj (Formula.isFunctionSpace kpair_convention_l .newest (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (numQuery_m p reserve 1).weaken)
            (protectedAssignmentQuery_m a (fun i => (numSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
              (numOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest (numOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (numQuery_m p reserve 1).weaken))

private def canonicalPredicateNumberedBody {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 2)) <| .imp (jh_value_m (.bound 2) (.bound 1)) <|
      .imp (Formula.isOmega .newest) <| .imp (.mem .newest (.bound 1)) <|
        .existsE <| existsBlock_m (deltaSourceWidth_l p reserve) <|
          .conj (.mem (numOld_m p reserve 0) (numOld_m p reserve 2)) <|
            .conj (registerFrame_m (deltaSourceWidth_l p reserve) (numOld_m p reserve 0) (numSlot_m p reserve)) <|
              .conj (finConj_m (deltaSourceWidth_l p reserve) (fun i => .mem (numSlot_m p reserve i) (numOld_m p reserve 2)))
                (canonicalPredicateNumberedResult_m a reserve p φ)

theorem canonicalPredicateNumberedBody_closed_l {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) :
    (canonicalPredicateNumberedBody a reserve p φ).FreeClosed := by
  simp -implicitDefEqProofs [canonicalPredicateNumberedBody,canonicalPredicateNumberedResult_m,numOld_m,numSlot_m,numSource_m,
    numResult_m,numQuery_m,registerFrame_closed_l,compiledPredicateNumberedQuery_closed_l,protectedAssignmentQuery_closed_l,
    sourceTerm_m,Definitional.Formula.FreeClosed,hc]

def canonicalPredicateNumberedSentence {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) : Sentence :=
  .ofFormula (canonicalPredicateNumberedBody a reserve p φ) (canonicalPredicateNumberedBody_closed_l a reserve p φ hc)

theorem canonicalPredicateNumberedCompilation_models {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalPredicateNumberedSentence a reserve p φ hc) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (canonicalPredicateNumberedBody a reserve p φ)
  simp only [canonicalPredicateNumberedBody,canonicalPredicateNumberedResult_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,existsBlock_sat_l,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,
    registerFrame_sat_l hZF.1,finConj_sat_l,pboundedFormula_sat_l (ZF.modelsKP hZF),
    programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,within_sat_l,Within_d,pprogramCode_matrix_sat_l (ZF.modelsKP hZF),
    compiledPredicateNumberedQuery_sat_l hZF.1,protectedAssignmentQuery_sat_l hZF.1,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,numOld_m,numSlot_m,numSource_m,numResult_m,numQuery_m,
    numProgramParams_at0_l,numProgramParams_at1_l,numProgramParams_at2_l,numProgramParams_at3_l,numProgramParams_at4_l,oldTerm_eval_l,sourceTerm_eval_l]
  intro α C ω hα hC hω hωC
  obtain ⟨n,slots,U,G,K,r,e,compiled,he,heC,code,smallCode,_⟩ := jh_canonicalPredicate_numbered_l hZF a reserve φ p hp hc parsed hα hC hω hωC
  refine ⟨n,slots,compiled.arity_mem,compiled.frame,compiled.slots_mem,U,G,K,r,e,compiled.container_mem,compiled.container_transitive,
    compiled.program_mem,compiled.length_mem,compiled.root_mem,he,heC,compiled.valid,compiled.root_bound,code,?_,?_,?_⟩
  · obtain ⟨w,hwC,body⟩ := smallCode
    refine ⟨w,hwC,?_⟩
    change ∃ H, M.mem H w ∧ ∃ c, M.mem c w ∧ ∃ b, M.mem b w ∧ ∃ R, M.mem R w ∧
      ∃ Q, M.mem Q w ∧ ∃ p, M.mem p w ∧ ∃ q, M.mem q w ∧ PProgramCheck_d U ω n K G r e H c b R Q p q
    exact (pprogramCode_matrix_sat_l (ZF.modelsKP hZF) (predicateProgramCodeEnv_l U ω n K r) G e w).mp body
  · intro X f hx
    constructor
    · intro σ fn corr
      let ρ : Env M d := ⟨σ,free⟩
      let η : Env M 2 := ⟨Fin.cases (σ a) (fun _ : Fin 1 => ω),free⟩
      exact (pnumberedTruth_fixed_l (M := M) hZF true η hω compiled.valid code hx (fn0_function_l (ZF.modelsKP hZF) fn)).trans
        (compiled.correct X f ρ hx fn corr).1
    · intro σ fn corr
      let ρ : Env M d := ⟨σ,free⟩
      let η : Env M 2 := ⟨Fin.cases (σ a) (fun _ : Fin 1 => ω),free⟩
      exact (pnumberedTruth_fixed_l (M := M) hZF false η hω compiled.valid code hx (fn0_function_l (ZF.modelsKP hZF) fn)).trans
        ((compiled.correct X f ρ hx fn corr).2.trans (Formula.satisfies_neg_iff ρ φ).symm)
  · intro X default hXC hx inhabited
    obtain ⟨E,hEC,full,all⟩ := compiled.realizes X default hXC hx inhabited
    refine ⟨E,hEC,full,fun σ values => ?_⟩
    obtain ⟨f,hfE,hfC,fn,corr,_⟩ := all (⟨σ,free⟩ : Env M d) values
    exact ⟨f,hfE,hfC,fn,corr⟩

theorem canonicalPredicateNumberedCompilation_derives {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPredicateNumberedSentence a reserve p φ hc) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalPredicateNumberedCompilation_models a reserve φ p hp hc parsed M hM)

def predicateNumberedCompilationSentence {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) : Sentence :=
  canonicalPredicateNumberedSentence a reserve (parsedSourceTest_l φ hp.delta0_l hc) φ hc

theorem predicateNumberedCompilation_derives {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (predicateNumberedCompilationSentence a reserve φ hp hc) :=
  canonicalPredicateNumberedCompilation_derives a reserve φ (parsedSourceTest_l φ hp.delta0_l hc) hp hc
    (parsedSourceTest_some_l φ hp.delta0_l hc)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
