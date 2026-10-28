import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalDelta0Compiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramNumberObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CompiledBooleanQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RegisterAssignmentObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 完整 Δ₀ 编译、实际赋值与共享代码的原对象推导

句子自行生成数码框架和程序代码；传递求值域上的源变量由实际函数图实现。
同一代码的正负规格与全部域内源值的实际同层赋值实现都在原对象句子中。
该程序及根的唯一内部自然数编号也在句子中实际存在量化；编号图的局部 Σ₁ 规格仍待完成。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u

private def deltaOld_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 4) : Term (4+(deltaSourceWidth_l p reserve)) :=
  oldTerm_m (.bound i : Term 4)
private def deltaSlot_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin (deltaSourceWidth_l p reserve)) : Term (4+(deltaSourceWidth_l p reserve)) :=
  sourceTerm_m 4 i
private def deltaSource_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin d) : Term (4+(deltaSourceWidth_l p reserve)) :=
  sourceTerm_m 4 ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def deltaResult_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 4) : Term ((4+(deltaSourceWidth_l p reserve))+4) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def deltaQuerySlot_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 6) : Term ((4+(deltaSourceWidth_l p reserve))+6) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩

private def canonicalDelta0Result_m {d} (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 (4+(deltaSourceWidth_l p reserve)) :=
  .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (.mem (deltaResult_m p reserve 3) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
      .conj (Formula.isTransitive (deltaResult_m p reserve 3)) <|
        .conj (.mem (deltaResult_m p reserve 2) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
          .conj (.mem (deltaResult_m p reserve 1) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
            .conj (.mem (deltaResult_m p reserve 0) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
              .conj (boundedFormula_m (deltaResult_m p reserve 3) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken
                (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken (deltaResult_m p reserve 1) (deltaResult_m p reserve 2)) <|
                .conj (.mem (deltaResult_m p reserve 0) (deltaResult_m p reserve 1)) <|
                  .conj (.existsE <| .conj (.mem .newest (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken) <|
                    .conj (.mem .newest (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken) <|
                      programNumber_m (𝒞 := kpair_convention_l)
                        (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken
                        (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken
                        (deltaResult_m p reserve 1).weaken (deltaResult_m p reserve 2).weaken
                        (deltaResult_m p reserve 0).weaken .newest) <|
                  .conj (.forallE <| .forallE <|
                    .imp (Formula.isTransitive (deltaQuerySlot_m p reserve 1)) <|
                    .conj (compiledBooleanQuery_m true φ (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken)
                      (deltaQuerySlot_m p reserve 5) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken
                      (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1)
                      (deltaQuerySlot_m p reserve 4) (deltaQuerySlot_m p reserve 3) (deltaQuerySlot_m p reserve 2) (deltaQuerySlot_m p reserve 0))
                      (compiledBooleanQuery_m false φ (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken)
                        (deltaQuerySlot_m p reserve 5) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken
                        (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1)
                        (deltaQuerySlot_m p reserve 4) (deltaQuerySlot_m p reserve 3) (deltaQuerySlot_m p reserve 2) (deltaQuerySlot_m p reserve 0))) <|
                    .forallE <| .forallE <|
                      .imp (.mem (deltaQuerySlot_m p reserve 1) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken) <|
                        .imp (Formula.isTransitive (deltaQuerySlot_m p reserve 1)) <|
                        .imp (.mem (deltaQuerySlot_m p reserve 0) (deltaQuerySlot_m p reserve 1)) <|
                          .existsE <| .conj (.mem .newest (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken) <|
                            .conj (Formula.isFunctionSpace kpair_convention_l .newest
                              (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1).weaken)
                              (assignmentInSpaceQuery_m (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken.weaken)
                                (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest
                                (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1).weaken)

private def canonicalDelta0Body {d} (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 2)) <| .imp (jh_value_m (.bound 2) (.bound 1)) <|
      .imp (Formula.isOmega .newest) <| .imp (.mem .newest (.bound 1)) <|
        .existsE <| existsBlock_m (deltaSourceWidth_l p reserve) <|
          .conj (.mem (deltaOld_m p reserve 0) (deltaOld_m p reserve 2)) <|
            .conj (registerFrame_m (deltaSourceWidth_l p reserve) (deltaOld_m p reserve 0) (deltaSlot_m p reserve)) <|
              .conj (finConj_m (deltaSourceWidth_l p reserve) (fun i => .mem (deltaSlot_m p reserve i) (deltaOld_m p reserve 2)))
                (canonicalDelta0Result_m reserve p φ)

theorem canonicalDelta0Body_closed_l {d} (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) :
    (canonicalDelta0Body reserve p φ).FreeClosed := by
  simp -implicitDefEqProofs [canonicalDelta0Body,canonicalDelta0Result_m,deltaOld_m,deltaSlot_m,deltaSource_m,
    deltaResult_m,deltaQuerySlot_m,registerFrame_closed_l,compiledBooleanQuery_closed_l,assignmentInSpaceQuery_closed_l,
    sourceTerm_m,Definitional.Formula.FreeClosed,hc]

def canonicalDelta0Sentence {d} (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) : Sentence :=
  .ofFormula (canonicalDelta0Body reserve p φ) (canonicalDelta0Body_closed_l reserve p φ hc)

theorem canonicalDelta0Compilation_models {d} (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalDelta0Sentence reserve p φ hc) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (canonicalDelta0Body reserve p φ)
  simp only [canonicalDelta0Body,canonicalDelta0Result_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,existsBlock_sat_l,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,
    registerFrame_sat_l hZF.1,finConj_sat_l,boundedFormula_sat_l (ZF.modelsKP hZF),
    programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    compiledBooleanQuery_sat_l (ZF.modelsKP hZF),assignmentInSpaceQuery_sat_l hZF.1,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,deltaOld_m,deltaSlot_m,deltaSource_m,
    deltaResult_m,deltaQuerySlot_m,oldTerm_eval_l,sourceTerm_eval_l]
  intro a C ω ha h hω hωC
  obtain ⟨n,slots,U,G,K,r,result⟩ := jh_canonicalDelta0_compile_l hZF reserve φ p hd hc parsed ha h hω hωC
  obtain ⟨e,he,num⟩ := programNumber_exists_l hZF hω result.valid result.root_bound
  have heC := jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC e he
  refine ⟨n,slots,result.arity_mem,result.frame,result.slots_mem,U,G,K,r,result.container_mem,result.container_transitive,
    result.program_mem,result.length_mem,result.root_mem,result.valid,result.root_bound,⟨e,he,heC,num⟩,?_,?_⟩
  · intro X f hx
    constructor
    · intro σ fn corr
      exact (result.correct X f (⟨σ,envFree⟩ : Env M d) hx fn corr).1
    · intro σ fn corr
      exact ((result.correct X f (⟨σ,envFree⟩ : Env M d) hx fn corr).2).trans
        (Formula.satisfies_neg_iff (⟨σ,envFree⟩ : Env M d) φ).symm
  · intro X default hXC hx inhabited
    obtain ⟨E,hEC,full,all⟩ := result.realizes X default hXC hx inhabited
    refine ⟨E,hEC,full,fun σ values => ?_⟩
    obtain ⟨f,hfE,hfC,fn,corr,_⟩ := all (⟨σ,envFree⟩ : Env M d) values
    exact ⟨f,hfE,hfC,fn,corr⟩

theorem canonicalDelta0Compilation_derives {d} (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalDelta0Sentence reserve p φ hc) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalDelta0Compilation_models reserve φ p hd hc parsed M hM)

theorem canonicalDelta0Test_derives {d} (reserve : Nat) (p : Cp_test d) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF
      (canonicalDelta0Sentence reserve p (cp_test_formula_l p) (cp_test_closed_l p)) :=
  canonicalDelta0Compilation_derives reserve (cp_test_formula_l p) p
    (cp_test_delta_l p) (cp_test_closed_l p) (cp_parse_test_l p)

/-- 原 Δ₀ 公式由确定性解析直接给出对象句子，不要求调用者提供语法证书对象。 -/
def delta0CompilationSentence {d} (reserve : Nat) (φ : Formula 1 d) (hd : φ.IsDelta0) (hc : φ.FreeClosed) : Sentence :=
  canonicalDelta0Sentence reserve (parsedSourceTest_l φ hd hc) φ hc

/-- 任意固定原 Δ₀ 模板的完整规范编译，在原 ZF 推导核内可证。 -/
theorem delta0Compilation_derives {d} (reserve : Nat) (φ : Formula 1 d) (hd : φ.IsDelta0) (hc : φ.FreeClosed) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (delta0CompilationSentence reserve φ hd hc) :=
  canonicalDelta0Compilation_derives reserve φ (parsedSourceTest_l φ hd hc) hd hc (parsedSourceTest_some_l φ hd hc)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
