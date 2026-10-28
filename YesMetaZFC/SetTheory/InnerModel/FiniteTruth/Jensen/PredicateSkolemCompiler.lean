import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumericSkolemSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramNumberExists

/-! # 实际规范函数与原源公式的语义桥接

本模块给任意模型的源语义对应和自动同层源覆盖；原逐模板源句子的组合封装另行验收。
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

def predicateSkolem_env_l {d} (a : Fin d) (ω : M.Domain) (σ : Env M d) : Env M 2 :=
  ⟨Fin.cases (σ.bound a) (fun _ => ω),σ.free⟩

/-- 原完整编译器的规范前缀寄存器，槽零承担新源 binder 的见证。 -/
def predicateSourceRegisters_l {d} (p : Cp_test (d+1)) (reserve : Nat)
    (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) : Fin (d+1) → M.Domain :=
  framePrefix_l (by unfold deltaSourceWidth_l; omega) slots

/-- 同一源程序和同一数码的实际源覆盖；语义模式由固定原模板索引。 -/
structure PredicateNumericSkolemSource_d (hKP : M.Models KP) {d} (a : Fin d) (reserve : Nat) (p : Cp_test (d+1)) (φ : Formula 1 (d+1))
    (C ω n : M.Domain) (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) (T F L r e : M.Domain) : Prop where
  compiled : CanonicalPredicateDelta0_d hKP a.succ reserve p φ C ω n slots T F L r
  number_natural : M.mem e ω
  number_mem : M.mem e C
  code : ProgramNumber_d (kp_pair_l hKP) ω n L F r e
  sound : ∀ (f input y : M.Domain) (σ : Env M d), Rd_triple_d input e f (predicateSourceRegisters_l p reserve slots 0) →
    (∀ j, j ≠ a → Rd_entry_d (predicateSourceRegisters_l p reserve slots j.succ) (σ.bound j) f) →
    predicateNumericSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input y → Formula.satisfies (σ.push y) φ
  realizes : ∀ X default, M.mem X C → M.TransitiveSet X → M.mem default X →
    ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l hKP) E n X ∧
      ∀ σ : Env M d, (∀ j, j ≠ a → M.mem (σ.bound j) X) → ∃ f input, M.mem f E ∧ M.mem f C ∧ M.mem input C ∧ Fn0_d n X f ∧
        Rd_triple_d input e f (predicateSourceRegisters_l p reserve slots 0) ∧
        ∀ j, j ≠ a → Rd_entry_d (predicateSourceRegisters_l p reserve slots j.succ) (σ.bound j) f
  local_total : ∀ (X f input : M.Domain) (σ : Env M d), AmenableSet_d C (σ.bound a) → M.mem input C →
    M.IsSetFunctionFromTo (kp_pair_l hKP) f n X → Rd_triple_d input e f (predicateSourceRegisters_l p reserve slots 0) →
    (∀ j, j ≠ a → Rd_entry_d (predicateSourceRegisters_l p reserve slots j.succ) (σ.bound j) f) →
    (∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) →
      ∃ z, M.mem z C ∧ Within_d predicateNumericSkolem_s (predicateSkolem_env_l a ω σ) input z C ∧ Formula.satisfies (σ.push z) φ ∧
        ∀ t, predicateNumericSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input t → t = z

/-- 自动生成同层原数码、实际参数输入及规范函数的全部原源语义。 -/
theorem jh_predicateNumericSkolem_sourceCompile_l (hZF : M.Models ZF) {d} (a : Fin d) (reserve : Nat)
    (φ : Formula 1 (d+1)) (p : Cp_test (d+1)) (hp : PredicateDelta0 a.succ φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ slots : Fin (deltaSourceWidth_l p reserve) → M.Domain, ∃ T F L r e,
      PredicateNumericSkolemSource_d (ZF.modelsKP hZF) a reserve p φ C ω n slots T F L r e := by
  obtain ⟨n,slots,T,F,L,r,compiled⟩ := jh_canonicalPredicate_compile_l hZF a.succ reserve φ p hp hc parsed hα h hω hωC
  obtain ⟨e,he,code⟩ := pprogramNumber_exists_l hZF hω compiled.valid compiled.root_bound
  have heC := jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC e he
  let v := predicateSourceRegisters_l p reserve slots
  have vb : ∀ j, M.mem (v j) n := compiled.frame.prefix_bound_l hZF.1 (by unfold deltaSourceWidth_l; omega)
  have vi : Function.Injective v := compiled.frame.prefix_injective_l (ZF.modelsKP hZF) (by unfold deltaSourceWidth_l; omega)
  have correct : PWitnessSourceCorrect_d a φ v T ω n L F r := fun X g η hx fn corr => (compiled.correct X g η hx fn corr).1
  refine ⟨n,slots,T,F,L,r,e,compiled,he,heC,code,?_,?_,?_⟩
  · intro f input y σ packet corr selected
    exact predicateNumericSkolem_source_sound_l hZF (predicateSkolem_env_l a ω σ) a σ rfl hω compiled.valid code packet vi correct corr selected
  · intro X default hXC hx inhabited
    obtain ⟨E,hEC,full,all⟩ := compiled.realizes X default hXC hx inhabited
    refine ⟨E,hEC,full,fun σ values => ?_⟩
    have allValues : ∀ j, j ≠ a.succ → M.mem ((σ.push default).bound j) X :=
      Fin.cases (fun _ => inhabited) (fun j hj => values j (fun eq => hj (congrArg Fin.succ eq)))
    obtain ⟨f,hfE,hfC,fn,corr,_⟩ := all (σ.push default) allValues
    obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f (v 0)
    obtain ⟨input,hinput⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
    have packet : Rd_triple_d input e f (v 0) := ⟨q,hq,hinput⟩
    have hvC : M.mem (v 0) C := compiled.slots_mem ⟨0,by unfold deltaSourceWidth_l; omega⟩
    have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e f (v 0) heC hfC hvC input (rd_triple_value_l hZF.1 packet)
    exact ⟨f,input,hfE,hfC,hinC,fn,packet,fun j hj => corr j.succ (fun eq => hj ((by simpa using eq)))⟩
  · intro X f input σ amenable hinC hf packet corr he
    exact jh_predicateNumericSkolem_source_function_l hZF hα h (predicateSkolem_env_l a ω σ) a σ rfl amenable hω hωC hinC
      compiled.valid code packet (vb 0) vi correct hf corr he


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
