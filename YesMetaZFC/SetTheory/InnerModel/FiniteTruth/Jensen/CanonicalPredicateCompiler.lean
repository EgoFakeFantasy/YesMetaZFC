import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProtectedDelta0Compiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalDelta0Compiler

/-! # 全原有界谓词模板的规范共享代码及真实赋值实现

指定谓词槽的寄存器不用来存 A；实现时填域内默认值，只有其余普通条目对应。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure CanonicalPredicateDelta0_d (hKP : M.Models KP) {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d)
    (C ω n : M.Domain) (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) (U G K r : M.Domain) : Prop where
  frame : RegisterFrame_d (deltaSourceWidth_l p reserve) n slots
  arity_mem : M.mem n C
  slots_mem : ∀ i, M.mem (slots i) C
  container_mem : M.mem U C
  container_transitive : M.TransitiveSet U
  program_mem : M.mem G C
  length_mem : M.mem K C
  root_mem : M.mem r C
  valid : PBoundedFormula_d U ω n K G
  root_bound : M.mem r K
  correct : ∀ (X f : M.Domain) (ρ : Env M d), M.TransitiveSet X → Fn0_d n X f →
    (∀ i, i ≠ a → Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) →
      (PFiniteTruth_d true U (ρ.bound a) ω n X G K r f ↔ Formula.satisfies ρ φ) ∧
      (PFiniteTruth_d false U (ρ.bound a) ω n X G K r f ↔ ¬ Formula.satisfies ρ φ)
  realizes : ∀ X default, M.mem X C → M.TransitiveSet X → M.mem default X →
    ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l hKP) E n X ∧
      ∀ ρ : Env M d, (∀ i, i ≠ a → M.mem (ρ.bound i) X) →
        ∃ f, M.mem f E ∧ M.mem f C ∧ Fn0_d n X f ∧
          (∀ i, i ≠ a → Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) ∧
          (PFiniteTruth_d true U (ρ.bound a) ω n X G K r f ↔ Formula.satisfies ρ φ) ∧
          (PFiniteTruth_d false U (ρ.bound a) ω n X G K r f ↔ ¬ Formula.satisfies ρ φ)

theorem jh_canonicalPredicate_compile_l (hZF : M.Models ZF) {d} (a : Fin d) (reserve : Nat)
    (φ : Formula 1 d) (p : Cp_test d) (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ slots : Fin (deltaSourceWidth_l p reserve) → M.Domain, ∃ U G K r,
      CanonicalPredicateDelta0_d (ZF.modelsKP hZF) a reserve p φ C ω n slots U G K r := by
  classical
  obtain ⟨n,slots,hnC,frame,slotsC⟩ := jh_registerFrame_l hZF (deltaSourceWidth_l p reserve) hα hC hω hωC
  let indices := layoutPrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  let v := layoutValues_l slots indices
  have bound : ∀ i, M.mem (v i) n := frame.prefix_bound_l hZF.1 (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  have injective : Function.Injective v := frame.prefix_injective_l (ZF.modelsKP hZF)
    (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  have hn := frame.omega_l hZF.1 hω
  obtain ⟨e,he,heω⟩ := hω.1.1
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) hC
  have heC := trans ω hωC e heω
  have empty : PBoundedFormula_d ω ω n e e := (boundedFormula_empty_l hn heω he).predicate_l
  obtain ⟨U,G,K,r,result⟩ := jh_parsedPredicate_compile_l hZF slots frame a φ p hp hc parsed d indices
    (layoutPrefix_safe_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega))
    (deltaSourceWidth_budget_l p reserve) hα hC hω hωC hωC heC empty
  refine ⟨n,slots,U,G,K,r,frame,hnC,slotsC,result.container_mem,result.container_transitive,
    result.program_mem,result.length_mem,trans K result.length_mem r result.root_bound,result.extension.valid,result.root_bound,
    (fun X f ρ hx fn corr => ⟨result.correct X f ρ hx (fn0_function_l (ZF.modelsKP hZF) fn) corr,
      (result.correct_polarity_l hZF false hω X f ρ hx (fn0_function_l (ZF.modelsKP hZF) fn) corr).trans
        (Formula.satisfies_neg_iff ρ φ)⟩),fun X default hXC hx inhabited => ?_⟩
  obtain ⟨E,hEC,full,all⟩ := jh_assignment_realize_l hZF v hα hC hω hωC hXC hn bound injective inhabited
  refine ⟨E,hEC,full,fun ρ values => ?_⟩
  let σ : Fin d → M.Domain := fun i => if i = a then default else ρ.bound i
  have valuesσ : ∀ i, M.mem (σ i) X := by
    intro i
    by_cases eq : i = a
    · simpa only [σ,if_pos eq] using inhabited
    · simpa only [σ,if_neg eq] using values i eq
  obtain ⟨f,hfE,hfC,fn,corr⟩ := all σ valuesσ
  have ordinary : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f := by
    intro i different
    simpa only [σ,if_neg different] using corr i
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  exact ⟨f,hfE,hfC,fn,ordinary,result.correct X f ρ hx ff ordinary,
    (result.correct_polarity_l hZF false hω X f ρ hx ff ordinary).trans (Formula.satisfies_neg_iff ρ φ)⟩

/-- 同一完整编译代码在实际 amenable 谓词层内也准确解释原模板。 -/
theorem CanonicalPredicateDelta0_d.local_correct_l (hZF : M.Models ZF) (positive : Bool) {d a reserve}
    {p : Cp_test d} {φ : Formula 1 d} {α C ω n U G K r : M.Domain}
    {slots : Fin (deltaSourceWidth_l p reserve) → M.Domain}
    (compiled : CanonicalPredicateDelta0_d (ZF.modelsKP hZF) a reserve p φ C ω n slots U G K r)
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (ρ : Env M d) (amenable : AmenableSet_d C (ρ.bound a))
    (hω : M.IsOmega ω) (hωC : M.mem ω C) {X f : M.Domain} (hXC : M.mem X C) (hx : M.TransitiveSet X)
    (fn : Fn0_d n X f)
    (corr : ∀ i, i ≠ a → Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) :
    Within_d (pfiniteTruth_s positive) (pfiniteTruth_env_l U (ρ.bound a) ω n X G K) r f C ↔
      Formula.satisfies ρ (if positive then φ else .neg φ) := by
  let η := pfiniteTruth_env_l U (ρ.bound a) ω n X G K
  have params : ∀ i : Fin 6, M.mem (η.bound i.succ) C := Fin.cases compiled.length_mem
    (Fin.cases compiled.program_mem (Fin.cases hXC (Fin.cases compiled.arity_mem (Fin.cases hωC (fun _ => compiled.container_mem)))))
  have source := jh_pfiniteTruth_within_l hZF positive hα hC η amenable params hω compiled.valid r f
  cases positive
  · exact source.trans ((compiled.correct X f ρ hx fn corr).2.trans (Formula.satisfies_neg_iff ρ φ).symm)
  · exact source.trans (compiled.correct X f ρ hx fn corr).1

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
