import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.Delta0SourceCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RegisterFrame

/-! # 规范框架中的完整有界源编译

寄存器由模型数码自动生成；源寄存器取框架前缀，槽零用作常量占位。
代码在源环境之前选择，同层完整空间随后实现每个域内源环境。这里给出
任意模型中的组合定理，统一原对象句子由 CanonicalDelta0ObjectTheorems 提供。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def deltaSourceWidth_l {d} (p : Cp_test d) (reserve : Nat) : Nat :=
  d + sourceDepth_l (sourceToCore_l p) + reserve + 1

theorem deltaSourceWidth_budget_l {d} (p : Cp_test d) (reserve : Nat) :
    d + sourceDepth_l (sourceToCore_l p) < deltaSourceWidth_l p reserve := by
  unfold deltaSourceWidth_l
  omega

/-- 对原有限 AST 的确定性解析，不从任意模型选择语法对象。 -/
def parsedSourceTest_l {d} (φ : Formula 1 d) (hd : φ.IsDelta0) (hc : φ.FreeClosed) : Cp_test d :=
  (cp_parse_l φ).get (cp_parse_some_l hd hc)

theorem parsedSourceTest_some_l {d} (φ : Formula 1 d) (hd : φ.IsDelta0) (hc : φ.FreeClosed) :
    cp_parse_l φ = some (parsedSourceTest_l φ hd hc) := by
  exact (Option.some_get (cp_parse_some_l hd hc)).symm

structure CanonicalDelta0_d (hKP : M.Models KP) {d} (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d)
    (C ω n : M.Domain) (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) (U G K r : M.Domain) : Prop where
  frame : RegisterFrame_d (deltaSourceWidth_l p reserve) n slots
  arity_mem : M.mem n C
  slots_mem : ∀ i, M.mem (slots i) C
  container_mem : M.mem U C
  container_transitive : M.TransitiveSet U
  program_mem : M.mem G C
  length_mem : M.mem K C
  root_mem : M.mem r C
  valid : BoundedFormula_d U ω n K G
  root_bound : M.mem r K
  correct : ∀ (X f : M.Domain) (ρ : Env M d), M.TransitiveSet X → Fn0_d n X f →
    (∀ i, Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) →
      (FiniteTruth_d true U ω n X G K r f ↔ Formula.satisfies ρ φ) ∧
      (FiniteTruth_d false U ω n X G K r f ↔ ¬ Formula.satisfies ρ φ)
  realizes : ∀ X default, M.mem X C → M.TransitiveSet X → M.mem default X →
    ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l hKP) E n X ∧
      ∀ ρ : Env M d, (∀ i, M.mem (ρ.bound i) X) →
        ∃ f, M.mem f E ∧ M.mem f C ∧ Fn0_d n X f ∧
          (∀ i, Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) ∧
          (FiniteTruth_d true U ω n X G K r f ↔ Formula.satisfies ρ φ) ∧
          (FiniteTruth_d false U ω n X G K r f ↔ ¬ Formula.satisfies ρ φ)

/-- 按实际正规化量词深度选取框架，生成全部原 Δ₀ 源构造的同层程序。 -/
theorem jh_canonicalDelta0_compile_l (hZF : M.Models ZF) {d} (reserve : Nat)
    (φ : Formula 1 d) (p : Cp_test d)
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {a C ω : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ slots : Fin (deltaSourceWidth_l p reserve) → M.Domain, ∃ U G K r,
      CanonicalDelta0_d (ZF.modelsKP hZF) reserve p φ C ω n slots U G K r := by
  obtain ⟨n,slots,hnC,frame,slotsC⟩ := jh_registerFrame_l hZF (deltaSourceWidth_l p reserve) ha h hω hωC
  let indices := layoutPrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  let v := layoutValues_l slots indices
  have bound : ∀ i, M.mem (v i) n := frame.prefix_bound_l hZF.1 (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  have injective : Function.Injective v := frame.prefix_injective_l (ZF.modelsKP hZF) (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)
  have hn := frame.omega_l hZF.1 hω
  obtain ⟨e,he,heω⟩ := hω.1.1
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have heC := trans ω hωC e heω
  have empty : BoundedFormula_d ω ω n e e := boundedFormula_empty_l hn heω he
  obtain ⟨U,G,K,r,result⟩ := jh_parsedDeltaSource_compile_l hZF slots frame φ p hd hc parsed
    d indices (layoutPrefix_safe_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega)) (deltaSourceWidth_budget_l p reserve) ha h hω hωC hωC heC empty
  refine ⟨n,slots,U,G,K,r,frame,hnC,slotsC,result.container_mem,result.container_transitive,
    result.program_mem,result.length_mem,trans K result.length_mem r result.root_bound,
    result.extension.valid,result.root_bound,
    (fun X f ρ hx fn corr => ⟨result.correct X f ρ hx (fn0_function_l (ZF.modelsKP hZF) fn) corr,
      (result.correct_polarity_l hZF false hω X f ρ hx (fn0_function_l (ZF.modelsKP hZF) fn) corr).trans
        (Formula.satisfies_neg_iff ρ φ)⟩),
    fun X default hXC hx inhabited => ?_⟩
  obtain ⟨E,hEC,full,all⟩ := jh_assignment_realize_l hZF v ha h hω hωC hXC hn bound injective inhabited
  refine ⟨E,hEC,full,fun ρ values => ?_⟩
  obtain ⟨f,hfE,hfC,fn,corr⟩ := all ρ.bound values
  have hf := fn0_function_l (ZF.modelsKP hZF) fn
  exact ⟨f,hfE,hfC,fn,corr,result.correct X f ρ hx hf corr,
    (result.correct_polarity_l hZF false hω X f ρ hx hf corr).trans (Formula.satisfies_neg_iff ρ φ)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
