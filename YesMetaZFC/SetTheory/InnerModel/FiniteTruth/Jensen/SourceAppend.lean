import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramExtension
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AtomicAppend

/-! # 源公式连续编译的同层组合接口

每份结果包含真实程序扩展、同层对象预算、根的内部界和所有合法赋值上的
源语义对应。这里的外部公式参数不是模型内部统一真值谓词；布尔片段的
逐模板对象推导由 BooleanCompilerObjectTheorems 提供，量词新鲜变量布局仍待完成。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure SourceAppend_d (hKP : M.Models KP) {d} (v : Fin d → M.Domain) (φ : Formula 1 d)
    (C T ω n F L U G K r : M.Domain) : Prop where
  extension : ProgramExtension_d T ω n F L U G K
  container_mem : M.mem U C
  container_transitive : M.TransitiveSet U
  program_mem : M.mem G C
  length_mem : M.mem K C
  root_bound : M.mem r K
  correct : ∀ (X f : M.Domain) (ρ : Env M d),
    M.IsSetFunctionFromTo (kp_pair_l hKP) f n X → (∀ i, Rd_entry_d (v i) (ρ.bound i) f) →
      (FiniteTruth_d true U ω n X G K r f ↔ Formula.satisfies ρ φ)

/-- 同一实际程序可沿源公式的逐环境语义等价重新给出规格。 -/
theorem SourceAppend_d.congr_l {hKP : M.Models KP} {d} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : SourceAppend_d hKP v φ C T ω n F L U G K r)
    (same : ∀ ρ : Env M d, Formula.satisfies ρ φ ↔ Formula.satisfies ρ ψ) :
    SourceAppend_d hKP v ψ C T ω n F L U G K r :=
  ⟨compiled.extension,compiled.container_mem,compiled.container_transitive,compiled.program_mem,
    compiled.length_mem,compiled.root_bound,fun X f ρ hf corr => (compiled.correct X f ρ hf corr).trans (same ρ)⟩

/-- 已有结果作为自身前缀的恒等扩展，复用同一根和全部语义。 -/
theorem SourceAppend_d.stay_l {hKP : M.Models KP} {d} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : SourceAppend_d hKP v φ C T ω n F L U G K r) :
    SourceAppend_d hKP v φ C U ω n G K U G K r :=
  ⟨ProgramExtension_d.refl_l hKP compiled.extension.valid,compiled.container_mem,
    compiled.container_transitive,compiled.program_mem,compiled.length_mem,compiled.root_bound,compiled.correct⟩

theorem jh_sourceAtomicAppend_l (hZF : M.Models ZF) (equal : Bool) {d} (v : Fin d → M.Domain) (p q : Fin d)
    {a C T ω n F L : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hFC : M.mem F C)
    (valid : BoundedFormula_d T ω n L F) (hv : ∀ i, M.mem (v i) n) :
    ∃ U G K, SourceAppend_d (ZF.modelsKP hZF) v (atomicRelation_m equal (.bound p) (.bound q))
      C T ω n F L U G K L := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,_,program⟩ := jh_atomicAppend_l hZF equal ha h hω hωC hTC hFC valid (hv p) (hv q)
  exact ⟨U,G,K,program.extension_l valid sub,hUC,hu,hGC,hKC,program.length.predecessor_mem,
    fun X f ρ hf corr => sourceAtomicAppend_compile_l hZF true equal v ρ p q hω program hf corr⟩

/-- 常真使用一个给定的界内占位寄存器；它可不属于源变量映射。 -/
theorem jh_sourceTruthAppend_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    {a C T ω n F L dummy : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hFC : M.mem F C)
    (valid : BoundedFormula_d T ω n L F) (hdummy : M.mem dummy n) :
    ∃ U G K, SourceAppend_d (ZF.modelsKP hZF) v .truth C T ω n F L U G K L := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,_,program⟩ := jh_atomicAppend_l hZF true ha h hω hωC hTC hFC valid hdummy hdummy
  refine ⟨U,G,K,program.extension_l valid sub,hUC,hu,hGC,hKC,program.length.predecessor_mem,fun X f ρ hf _ => ?_⟩
  obtain ⟨a,hia⟩ := (hf.2.1 dummy).mp hdummy
  have result := atomicAppend_eval_l hZF true true hω program hf hia hia
  simpa only [AtomicAnswer_d,AtomicRelation_d,↓reduceIte,Formula.satisfies_truth_iff,eq_self_iff_true] using result

/-- 先编译左子式，再在其程序后编译右子式，最后追加真实或非。 -/
theorem jh_sourceNorAppend_l (hZF : M.Models ZF) {d} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {a C T ω n F L U G K r V H J s : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (left : SourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r)
    (right : SourceAppend_d (ZF.modelsKP hZF) v ψ C U ω n G K V H J s) :
    ∃ W N O, SourceAppend_d (ZF.modelsKP hZF) v (norAnswer_m true φ ψ) C T ω n F L W N O J := by
  obtain ⟨W,N,O,c,hWC,hw,sub,hNC,hOC,_,program,correct⟩ := jh_norAppend_compile_l hZF ha h hω hωC
    right.container_mem right.program_mem right.extension.valid
    (right.extension.lengths r left.root_bound) right.root_bound
  refine ⟨W,N,O,(left.extension.trans_l (ZF.modelsKP hZF) right.extension).trans_l (ZF.modelsKP hZF)
    (program.extension_l right.extension.valid sub),hWC,hw,hNC,hOC,program.length.predecessor_mem,fun X f ρ hf corr => ?_⟩
  have l := (right.extension.query_l hZF true hω left.root_bound).symm.trans (left.correct X f ρ hf corr)
  exact (correct true X f hf).trans ((norAnswer_congr_l true l (right.correct X f ρ hf corr)).trans
    (norAnswer_sat_l true ρ φ ψ).symm)

theorem jh_sourceNegAppend_l (hZF : M.Models ZF) {d} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {a C T ω n F L U G K r : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (compiled : SourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r) :
    ∃ W N O s, SourceAppend_d (ZF.modelsKP hZF) v (.neg φ) C T ω n F L W N O s := by
  obtain ⟨W,N,O,result⟩ := jh_sourceNorAppend_l hZF ha h hω hωC compiled compiled.stay_l
  refine ⟨W,N,O,K,result.congr_l ?_⟩
  intro ρ
  simp only [norAnswer_m,↓reduceIte,Formula.satisfies_neg_iff,Formula.satisfies_disj_iff,or_self]

theorem jh_sourceFalsumAppend_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    {a C T ω n F L dummy : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hFC : M.mem F C)
    (valid : BoundedFormula_d T ω n L F) (hdummy : M.mem dummy n) :
    ∃ U G K r, SourceAppend_d (ZF.modelsKP hZF) v .falsum C T ω n F L U G K r := by
  obtain ⟨U,G,K,truth⟩ := jh_sourceTruthAppend_l hZF v ha h hω hωC hTC hFC valid hdummy
  obtain ⟨W,N,O,r,result⟩ := jh_sourceNegAppend_l hZF ha h hω hωC truth
  refine ⟨W,N,O,r,result.congr_l ?_⟩
  intro ρ
  simp only [Formula.satisfies_neg_iff,Formula.satisfies_truth_iff,Formula.satisfies_falsum_iff,not_true_eq_false]

/-- 同一实际编译结果同时给出原源公式的正负查询正确性。 -/
theorem SourceAppend_d.correct_polarity_l (hZF : M.Models ZF) (positive : Bool) {d}
    {v : Fin d → M.Domain} {φ : Formula 1 d} {C T ω n F L U G K r : M.Domain}
    (compiled : SourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r)
    (hω : M.IsOmega ω) (X f : M.Domain) (ρ : Env M d)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ i, Rd_entry_d (v i) (ρ.bound i) f) :
    FiniteTruth_d positive U ω n X G K r f ↔ Formula.satisfies ρ (if positive then φ else .neg φ) := by
  cases positive
  · exact (finiteTruth_complement_l hZF hω compiled.extension.valid hf).trans
      ((not_congr (compiled.correct X f ρ hf corr)).trans (Formula.satisfies_neg_iff ρ φ).symm)
  · exact compiled.correct X f ρ hf corr

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
