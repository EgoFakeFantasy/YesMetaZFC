import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BooleanSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.SourceAppend

/-! # 原布尔源公式的真实同层递归编译

沿上游 Cp_test 的或非片段递归，逐个追加实际内部程序；先编译右子式时也
保留已生成的左根。结果统一覆盖所有合法赋值。寄存器映射和一个界内占位
寄存器显式给定；逐模板对象推导由 BooleanCompilerObjectTheorems 提供，
子集与有界量词仍待编译。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 或非片段在任意已有程序后实际生成，所有代码对象留在同一原 J 层。 -/
theorem jh_norSource_compile_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    {p : Cp_test d} (form : NorSource_d p) {a C T ω n F L dummy : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hv : ∀ i, M.mem (v i) n) (hdummy : M.mem dummy n) :
    ∃ U G K r, SourceAppend_d (ZF.modelsKP hZF) v (cp_test_formula_l p) C T ω n F L U G K r := by
  induction form generalizing T F L with
  | falsum => exact jh_sourceFalsumAppend_l hZF v ha h hω hωC hTC hFC valid hdummy
  | truth =>
    obtain ⟨U,G,K,result⟩ := jh_sourceTruthAppend_l hZF v ha h hω hωC hTC hFC valid hdummy
    exact ⟨U,G,K,L,result⟩
  | mem i j =>
    obtain ⟨U,G,K,result⟩ := jh_sourceAtomicAppend_l hZF false v i j ha h hω hωC hTC hFC valid hv
    exact ⟨U,G,K,L,result⟩
  | eq i j =>
    obtain ⟨U,G,K,result⟩ := jh_sourceAtomicAppend_l hZF true v i j ha h hω hωC hTC hFC valid hv
    exact ⟨U,G,K,L,result⟩
  | nor _ _ ihp ihq =>
    obtain ⟨U,G,K,r,left⟩ := ihp hTC hFC valid
    obtain ⟨V,H,J,s,right⟩ := ihq left.container_mem left.program_mem left.extension.valid
    obtain ⟨W,N,O,result⟩ := jh_sourceNorAppend_l hZF ha h hω hωC left right
    exact ⟨W,N,O,J,result⟩

/-- 成员、相等、常量及全部无量词布尔联结词，均生成真实同层内部程序。 -/
theorem jh_booleanSource_compile_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    (p : Cp_test d) (form : BooleanSource_d p) {a C T ω n F L dummy : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hv : ∀ i, M.mem (v i) n) (hdummy : M.mem dummy n) :
    ∃ U G K r, SourceAppend_d (ZF.modelsKP hZF) v (cp_test_formula_l p) C T ω n F L U G K r := by
  obtain ⟨U,G,K,r,result⟩ := jh_norSource_compile_l hZF v (booleanToNor_shape_l p form)
    ha h hω hωC hTC hFC valid hv hdummy
  exact ⟨U,G,K,r,result.congr_l (fun ρ => booleanToNor_sat_l p form ρ)⟩

/-- 从原 Project 解析得到的片段，可经精确往返连接到同层程序。 -/
theorem jh_parsedBooleanSource_compile_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    (φ : Formula 1 d) (p : Cp_test d) (form : BooleanSource_d p)
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {a C T ω n F L dummy : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hv : ∀ i, M.mem (v i) n) (hdummy : M.mem dummy n) :
    ∃ U G K r, SourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r := by
  obtain ⟨U,G,K,r,result⟩ := jh_booleanSource_compile_l hZF v p form ha h hω hωC hTC hFC valid hv hdummy
  exact ⟨U,G,K,r,result.congr_l (fun ρ => parsedSource_sat_l (ZF.modelsKP hZF) hd hc parsed ρ)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
