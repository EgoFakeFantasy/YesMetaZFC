import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CoreSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.RegisterLayout
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.TransitiveSourceAppend

/-! # 全部原有界源指令的实际同层递归编译

布局计数器与正规化后的量词深度共同给出槽预算。每个 binder 实际选取新槽，
正文用更新后的源环境解释；全部代码由同层真实追加生成。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_coreSource_compile_l (hZF : M.Models ZF) {width n} (slots : Fin width → M.Domain)
    (frame : RegisterFrame_d width n slots) {d} {p : Cp_test d} (form : CoreSource_d p)
    (next : Nat) (indices : Fin d → Fin width) (safe : RegisterLayout_d next indices)
    (budget : next + sourceDepth_l p < width) {a C T ω F L : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F) :
    ∃ U G K r, TransSourceAppend_d (ZF.modelsKP hZF) (layoutValues_l slots indices) (cp_test_formula_l p)
      C T ω n F L U G K r := by
  induction form generalizing next T F L with
  | falsum =>
    have room : 0 < width := by omega
    obtain ⟨U,G,K,r,result⟩ := jh_sourceFalsumAppend_l hZF (layoutValues_l slots indices)
      ha h hω hωC hTC hFC valid (frame.bound_l hZF.1 ⟨0,room⟩)
    exact ⟨U,G,K,r,result.transitive_l⟩
  | truth =>
    have room : 0 < width := by omega
    obtain ⟨U,G,K,result⟩ := jh_sourceTruthAppend_l hZF (layoutValues_l slots indices)
      ha h hω hωC hTC hFC valid (frame.bound_l hZF.1 ⟨0,room⟩)
    exact ⟨U,G,K,L,result.transitive_l⟩
  | mem i j =>
    obtain ⟨U,G,K,result⟩ := jh_sourceAtomicAppend_l hZF false (layoutValues_l slots indices) i j
      ha h hω hωC hTC hFC valid (fun i => frame.bound_l hZF.1 (indices i))
    exact ⟨U,G,K,L,result.transitive_l⟩
  | eq i j =>
    obtain ⟨U,G,K,result⟩ := jh_sourceAtomicAppend_l hZF true (layoutValues_l slots indices) i j
      ha h hω hωC hTC hFC valid (fun i => frame.bound_l hZF.1 (indices i))
    exact ⟨U,G,K,L,result.transitive_l⟩
  | @nor _ p q _ _ ihp ihq =>
    change next + max (sourceDepth_l p) (sourceDepth_l q) < width at budget
    have bp : next + sourceDepth_l p < width := by
      have hmax := Nat.le_max_left (sourceDepth_l p) (sourceDepth_l q)
      omega
    have bq : next + sourceDepth_l q < width := by
      have hmax := Nat.le_max_right (sourceDepth_l p) (sourceDepth_l q)
      omega
    obtain ⟨U,G,K,r,left⟩ := ihp next indices safe bp hTC hFC valid
    obtain ⟨V,H,J,s,right⟩ := ihq next indices safe bq left.container_mem left.program_mem left.extension.valid
    obtain ⟨W,N,O,result⟩ := jh_transNorAppend_l hZF ha h hω hωC left right
    exact ⟨W,N,O,J,result⟩
  | @any _ q p _ ih =>
    change next + (sourceDepth_l p + 1) < width at budget
    have room : next < width := by omega
    have childBudget : (next+1) + sourceDepth_l p < width := by omega
    obtain ⟨V,H,J,k,body⟩ := ih (next+1) (layoutPush_l next indices room) (safe.push_l room) childBudget hTC hFC valid
    rw [layoutValues_push_l] at body
    obtain ⟨W,N,O,result⟩ := jh_transExistsAppend_l hZF q ha h hω hωC body
      (frame.bound_l hZF.1 ⟨next,room⟩) (frame.bound_l hZF.1 (indices q)) (safe.fresh_l (ZF.modelsKP hZF) frame room)
    exact ⟨W,N,O,J,result⟩

/-- 原 Cp_test 全部构造均可编译，含子集、有界全称和有界存在。 -/
theorem jh_deltaSource_compile_l (hZF : M.Models ZF) {width n} (slots : Fin width → M.Domain)
    (frame : RegisterFrame_d width n slots) {d} (p : Cp_test d)
    (next : Nat) (indices : Fin d → Fin width) (safe : RegisterLayout_d next indices)
    (budget : next + sourceDepth_l (sourceToCore_l p) < width) {a C T ω F L : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F) :
    ∃ U G K r, TransSourceAppend_d (ZF.modelsKP hZF) (layoutValues_l slots indices) (cp_test_formula_l p)
      C T ω n F L U G K r := by
  obtain ⟨U,G,K,r,result⟩ := jh_coreSource_compile_l hZF slots frame (sourceToCore_shape_l p)
    next indices safe budget ha h hω hωC hTC hFC valid
  exact ⟨U,G,K,r,result.congr_l (fun ρ => sourceToCore_sat_l p ρ)⟩

theorem jh_parsedDeltaSource_compile_l (hZF : M.Models ZF) {width n} (slots : Fin width → M.Domain)
    (frame : RegisterFrame_d width n slots) {d} (φ : Formula 1 d) (p : Cp_test d)
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    (next : Nat) (indices : Fin d → Fin width) (safe : RegisterLayout_d next indices)
    (budget : next + sourceDepth_l (sourceToCore_l p) < width) {a C T ω F L : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F) :
    ∃ U G K r, TransSourceAppend_d (ZF.modelsKP hZF) (layoutValues_l slots indices) φ C T ω n F L U G K r := by
  obtain ⟨U,G,K,r,result⟩ := jh_deltaSource_compile_l hZF slots frame p next indices safe budget ha h hω hωC hTC hFC valid
  exact ⟨U,G,K,r,result.congr_l (fun ρ => parsedSource_sat_l (ZF.modelsKP hZF) hd hc parsed ρ)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
