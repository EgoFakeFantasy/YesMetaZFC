import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProtectedSourceAppend
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProtectedCoreSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.RegisterLayout

/-! # 全原谓词有界模板的实际递归编译

原解析/正规化分类用于结构归纳；普通变量的条目对应不包含指定谓词槽。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_protectedCore_compile_l (hZF : M.Models ZF) {width n} (slots : Fin width → M.Domain)
    (frame : RegisterFrame_d width n slots) {d} {a : Fin d} {p : Cp_test d} (form : ProtectedCore_d a p)
    (next : Nat) (indices : Fin d → Fin width) (safe : RegisterLayout_d next indices)
    (budget : next + sourceDepth_l p < width) {α C T ω F L : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) :
    ∃ U G K r, PSourceAppend_d (ZF.modelsKP hZF) a (layoutValues_l slots indices) (cp_test_formula_l p)
      C T ω n F L U G K r := by
  induction form generalizing next T F L with
  | falsum a =>
    have room : 0 < width := by omega
    obtain ⟨U,G,K,r,result⟩ := jh_psourceFalsum_l hZF a (layoutValues_l slots indices)
      hα hC hω hωC hTC hFC valid (frame.bound_l hZF.1 ⟨0,room⟩)
    exact ⟨U,G,K,r,result⟩
  | truth a =>
    have room : 0 < width := by omega
    obtain ⟨U,G,K,result⟩ := jh_psourceTruth_l hZF a (layoutValues_l slots indices)
      hα hC hω hωC hTC hFC valid (frame.bound_l hZF.1 ⟨0,room⟩)
    exact ⟨U,G,K,L,result⟩
  | mem a i j hi =>
    classical
    by_cases hj : j = a
    · subst j
      obtain ⟨U,G,K,result⟩ := jh_psourcePredicate_l hZF a (layoutValues_l slots indices) i hi
        hα hC hω hωC hTC hFC valid (fun k => frame.bound_l hZF.1 (indices k))
      exact ⟨U,G,K,L,result⟩
    · obtain ⟨U,G,K,result⟩ := jh_psourceAtomic_l hZF false a (layoutValues_l slots indices) i j hi hj
        hα hC hω hωC hTC hFC valid (fun k => frame.bound_l hZF.1 (indices k))
      exact ⟨U,G,K,L,result⟩
  | eq a i j hi hj =>
    obtain ⟨U,G,K,result⟩ := jh_psourceAtomic_l hZF true a (layoutValues_l slots indices) i j hi hj
      hα hC hω hωC hTC hFC valid (fun k => frame.bound_l hZF.1 (indices k))
    exact ⟨U,G,K,L,result⟩
  | @nor _ a p q _ _ ihp ihq =>
    change next + max (sourceDepth_l p) (sourceDepth_l q) < width at budget
    have bp : next + sourceDepth_l p < width := by
      have maxBound := Nat.le_max_left (sourceDepth_l p) (sourceDepth_l q)
      omega
    have bq : next + sourceDepth_l q < width := by
      have maxBound := Nat.le_max_right (sourceDepth_l p) (sourceDepth_l q)
      omega
    obtain ⟨U,G,K,r,left⟩ := ihp next indices safe bp hTC hFC valid
    obtain ⟨V,H,J,s,right⟩ := ihq next indices safe bq left.container_mem left.program_mem left.extension.valid
    obtain ⟨W,N,O,result⟩ := jh_psourceNor_l hZF hα hC hω hωC left right
    exact ⟨W,N,O,J,result⟩
  | @any _ a q different p _ ih =>
    change next + (sourceDepth_l p + 1) < width at budget
    have room : next < width := by omega
    have childBudget : (next+1) + sourceDepth_l p < width := by omega
    obtain ⟨V,H,J,k,body⟩ := ih (next+1) (layoutPush_l next indices room) (safe.push_l room) childBudget hTC hFC valid
    rw [layoutValues_push_l] at body
    obtain ⟨W,N,O,result⟩ := jh_psourceExists_l hZF a q different hα hC hω hωC body
      (frame.bound_l hZF.1 ⟨next,room⟩) (frame.bound_l hZF.1 (indices q)) (safe.fresh_l (ZF.modelsKP hZF) frame room)
    exact ⟨W,N,O,J,result⟩

theorem jh_parsedPredicate_compile_l (hZF : M.Models ZF) {width n} (slots : Fin width → M.Domain)
    (frame : RegisterFrame_d width n slots) {d} (a : Fin d) (φ : Formula 1 d) (p : Cp_test d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    (next : Nat) (indices : Fin d → Fin width) (safe : RegisterLayout_d next indices)
    (budget : next + sourceDepth_l (sourceToCore_l p) < width) {α C T ω F L : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) :
    ∃ U G K r, PSourceAppend_d (ZF.modelsKP hZF) a (layoutValues_l slots indices) φ C T ω n F L U G K r := by
  obtain ⟨q,other,core⟩ := predicate_parse_core_l hp hc
  have eq := Option.some.inj (other.symm.trans parsed)
  subst q
  obtain ⟨U,G,K,r,result⟩ := jh_protectedCore_compile_l hZF slots frame core next indices safe budget hα hC hω hωC hTC hFC valid
  exact ⟨U,G,K,r,result.congr_l (fun ρ => (sourceToCore_sat_l p ρ).trans
    (parsedSource_sat_l (ZF.modelsKP hZF) hp.delta0_l hc parsed ρ))⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
