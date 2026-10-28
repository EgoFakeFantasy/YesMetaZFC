import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedSourceCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedObjectTheorems

/-! # 全原谓词模板接入同一个原自然数编号和双参数数码源 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def predicateProgramCodeEnv_l (T ω n L r : M.Domain) : Env M 5 :=
  ⟨Fin.cases r (Fin.cases L (Fin.cases n (Fin.cases ω (fun _ => T)))),fun _ => ω⟩

theorem jh_canonicalPredicate_numbered_l (hZF : M.Models ZF) {d} (a : Fin d) (reserve : Nat)
    (φ : Formula 1 d) (p : Cp_test d) (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ slots : Fin (deltaSourceWidth_l p reserve) → M.Domain, ∃ U G K r e,
      CanonicalPredicateDelta0_d (ZF.modelsKP hZF) a reserve p φ C ω n slots U G K r ∧
        M.mem e ω ∧ M.mem e C ∧ ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n K G r e ∧
          Within_d pprogramCode_s (predicateProgramCodeEnv_l U ω n K r) G e C ∧
            ∀ (positive : Bool) (X f : M.Domain) (ρ : Env M d), M.TransitiveSet X → Fn0_d n X f →
              (∀ i, i ≠ a → Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) →
                ((pnumberedTruth_s positive).schema.denote (pnumberedTruth_env_l (ρ.bound a) ω) e f ↔
                  Formula.satisfies ρ (if positive then φ else .neg φ)) := by
  obtain ⟨n,slots,U,G,K,r,compiled⟩ := jh_canonicalPredicate_compile_l hZF a reserve φ p hp hc parsed hα hC hω hωC
  obtain ⟨e,he,code⟩ := pprogramNumber_exists_l hZF hω compiled.valid compiled.root_bound
  have heC := jh_value_transitive_l (ZF.models_kpi_l hZF) hC ω hωC e he
  have localCode := (jh_pprogramCode_within_l hZF hα hC (predicateProgramCodeEnv_l U ω n K r) G e hω hωC).mpr ⟨compiled.valid,code⟩
  refine ⟨n,slots,U,G,K,r,e,compiled,he,heC,code,localCode,fun positive X f ρ hx fn corr => ?_⟩
  have semantic := pnumberedTruth_fixed_l hZF positive (pnumberedTruth_env_l (ρ.bound a) ω)
    hω compiled.valid code hx (fn0_function_l (ZF.modelsKP hZF) fn)
  cases positive
  · exact semantic.trans ((compiled.correct X f ρ hx fn corr).2.trans (Formula.satisfies_neg_iff ρ φ).symm)
  · exact semantic.trans (compiled.correct X f ρ hx fn corr).1

/-- 同一原数码在实际 amenable 谓词层内解释为原模板的两个极性。 -/
theorem canonicalPredicate_numbered_local_l (hZF : M.Models ZF) (positive : Bool) {d a reserve}
    {p : Cp_test d} {φ : Formula 1 d} {α C ω n U G K r e : M.Domain}
    {slots : Fin (deltaSourceWidth_l p reserve) → M.Domain}
    (compiled : CanonicalPredicateDelta0_d (ZF.modelsKP hZF) a reserve p φ C ω n slots U G K r)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n K G r e)
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M d) (amenable : AmenableSet_d C (ρ.bound a)) {X f : M.Domain}
    (hXC : M.mem X C) (hx : M.TransitiveSet X) (fn : Fn0_d n X f)
    (corr : ∀ i, i ≠ a → Rd_entry_d (framePrefix_l (show d ≤ deltaSourceWidth_l p reserve by unfold deltaSourceWidth_l; omega) slots i) (ρ.bound i) f) :
    Within_d (pnumberedTruth_s positive) (pnumberedTruth_env_l (ρ.bound a) ω) e f C ↔
      Formula.satisfies ρ (if positive then φ else .neg φ) := by
  let η := pnumberedTruth_env_l (ρ.bound a) ω
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  have hfC := jh_finite_function_mem_l hZF hα hC hω hωC hXC compiled.valid.variables ff
  have localSource := (jh_pnumberedTruth_within_l hZF positive hα hC η e f amenable hω hωC hfC).trans
    (pnumberedTruth_sat_l hZF positive η e f hω).symm
  have semantic := pnumberedTruth_fixed_l hZF positive η hω compiled.valid code hx ff
  cases positive
  · exact localSource.trans (semantic.trans ((compiled.correct X f ρ hx fn corr).2.trans (Formula.satisfies_neg_iff ρ φ).symm))
  · exact localSource.trans (semantic.trans (compiled.correct X f ρ hx fn corr).1)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
