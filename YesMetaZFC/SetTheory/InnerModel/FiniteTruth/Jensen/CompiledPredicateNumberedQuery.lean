import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CompiledPredicateQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalPredicateNumberedCompiler

/-! # 全原模板的双参数数码查询对象公式 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

private def predicateNumberedQueryParams {n d} (a : Fin d) (ω : Term n) : Fin 2 → Term (n+d) :=
  Fin.cases (querySourceValue_m n a) (fun _ => oldTerm_m ω)

def compiledPredicateNumberedQuery_m {n d} (a : Fin d) (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (ω arity X e f : Term n) : Formula 1 n :=
  forallBlock_m d <| .imp (fn0_m (oldTerm_m arity) (oldTerm_m X) (oldTerm_m f)) <|
    .imp (protectedConj_m a (fun i => rd_entry0_m (oldTerm_m (v i)) (querySourceValue_m n i) (oldTerm_m f))) <|
      .iff (binary_pred_m (pnumberedTruth_s positive).schema (predicateNumberedQueryParams a ω) (oldTerm_m e) (oldTerm_m f))
        ((if positive then φ else .neg φ).rename (sourceIndex_l n d))

private theorem predicateNumberedQuery_env_l {n d} (ρ : Env M n) (σ : Fin d → M.Domain) (a : Fin d) (ω : Term n) :
    (⟨fun i => (predicateNumberedQueryParams a ω i).eval (blockEnv_l ρ σ),(blockEnv_l ρ σ).free⟩ : Env M 2) =
      ⟨Fin.cases (σ a) (fun _ => ω.eval ρ),ρ.free⟩ := by
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact querySourceValue_eval_l ρ σ a
    · exact oldTerm_eval_l ρ σ ω
  · rfl

theorem compiledPredicateNumberedQuery_sat_l (hE : Extensional M) {n d} (ρ : Env M n) (a : Fin d)
    (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n) (ω arity X e f : Term n) :
    Formula.satisfies ρ (compiledPredicateNumberedQuery_m a positive φ v ω arity X e f) ↔
      ∀ σ : Fin d → M.Domain, Fn0_d (arity.eval ρ) (X.eval ρ) (f.eval ρ) →
        (∀ i, i ≠ a → Rd_entry_d ((v i).eval ρ) (σ i) (f.eval ρ)) →
          ((pnumberedTruth_s positive).schema.denote
            (⟨Fin.cases (σ a) (fun _ => ω.eval ρ),ρ.free⟩ : Env M 2) (e.eval ρ) (f.eval ρ) ↔
            Formula.satisfies (⟨σ,ρ.free⟩ : Env M d) (if positive then φ else .neg φ)) := by
  simp only [compiledPredicateNumberedQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,
    fn0_sat_l hE,protectedConj_sat_l,rd_entry0_sat_l hE,Formula.satisfies_iff_iff,
    binary_pred_sat_l,oldTerm_eval_l,querySourceValue_eval_l,sourceRename_sat_l]
  apply forall_congr'
  intro σ
  rw [predicateNumberedQuery_env_l ρ σ a ω]

theorem compiledPredicateNumberedQuery_closed_l {n d} (a : Fin d) (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (ω arity X e f : Term n) (hc : φ.FreeClosed) (hv : ∀ i, (v i).freeSupport = [])
    (hω : ω.freeSupport = []) (hn : arity.freeSupport = []) (hX : X.freeSupport = [])
    (he : e.freeSupport = []) (hf : f.freeSupport = []) :
    (compiledPredicateNumberedQuery_m a positive φ v ω arity X e f).FreeClosed := by
  have params : ∀ i, (predicateNumberedQueryParams (d := d) a ω i).freeSupport = [] :=
    Fin.cases rfl (fun _ => (oldTerm_support_l (k := d) ω).trans hω)
  have query := binary_pred_closed_l (pnumberedTruth_s positive).schema (predicateNumberedQueryParams a ω)
    (oldTerm_m (k := d) e) (oldTerm_m (k := d) f) params
    ((oldTerm_support_l e).trans he) ((oldTerm_support_l f).trans hf)
  cases positive <;> simp -implicitDefEqProofs [compiledPredicateNumberedQuery_m,querySourceValue_m,
    Definitional.Formula.FreeClosed,hc,hv,hn,hX,hf,query]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
