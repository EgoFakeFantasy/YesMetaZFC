import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProtectedBlocks
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CompiledBooleanQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalPredicateCompiler

/-! # 原指定谓词模板的共享代码与普通变量赋值查询 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

private def protectedQueryParams {n d} (a : Fin d) (T ω arity X F L : Term n) : Fin 7 → Term (n+d) :=
  Fin.cases (querySourceValue_m n a) (Fin.cases (oldTerm_m L) (Fin.cases (oldTerm_m F)
    (Fin.cases (oldTerm_m X) (Fin.cases (oldTerm_m arity) (Fin.cases (oldTerm_m ω) (fun _ => oldTerm_m T))))))

def compiledPredicateQuery_m {n d} (a : Fin d) (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (T ω arity X F L r f : Term n) : Formula 1 n :=
  forallBlock_m d <| .imp (fn0_m (oldTerm_m arity) (oldTerm_m X) (oldTerm_m f)) <|
    .imp (protectedConj_m a (fun i => rd_entry0_m (oldTerm_m (v i)) (querySourceValue_m n i) (oldTerm_m f))) <|
      .iff (binary_pred_m (pfiniteTruth_s positive).schema (protectedQueryParams a T ω arity X F L) (oldTerm_m r) (oldTerm_m f))
        ((if positive then φ else .neg φ).rename (sourceIndex_l n d))

theorem compiledPredicateQuery_sat_l (hKP : M.Models KP) {n d} (ρ : Env M n) (a : Fin d)
    (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n) (T ω arity X F L r f : Term n) :
    Formula.satisfies ρ (compiledPredicateQuery_m a positive φ v T ω arity X F L r f) ↔
      ∀ σ : Fin d → M.Domain, Fn0_d (arity.eval ρ) (X.eval ρ) (f.eval ρ) →
        (∀ i, i ≠ a → Rd_entry_d ((v i).eval ρ) (σ i) (f.eval ρ)) →
          (PFiniteTruth_d positive (T.eval ρ) (σ a) (ω.eval ρ) (arity.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ) ↔
            Formula.satisfies (⟨σ,ρ.free⟩ : Env M d) (if positive then φ else .neg φ)) := by
  have h0 : protectedQueryParams (d := d) a T ω arity X F L (0 : Fin 7) = querySourceValue_m n a := rfl
  have h1 : protectedQueryParams (d := d) a T ω arity X F L (1 : Fin 7) = oldTerm_m L := rfl
  have h2 : protectedQueryParams (d := d) a T ω arity X F L (2 : Fin 7) = oldTerm_m F := rfl
  have h3 : protectedQueryParams (d := d) a T ω arity X F L (3 : Fin 7) = oldTerm_m X := rfl
  have h4 : protectedQueryParams (d := d) a T ω arity X F L (4 : Fin 7) = oldTerm_m arity := rfl
  have h5 : protectedQueryParams (d := d) a T ω arity X F L (5 : Fin 7) = oldTerm_m ω := rfl
  have h6 : protectedQueryParams (d := d) a T ω arity X F L (6 : Fin 7) = oldTerm_m T := rfl
  simp only [compiledPredicateQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,
    fn0_sat_l hKP.1,protectedConj_sat_l,rd_entry0_sat_l hKP.1,Formula.satisfies_iff_iff,
    binary_pred_sat_l,pfiniteTruth_sat_l hKP,h0,h1,h2,h3,h4,h5,h6,
    oldTerm_eval_l,querySourceValue_eval_l,sourceRename_sat_l]

theorem compiledPredicateQuery_closed_l {n d} (a : Fin d) (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (T ω arity X F L r f : Term n) (hc : φ.FreeClosed) (hv : ∀ i, (v i).freeSupport = [])
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : arity.freeSupport = [])
    (hX : X.freeSupport = []) (hF : F.freeSupport = []) (hL : L.freeSupport = [])
    (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (compiledPredicateQuery_m a positive φ v T ω arity X F L r f).FreeClosed := by
  have params : ∀ i, (protectedQueryParams a T ω arity X F L i).freeSupport = [] :=
    Fin.cases rfl (Fin.cases ((oldTerm_support_l (k := d) L).trans hL)
      (Fin.cases ((oldTerm_support_l (k := d) F).trans hF)
        (Fin.cases ((oldTerm_support_l (k := d) X).trans hX)
          (Fin.cases ((oldTerm_support_l (k := d) arity).trans hn)
            (Fin.cases ((oldTerm_support_l (k := d) ω).trans hω)
              (fun _ => (oldTerm_support_l (k := d) T).trans hT))))))
  have query := binary_pred_closed_l (pfiniteTruth_s positive).schema (protectedQueryParams a T ω arity X F L)
    (oldTerm_m (k := d) r) (oldTerm_m (k := d) f) params
    ((oldTerm_support_l r).trans hr) ((oldTerm_support_l f).trans hf)
  cases positive <;> simp -implicitDefEqProofs [compiledPredicateQuery_m,querySourceValue_m,
    Definitional.Formula.FreeClosed,hc,hv,hn,hX,hf,query]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
