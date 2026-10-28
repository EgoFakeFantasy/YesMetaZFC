import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.VariableBlocks
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.BooleanCompiler

/-! # 编译结果的原对象全赋值查询

把固定模板的源变量作为量词块引入；所有代码参数在该块外，源公式通过
实际重命名进入块内。查询同时保留合法赋值与全部寄存器条目对应。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

def querySourceValue_m (n : Nat) {d} (i : Fin d) : Term (n+d) := .bound (sourceIndex_l n d i)

theorem querySourceValue_eval_l {n d} (ρ : Env M n) (σ : Fin d → M.Domain) (i : Fin d) :
    (querySourceValue_m n i).eval (blockEnv_l ρ σ) = σ i := blockEnv_source_l ρ σ i

private def compiledQueryParams {n d} (T ω arity X F L : Term n) : Fin 6 → Term (n+d) :=
  Fin.cases (oldTerm_m L) (Fin.cases (oldTerm_m F) (Fin.cases (oldTerm_m X)
    (Fin.cases (oldTerm_m arity) (Fin.cases (oldTerm_m ω) (fun _ => oldTerm_m T)))))

def compiledBooleanQuery_m {n d} (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (T ω arity X F L r f : Term n) : Formula 1 n :=
  forallBlock_m d <| .imp (fn0_m (oldTerm_m arity) (oldTerm_m X) (oldTerm_m f)) <|
    .imp (finConj_m d (fun i => rd_entry0_m (oldTerm_m (v i)) (querySourceValue_m n i) (oldTerm_m f))) <|
      .iff (binary_pred_m (finiteTruth_s positive).schema (compiledQueryParams T ω arity X F L) (oldTerm_m r) (oldTerm_m f))
        ((if positive then φ else .neg φ).rename (sourceIndex_l n d))

/-- 原对象变量块与所有对应源环境准确一致；正负模板均适用。 -/
theorem compiledBooleanQuery_sat_l (hKP : M.Models KP) {n d} (ρ : Env M n)
    (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n) (T ω arity X F L r f : Term n) :
    Formula.satisfies ρ (compiledBooleanQuery_m positive φ v T ω arity X F L r f) ↔
      ∀ σ : Fin d → M.Domain, Fn0_d (arity.eval ρ) (X.eval ρ) (f.eval ρ) →
        (∀ i, Rd_entry_d ((v i).eval ρ) (σ i) (f.eval ρ)) →
          (FiniteTruth_d positive (T.eval ρ) (ω.eval ρ) (arity.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ) ↔
            Formula.satisfies (⟨σ,ρ.free⟩ : Env M d) (if positive then φ else .neg φ)) := by
  have h0 : compiledQueryParams (d := d) T ω arity X F L (0 : Fin 6) = oldTerm_m L := rfl
  have h1 : compiledQueryParams (d := d) T ω arity X F L (1 : Fin 6) = oldTerm_m F := rfl
  have h2 : compiledQueryParams (d := d) T ω arity X F L (2 : Fin 6) = oldTerm_m X := rfl
  have h3 : compiledQueryParams (d := d) T ω arity X F L (3 : Fin 6) = oldTerm_m arity := rfl
  have h4 : compiledQueryParams (d := d) T ω arity X F L (4 : Fin 6) = oldTerm_m ω := rfl
  have h5 : compiledQueryParams (d := d) T ω arity X F L (5 : Fin 6) = oldTerm_m T := rfl
  simp only [compiledBooleanQuery_m,forallBlock_sat_l,Formula.satisfies_imp_iff,
    fn0_sat_l hKP.1,finConj_sat_l,rd_entry0_sat_l hKP.1,Formula.satisfies_iff_iff,
    binary_pred_sat_l,finiteTruth_sat_l hKP,h0,h1,h2,h3,h4,h5,
    oldTerm_eval_l,querySourceValue_eval_l,sourceRename_sat_l]

theorem compiledBooleanQuery_closed_l {n d} (positive : Bool) (φ : Formula 1 d) (v : Fin d → Term n)
    (T ω arity X F L r f : Term n) (hc : φ.FreeClosed) (hv : ∀ i, (v i).freeSupport = [])
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : arity.freeSupport = [])
    (hX : X.freeSupport = []) (hF : F.freeSupport = []) (hL : L.freeSupport = [])
    (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (compiledBooleanQuery_m positive φ v T ω arity X F L r f).FreeClosed := by
  have params : ∀ i, (compiledQueryParams (d := d) T ω arity X F L i).freeSupport = [] :=
    Fin.cases ((oldTerm_support_l (k := d) L).trans hL)
      (Fin.cases ((oldTerm_support_l (k := d) F).trans hF)
        (Fin.cases ((oldTerm_support_l (k := d) X).trans hX)
          (Fin.cases ((oldTerm_support_l (k := d) arity).trans hn)
            (Fin.cases ((oldTerm_support_l (k := d) ω).trans hω)
              (fun _ => (oldTerm_support_l (k := d) T).trans hT)))))
  have query := binary_pred_closed_l (finiteTruth_s positive).schema (compiledQueryParams T ω arity X F L)
    (oldTerm_m (k := d) r) (oldTerm_m (k := d) f) params
    ((oldTerm_support_l r).trans hr) ((oldTerm_support_l f).trans hf)
  cases positive <;> simp -implicitDefEqProofs [compiledBooleanQuery_m,querySourceValue_m,
    Definitional.Formula.FreeClosed,hc,hv,hn,hX,hf,query]


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
