import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SourceParameterSequence
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSkolemCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolemSource

/-! # 原源模板的参数列与规范参数 Skolem 接线 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem predicateParameterSkolem_source_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {d} (a : Fin d) (empty : M.Domain) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e k params input y : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (outer : Rd_triple_d input e k params) (hk : Num_d d k) (slots : ∀ j, Num_d j.val (v j))
    (injective : Function.Injective v) (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (corr : SourceParameter_d (fun j => if j = a then empty else σ.bound j) params) (selected : predicateParameterSkolem_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ := by
  obtain ⟨packet,normal,choice⟩ := (predicateParameterSkolem_sat_l hZF ρ input y).mp selected
  obtain ⟨X,z,f,inner,parameters⟩ := (pnormalizedInput_fixed_l hZF ρ hω valid code outer).mp normal
  obtain ⟨zeroEq,baseCorr⟩ := parameterCheck_source_l hZF hω hk slots parameters corr
  have inner' : Rd_triple_d packet e f (v 0) := zeroEq ▸ inner
  have ordinary : ∀ j, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f := by
    intro j hj
    simpa only [if_neg hj] using baseCorr j
  exact predicateNumericSkolem_source_sound_l hZF ρ a σ predicateParam hω valid code inner' injective correct ordinary choice

/-- 每个层内源见证都传到规范化后的同一实际函数；参数图不依赖求值域。 -/
theorem jh_predicateParameterSkolem_source_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {d} (a : Fin d) (empty : M.Domain) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e k params input : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (outer : Rd_triple_d input e k params) (hk : Num_d d k) (kn : M.mem k n) (slots : ∀ j, Num_d j.val (v j))
    (injective : Function.Injective v) (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (ha : Fn0_d k X params) (corr : SourceParameter_d (fun j => if j = a then empty else σ.bound j) params)
    (existsSource : ∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) :
    ∃ z, M.mem z C ∧ Within_d predicateParameterSkolem_s ρ input z C ∧ Formula.satisfies (σ.push z) φ ∧
      ∀ t, predicateParameterSkolem_s.schema.denote ρ input t → t = z := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have details := outer
  obtain ⟨q,hq,hinput⟩ := details
  have ec := po_pair_bound_l trans hinC hinput
  have aC := (po_pair_bound_l trans ec.2 hq).2
  obtain ⟨Y,f,hYC,_,hfC,parameters⟩ := jh_parameterDomain_l hZF hα h hω hωC aC valid.variables kn (slots 0) ha
  have baseCorr := (parameterCheck_source_l hZF hω hk slots parameters corr).2
  have ordinary : ∀ j, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f := by
    intro j hj
    simpa only [if_neg hj] using baseCorr j
  obtain ⟨q',hq'⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f (v 0)
  obtain ⟨packet,hpacket⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q'
  have inner : Rd_triple_d packet e f (v 0) := ⟨q',hq',hpacket⟩
  have hzeroC := trans (ρ.bound 1) hωC (v 0) (num_mem_l hZF.1 hω (slots 0))
  have hpC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e f (v 0) ec.1 hfC hzeroC packet (rd_triple_value_l hZF.1 inner)
  have normal := (pnormalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,Y,e,k,params,v 0,f,outer,inner,parameters,valid,code⟩
  have he : ∃ packet y, M.mem y C ∧ pnormalizedInput_s.schema.denote ρ input packet ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) packet y := by
    obtain ⟨y,hyC,source⟩ := existsSource
    have fiberWithin := jh_pwitnessFiber_source_complete_l hZF hα h ρ a σ predicateParam amenable hω hωC hpC hyC valid code inner
      (parameters.zero_l hZF hω).1 injective correct (fn0_function_l (ZF.modelsKP hZF) parameters.full) ordinary source
    exact ⟨packet,y,hyC,normal,(pwitnessFiber_sat_l hZF ρ packet y hω).mp (within_toSchema_l pwitnessFiber_s ρ fiberWithin)⟩
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_predicateParameterSkolem_function_l hZF hα h ρ amenable hω hωC hinC he
  exact ⟨z,hzC,hz,predicateParameterSkolem_source_sound_l hZF ρ a empty σ predicateParam hω valid code outer hk slots injective correct corr
    (within_toSchema_l predicateParameterSkolem_s ρ hz),unique⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
