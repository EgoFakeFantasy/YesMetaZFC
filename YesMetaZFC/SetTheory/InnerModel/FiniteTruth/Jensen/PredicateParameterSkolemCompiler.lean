import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolemSource

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

structure PredicateParameterSkolemSource_d (hKP : M.Models KP) {d} (a : Fin d) (φ : Formula 1 (d+1)) (C ω e k empty : M.Domain) : Prop where
  zero : Num_d 0 empty
  empty_mem : M.mem empty C
  count : Num_d d k
  count_mem : M.mem k C
  number_natural : M.mem e ω
  number_mem : M.mem e C
  program : ∃ T n L F r, PBoundedFormula_d T ω n L F ∧ ProgramNumber_d (kp_pair_l hKP) ω n L F r e ∧ M.mem k n
  sound : ∀ (params input y : M.Domain) (σ : Env M d), SourceParameter_d (fun j => if j = a then empty else σ.bound j) params → Rd_triple_d input e k params →
    predicateParameterSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input y → Formula.satisfies (σ.push y) φ
  local_total : ∀ (X params input : M.Domain) (σ : Env M d), AmenableSet_d C (σ.bound a) → M.mem input C → Fn0_d k X params →
    SourceParameter_d (fun j => if j = a then empty else σ.bound j) params → Rd_triple_d input e k params → (∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) →
      ∃ z, M.mem z C ∧ Within_d predicateParameterSkolem_s (predicateSkolem_env_l a ω σ) input z C ∧ Formula.satisfies (σ.push z) φ ∧
        ∀ t, predicateParameterSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input t → t = z
  realizes : ∀ σ : Env M d, (∀ j, j ≠ a → M.mem (σ.bound j) C) → ∃ X params input, M.mem X C ∧ M.TransitiveSet X ∧
    M.mem params C ∧ M.mem input C ∧ Fn0_d k X params ∧ SourceParameter_d (fun j => if j = a then empty else σ.bound j) params ∧ Rd_triple_d input e k params
  parameter_unique : ∀ (X Y params b : M.Domain) (σ : Env M d), Fn0_d k X params → Fn0_d k Y b →
    SourceParameter_d (fun j => if j = a then empty else σ.bound j) params → SourceParameter_d (fun j => if j = a then empty else σ.bound j) b → params = b

/-- 同一实际原代码先于所有源环境存在；规范参数列和函数覆盖全部固定原 Δ₀ 模板。 -/
theorem jh_predicateParameterSkolem_sourceCompile_l (hZF : M.Models ZF) {d} (a : Fin d) (reserve : Nat)
    (φ : Formula 1 (d+1)) (p : Cp_test (d+1)) (hp : PredicateDelta0 a.succ φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ e k empty, PredicateParameterSkolemSource_d (ZF.modelsKP hZF) a φ C ω e k empty := by
  obtain ⟨n,slots,T,F,L,r,compiled⟩ := jh_canonicalPredicate_compile_l hZF a.succ reserve φ p hp hc parsed hα h hω hωC
  obtain ⟨e,he,code⟩ := pprogramNumber_exists_l hZF hω compiled.valid compiled.root_bound
  obtain ⟨empty,hzero⟩ := num_exists_l (ZF.modelsKP hZF) 0
  obtain ⟨k,hk⟩ := num_exists_l (ZF.modelsKP hZF) d
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hEmptyC := trans ω hωC empty (num_mem_l hZF.1 hω hzero)
  have heC := trans ω hωC e he
  have hkC := trans ω hωC k (num_mem_l hZF.1 hω hk)
  let v := predicateSourceRegisters_l p reserve slots
  have vn : ∀ j, Num_d j.val (v j) := fun j => compiled.frame.slots ⟨j.val,by unfold deltaSourceWidth_l; omega⟩
  have vi : Function.Injective v := compiled.frame.prefix_injective_l (ZF.modelsKP hZF) (by unfold deltaSourceWidth_l; omega)
  have kn := num_lt_l hZF.1 hk compiled.frame.arity (by unfold deltaSourceWidth_l; omega)
  have correct : PWitnessSourceCorrect_d a φ v T ω n L F r := fun X g η hx fn corr => (compiled.correct X g η hx fn corr).1
  refine ⟨e,k,empty,hzero,hEmptyC,hk,hkC,he,heC,⟨T,n,L,F,r,compiled.valid,code,kn⟩,?_,?_,?_,?_⟩
  · intro params input y σ corr outer selected
    exact predicateParameterSkolem_source_sound_l hZF (predicateSkolem_env_l a ω σ) a empty σ rfl hω compiled.valid code outer hk vn vi correct corr selected
  · intro X params input σ amenable hinC ha corr outer source
    exact jh_predicateParameterSkolem_source_function_l hZF hα h (predicateSkolem_env_l a ω σ) a empty σ rfl amenable hω hωC hinC compiled.valid code outer hk kn vn vi correct ha corr source
  · intro σ values
    obtain ⟨X,params,hXC,hx,haC,fn,corr⟩ := jh_sourceParameter_realize_l hZF hα h hω hωC hk (fun j => if j = a then empty else σ.bound j)
      (fun j => by
        by_cases hj : j = a
        · simpa only [if_pos hj] using hEmptyC
        · simpa only [if_neg hj] using values j hj)
    obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total k params
    obtain ⟨input,hinput⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
    have outer : Rd_triple_d input e k params := ⟨q,hq,hinput⟩
    have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e k params heC hkC haC input (rd_triple_value_l hZF.1 outer)
    exact ⟨X,params,input,hXC,hx,haC,hinC,fn,corr,outer⟩
  · intro X Y params b σ ha hb ca cb
    exact sourceParameter_unique_l (ZF.modelsKP hZF) hk ha hb ca cb


/-- 相同普通源值给出同一个完整参数图和输入包，即使谓词槽或求值域不同。 -/
theorem PredicateParameterSkolemSource_d.input_invariant_l (hKP : M.Models KP) {d a}
    {φ : Formula 1 (d+1)} {C ω e k empty : M.Domain}
    (result : PredicateParameterSkolemSource_d hKP a φ C ω e k empty)
    (σ τ : Env M d) (ordinary : ∀ j, j ≠ a → σ.bound j = τ.bound j)
    {X Y params other input input' : M.Domain}
    (left : Fn0_d k X params) (right : Fn0_d k Y other)
    (lc : SourceParameter_d (fun j => if j = a then empty else σ.bound j) params)
    (rc : SourceParameter_d (fun j => if j = a then empty else τ.bound j) other)
    (lp : Rd_triple_d input e k params) (rp : Rd_triple_d input' e k other) :
    params = other ∧ input = input' := by
  have masked : (fun j => if j = a then empty else σ.bound j) =
      (fun j => if j = a then empty else τ.bound j) := by
    funext j
    by_cases hj : j = a
    · simp only [if_pos hj]
    · simpa only [if_neg hj] using ordinary j hj
  have eq := result.parameter_unique X Y params other σ left right lc (by rw [masked]; exact rc)
  subst other
  exact ⟨rfl,normalizedTriple_unique_l hKP.1 lp rp⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
