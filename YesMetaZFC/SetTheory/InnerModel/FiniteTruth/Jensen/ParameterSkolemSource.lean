import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SourceParameterSequence
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NumericSkolemSource

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

theorem parameterSkolem_source_sound_l (hZF : M.Models ZF) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e k a input y : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (outer : Rd_triple_d input e k a) (hk : Num_d d k) (slots : ∀ j, Num_d j.val (v j))
    (injective : Function.Injective v) (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (corr : SourceParameter_d σ.bound a) (selected : parameterSkolem_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ := by
  obtain ⟨packet,normal,choice⟩ := (parameterSkolem_sat_l hZF ρ input y).mp selected
  obtain ⟨X,z,f,inner,parameters⟩ := (normalizedInput_fixed_l hZF ρ hω valid code outer).mp normal
  obtain ⟨zeroEq,baseCorr⟩ := parameterCheck_source_l hZF hω hk slots parameters corr
  have inner' : Rd_triple_d packet e f (v 0) := zeroEq ▸ inner
  exact numericSkolem_source_sound_l hZF ρ σ hω valid code inner' injective correct baseCorr choice

/-- 每个层内源见证都传到规范化后的同一实际函数；参数图不依赖求值域。 -/
theorem jh_parameterSkolem_source_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e k a input : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (outer : Rd_triple_d input e k a) (hk : Num_d d k) (kn : M.mem k n) (slots : ∀ j, Num_d j.val (v j))
    (injective : Function.Injective v) (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (ha : Fn0_d k X a) (corr : SourceParameter_d σ.bound a)
    (existsSource : ∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) :
    ∃ z, M.mem z C ∧ Within_d parameterSkolem_s ρ input z C ∧ Formula.satisfies (σ.push z) φ ∧
      ∀ t, parameterSkolem_s.schema.denote ρ input t → t = z := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have details := outer
  obtain ⟨q,hq,hinput⟩ := details
  have ec := po_pair_bound_l trans hinC hinput
  have aC := (po_pair_bound_l trans ec.2 hq).2
  obtain ⟨Y,f,hYC,_,hfC,parameters⟩ := jh_parameterDomain_l hZF hα h hω hωC aC valid.variables kn (slots 0) ha
  have baseCorr := (parameterCheck_source_l hZF hω hk slots parameters corr).2
  obtain ⟨q',hq'⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f (v 0)
  obtain ⟨packet,hpacket⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q'
  have inner : Rd_triple_d packet e f (v 0) := ⟨q',hq',hpacket⟩
  have hzeroC := trans (ρ.bound 0) hωC (v 0) (num_mem_l hZF.1 hω (slots 0))
  have hpC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e f (v 0) ec.1 hfC hzeroC packet (rd_triple_value_l hZF.1 inner)
  have normal := (normalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,Y,e,k,a,v 0,f,outer,inner,parameters,valid,code⟩
  have he : ∃ packet y, M.mem y C ∧ normalizedInput_s.schema.denote ρ input packet ∧
      WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) packet y := by
    obtain ⟨y,hyC,source⟩ := existsSource
    have fiberWithin := jh_witnessFiber_source_complete_l hZF hα h ρ σ hω hωC hpC hyC valid code inner
      (parameters.zero_l hZF hω).1 injective correct (fn0_function_l (ZF.modelsKP hZF) parameters.full) baseCorr source
    exact ⟨packet,y,hyC,normal,(witnessFiber_sat_l hZF ρ packet y hω).mp (within_toSchema_l witnessFiber_s ρ fiberWithin)⟩
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_parameterSkolem_function_l hZF hα h ρ hω hωC hinC he
  exact ⟨z,hzC,hz,parameterSkolem_source_sound_l hZF ρ σ hω valid code outer hk slots injective correct corr
    (within_toSchema_l parameterSkolem_s ρ hz),unique⟩

/-- 所有层内源参数都有实际同层完整参数列；未以空前提替代输入存在。 -/
theorem jh_sourceParameter_realize_l (hZF : M.Models ZF) {α C ω k : M.Domain} {d}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hk : Num_d d k) (values : Fin d → M.Domain) (inC : ∀ j, M.mem (values j) C) :
    ∃ X a, M.mem X C ∧ M.TransitiveSet X ∧ M.mem a C ∧ Fn0_d k X a ∧ SourceParameter_d values a := by
  obtain ⟨k',positions,_,frame,_⟩ := jh_registerFrame_l hZF d hα h hω hωC
  have eq := num_unique_l hZF.1 frame.arity hk
  subst k'
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  obtain ⟨U,hUC,hu,hωU⟩ := jh_local_enclosure_l (ZF.models_kpi_l hZF) hα h ω hωC
  have covers : ∀ A, A ∈ List.ofFn values → ∃ Y, M.mem Y C ∧ M.TransitiveSet Y ∧ M.mem A Y := by
    intro A hA
    obtain ⟨j,eq⟩ := List.mem_ofFn.mp hA
    subst A
    exact jh_local_enclosure_l (ZF.models_kpi_l hZF) hα h (values j) (inC j)
  obtain ⟨X,hXC,hx,sub,all⟩ := rd_finite_enclosed_l (ZF.modelsKP hZF) closed hUC hu (List.ofFn values) covers
  obtain ⟨zero,hzero⟩ := num_exists_l (ZF.modelsKP hZF) 0
  have hzX := sub zero (hu ω hωU zero (num_mem_l hZF.1 hω hzero))
  obtain ⟨a,fn,corr⟩ := assignment_realize_l hZF positions values (frame.bound_l hZF.1)
    (frame.injective_l (ZF.modelsKP hZF)) (fun j => all (values j) (List.mem_ofFn.mpr ⟨j,rfl⟩)) hzX
  have haC := jh_finite_function_mem_l hZF hα h hω hωC hXC (num_mem_l hZF.1 hω hk) (fn0_function_l (ZF.modelsKP hZF) fn)
  exact ⟨X,a,hXC,hx,haC,fn,fun j => ⟨positions j,frame.slots j,corr j⟩⟩

structure ParameterSkolemSource_d (hKP : M.Models KP) {d} (φ : Formula 1 (d+1)) (C ω e k : M.Domain) : Prop where
  count : Num_d d k
  count_mem : M.mem k C
  number_natural : M.mem e ω
  number_mem : M.mem e C
  program : ∃ T n L F r, BoundedFormula_d T ω n L F ∧ ProgramNumber_d (kp_pair_l hKP) ω n L F r e ∧ M.mem k n
  sound : ∀ (a input y : M.Domain) (σ : Env M d), SourceParameter_d σ.bound a → Rd_triple_d input e k a →
    parameterSkolem_s.schema.denote (⟨fun _ => ω,σ.free⟩ : Env M 1) input y → Formula.satisfies (σ.push y) φ
  local_total : ∀ (X a input : M.Domain) (σ : Env M d), M.mem input C → Fn0_d k X a →
    SourceParameter_d σ.bound a → Rd_triple_d input e k a → (∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) →
      ∃ z, M.mem z C ∧ Within_d parameterSkolem_s (⟨fun _ => ω,σ.free⟩ : Env M 1) input z C ∧ Formula.satisfies (σ.push z) φ ∧
        ∀ t, parameterSkolem_s.schema.denote (⟨fun _ => ω,σ.free⟩ : Env M 1) input t → t = z
  realizes : ∀ σ : Env M d, (∀ j, M.mem (σ.bound j) C) → ∃ X a input, M.mem X C ∧ M.TransitiveSet X ∧
    M.mem a C ∧ M.mem input C ∧ Fn0_d k X a ∧ SourceParameter_d σ.bound a ∧ Rd_triple_d input e k a
  parameter_unique : ∀ (X Y a b : M.Domain) (σ : Env M d), Fn0_d k X a → Fn0_d k Y b →
    SourceParameter_d σ.bound a → SourceParameter_d σ.bound b → a = b

/-- 同一实际原代码先于所有源环境存在；规范参数列和函数覆盖全部固定原 Δ₀ 模板。 -/
theorem jh_parameterSkolem_sourceCompile_l (hZF : M.Models ZF) {d} (reserve : Nat)
    (φ : Formula 1 (d+1)) (p : Cp_test (d+1)) (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ e k, ParameterSkolemSource_d (ZF.modelsKP hZF) φ C ω e k := by
  obtain ⟨n,slots,T,F,L,r,compiled⟩ := jh_canonicalDelta0_compile_l hZF reserve φ p hd hc parsed hα h hω hωC
  obtain ⟨e,he,code⟩ := programNumber_exists_l hZF hω compiled.valid compiled.root_bound
  obtain ⟨k,hk⟩ := num_exists_l (ZF.modelsKP hZF) d
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have heC := trans ω hωC e he
  have hkC := trans ω hωC k (num_mem_l hZF.1 hω hk)
  let v := numericSourceRegisters_l p reserve slots
  have vn : ∀ j, Num_d j.val (v j) := fun j => compiled.frame.slots ⟨j.val,by unfold deltaSourceWidth_l; omega⟩
  have vi : Function.Injective v := compiled.frame.prefix_injective_l (ZF.modelsKP hZF) (by unfold deltaSourceWidth_l; omega)
  have kn := num_lt_l hZF.1 hk compiled.frame.arity (by unfold deltaSourceWidth_l; omega)
  have correct : WitnessSourceCorrect_d φ v T ω n L F r := fun X g η hx fn corr => (compiled.correct X g η hx fn corr).1
  refine ⟨e,k,hk,hkC,he,heC,⟨T,n,L,F,r,compiled.valid,code,kn⟩,?_,?_,?_,?_⟩
  · intro a input y σ corr outer selected
    exact parameterSkolem_source_sound_l hZF ⟨fun _ => ω,σ.free⟩ σ hω compiled.valid code outer hk vn vi correct corr selected
  · intro X a input σ hinC ha corr outer source
    exact jh_parameterSkolem_source_function_l hZF hα h ⟨fun _ => ω,σ.free⟩ σ hω hωC hinC compiled.valid code outer hk kn vn vi correct ha corr source
  · intro σ values
    obtain ⟨X,a,hXC,hx,haC,fn,corr⟩ := jh_sourceParameter_realize_l hZF hα h hω hωC hk σ.bound values
    obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total k a
    obtain ⟨input,hinput⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
    have outer : Rd_triple_d input e k a := ⟨q,hq,hinput⟩
    have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e k a heC hkC haC input (rd_triple_value_l hZF.1 outer)
    exact ⟨X,a,input,hXC,hx,haC,hinC,fn,corr,outer⟩
  · intro X Y a b σ ha hb ca cb
    exact sourceParameter_unique_l (ZF.modelsKP hZF) hk ha hb ca cb

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
