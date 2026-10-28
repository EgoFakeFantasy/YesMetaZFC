import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NormalizedInput
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NumericSkolem

/-! # 规范参数列输入上的统一 Skolem 函数 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def parameterSkolem_s : S1_binary 1 := normalizedInput_s.comp numericSkolem_s

theorem parameterSkolem_sat_l (hZF : M.Models ZF) (ρ : Env M 1) (input y : M.Domain) :
    parameterSkolem_s.schema.denote ρ input y ↔ ∃ packet, normalizedInput_s.schema.denote ρ input packet ∧
      numericSkolem_s.schema.denote ρ packet y :=
  S1_binary.comp_sat_l (ZF.modelsKP hZF) normalizedInput_s numericSkolem_s ρ input y

theorem parameterSkolem_sound_l (hZF : M.Models ZF) (ρ : Env M 1) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (selected : parameterSkolem_s.schema.denote ρ input y) :
    ∃ packet, NormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input packet ∧
      WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) packet y := by
  obtain ⟨packet,normal,choice⟩ := (parameterSkolem_sat_l hZF ρ input y).mp selected
  exact ⟨packet,(normalizedInput_sat_l hZF ρ input packet hω).mp normal,numericSkolem_sound_l hZF ρ hω choice⟩

theorem parameterSkolem_unique_l (hZF : M.Models ZF) (ρ : Env M 1) {input y z : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hy : parameterSkolem_s.schema.denote ρ input y)
    (hz : parameterSkolem_s.schema.denote ρ input z) : y = z := by
  obtain ⟨p,hp,sy⟩ := (parameterSkolem_sat_l hZF ρ input y).mp hy
  obtain ⟨q,hq,sz⟩ := (parameterSkolem_sat_l hZF ρ input z).mp hz
  have eq := normalizedInput_unique_l hZF ρ hω hp hq
  subst q
  exact numericSkolem_unique_l hZF ρ sy sz

/-- 任意合法共同求值域内的规范赋值均给出同一实际规范函数值。 -/
theorem parameterSkolem_fixed_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r X e k a z f input packet y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (outer : Rd_triple_d input e k a) (inner : Rd_triple_d packet e f z) (parameters : ParameterCheck_d (ρ.bound 0) k n X a z f) :
    parameterSkolem_s.schema.denote ρ input y ↔ numericSkolem_s.schema.denote ρ packet y := by
  have normal := (normalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩
  rw [parameterSkolem_sat_l hZF]
  constructor
  · rintro ⟨other,hother,selected⟩
    have eq := normalizedInput_unique_l hZF ρ hω hother normal
    subst other
    exact selected
  · intro selected
    exact ⟨packet,normal,selected⟩

/-- 完整复合见证的同层预算，不预设该层满足 KP。 -/
theorem within_comp_cover_l (hKP : M.Models KP) {C A : M.Domain} (trans : M.TransitiveSet C) (closed : Rd_closed_d C)
    (hAC : M.mem A C) {n} (φ ψ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    Within_d (φ.comp ψ) ρ x y C ↔ ∃ z, M.mem z C ∧ Within_d φ ρ x z C ∧ Within_d ψ ρ z y C := by
  unfold Within_d
  simp only [S1_binary.comp_matrix_l]
  constructor
  · rintro ⟨T,hTC,z,hz,w,hw,v,hv,hφ,hψ⟩
    exact ⟨z,trans T hTC z hz,⟨w,trans T hTC w hw,hφ⟩,v,trans T hTC v hv,hψ⟩
  · rintro ⟨z,hzC,⟨w,hwC,hφ⟩,v,hvC,hψ⟩
    have all : ∀ a, a ∈ [z,w,v] → M.mem a C := by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
    obtain ⟨T,hTC,hT⟩ := rd_finiteTruth_cover_l hKP closed hAC [z,w,v] all
    exact ⟨T,hTC,z,hT z (by simp),w,hT w (by simp),v,hT v (by simp),hφ,hψ⟩

theorem within_toSchema_l {n} (φ : S1_binary n) (ρ : Env M n) {x y C : M.Domain}
    (within : Within_d φ ρ x y C) : φ.schema.denote ρ x y := by
  obtain ⟨w,_,hw⟩ := within
  exact (φ.sat_l ρ x y).mpr ⟨w,hw⟩

/-- 层内存在原源见证时，完整规范化和规范选取都在同一原层完成。 -/
theorem jh_parameterSkolem_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {input : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet y, M.mem y C ∧ normalizedInput_s.schema.denote ρ input packet ∧
      WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) packet y) :
    ∃ z, M.mem z C ∧ Within_d parameterSkolem_s ρ input z C ∧
      (∃ packet, normalizedInput_s.schema.denote ρ input packet ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) packet z) ∧
      ∀ t, parameterSkolem_s.schema.denote ρ input t → t = z := by
  obtain ⟨packet,y,hyC,normal,fiber⟩ := existsWitness
  have hpC := jh_normalizedInput_output_l hZF hα h ρ hω hωC hinC normal
  have pWithin := (jh_normalizedInput_within_l hZF hα h ρ input packet hω hωC hinC).mpr
    ((normalizedInput_sat_l hZF ρ input packet hω).mp normal)
  obtain ⟨z,hzC,zWithin,fiberZ,_⟩ := jh_numericSkolem_function_l hZF hα h ρ hω hωC hpC ⟨y,hyC,fiber⟩
  have selected : Within_d parameterSkolem_s ρ input z C :=
    (within_comp_cover_l (ZF.modelsKP hZF) (jh_value_transitive_l (ZF.models_kpi_l hZF) h)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC normalizedInput_s numericSkolem_s ρ input z).mpr
        ⟨packet,hpC,pWithin,zWithin⟩
  exact ⟨z,hzC,selected,⟨packet,normal,fiberZ⟩,fun t ht => parameterSkolem_unique_l hZF ρ hω ht (within_toSchema_l parameterSkolem_s ρ selected)⟩

theorem jh_parameterSkolem_capture_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet z, M.mem z C ∧ normalizedInput_s.schema.denote ρ input packet ∧
      WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) packet z)
    (selected : parameterSkolem_s.schema.denote ρ input y) : M.mem y C ∧ Within_d parameterSkolem_s ρ input y C := by
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_parameterSkolem_function_l hZF hα h ρ hω hωC hinC existsWitness
  have eq := unique y selected
  subst y
  exact ⟨hzC,hz⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
