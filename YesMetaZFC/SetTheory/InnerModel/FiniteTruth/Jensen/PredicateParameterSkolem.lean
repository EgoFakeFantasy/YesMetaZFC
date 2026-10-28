import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNormalizedInput
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumericSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolem

/-! # 规范参数列输入上的统一 Skolem 函数 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def predicateParameterSkolem_s : S1_binary 2 := pnormalizedInput_s.comp predicateNumericSkolem_s

theorem predicateParameterSkolem_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (input y : M.Domain) :
    predicateParameterSkolem_s.schema.denote ρ input y ↔ ∃ packet, pnormalizedInput_s.schema.denote ρ input packet ∧
      predicateNumericSkolem_s.schema.denote ρ packet y :=
  S1_binary.comp_sat_l (ZF.modelsKP hZF) pnormalizedInput_s predicateNumericSkolem_s ρ input y

theorem predicateParameterSkolem_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (selected : predicateParameterSkolem_s.schema.denote ρ input y) :
    ∃ packet, PNormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) input packet ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) packet y := by
  obtain ⟨packet,normal,choice⟩ := (predicateParameterSkolem_sat_l hZF ρ input y).mp selected
  exact ⟨packet,(pnormalizedInput_sat_l hZF ρ input packet hω).mp normal,predicateNumericSkolem_sound_l hZF ρ hω choice⟩

theorem predicateParameterSkolem_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input y z : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hy : predicateParameterSkolem_s.schema.denote ρ input y)
    (hz : predicateParameterSkolem_s.schema.denote ρ input z) : y = z := by
  obtain ⟨p,hp,sy⟩ := (predicateParameterSkolem_sat_l hZF ρ input y).mp hy
  obtain ⟨q,hq,sz⟩ := (predicateParameterSkolem_sat_l hZF ρ input z).mp hz
  have eq := pnormalizedInput_unique_l hZF ρ hω hp hq
  subst q
  exact predicateNumericSkolem_unique_l hZF ρ sy sz

/-- 任意合法共同求值域内的规范赋值均给出同一实际规范函数值。 -/
theorem predicateParameterSkolem_fixed_l (hZF : M.Models ZF) (ρ : Env M 2) {T n L F r X e k a z f input packet y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (outer : Rd_triple_d input e k a) (inner : Rd_triple_d packet e f z) (parameters : ParameterCheck_d (ρ.bound 1) k n X a z f) :
    predicateParameterSkolem_s.schema.denote ρ input y ↔ predicateNumericSkolem_s.schema.denote ρ packet y := by
  have normal := (pnormalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩
  rw [predicateParameterSkolem_sat_l hZF]
  constructor
  · rintro ⟨other,hother,selected⟩
    have eq := pnormalizedInput_unique_l hZF ρ hω hother normal
    subst other
    exact selected
  · intro selected
    exact ⟨packet,normal,selected⟩

/-- 层内存在原源见证时，完整规范化和规范选取都在同一原层完成。 -/
theorem jh_predicateParameterSkolem_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet y, M.mem y C ∧ pnormalizedInput_s.schema.denote ρ input packet ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) packet y) :
    ∃ z, M.mem z C ∧ Within_d predicateParameterSkolem_s ρ input z C ∧
      (∃ packet, pnormalizedInput_s.schema.denote ρ input packet ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) packet z) ∧
      ∀ t, predicateParameterSkolem_s.schema.denote ρ input t → t = z := by
  obtain ⟨packet,y,hyC,normal,fiber⟩ := existsWitness
  have hpC := jh_pnormalizedInput_output_l hZF hα h ρ hω hωC hinC normal
  have pWithin := (jh_pnormalizedInput_within_l hZF hα h ρ input packet hω hωC hinC).mpr
    ((pnormalizedInput_sat_l hZF ρ input packet hω).mp normal)
  obtain ⟨z,hzC,zWithin,fiberZ,_⟩ := jh_predicateNumericSkolem_function_l hZF hα h ρ amenable hω hωC hpC ⟨y,hyC,fiber⟩
  have selected : Within_d predicateParameterSkolem_s ρ input z C :=
    (within_comp_cover_l (ZF.modelsKP hZF) (jh_value_transitive_l (ZF.models_kpi_l hZF) h)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC pnormalizedInput_s predicateNumericSkolem_s ρ input z).mpr
        ⟨packet,hpC,pWithin,zWithin⟩
  exact ⟨z,hzC,selected,⟨packet,normal,fiberZ⟩,fun t ht => predicateParameterSkolem_unique_l hZF ρ hω ht (within_toSchema_l predicateParameterSkolem_s ρ selected)⟩

theorem jh_predicateParameterSkolem_capture_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet z, M.mem z C ∧ pnormalizedInput_s.schema.denote ρ input packet ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) packet z)
    (selected : predicateParameterSkolem_s.schema.denote ρ input y) : M.mem y C ∧ Within_d predicateParameterSkolem_s ρ input y C := by
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_predicateParameterSkolem_function_l hZF hα h ρ amenable hω hωC hinC existsWitness
  have eq := unique y selected
  subst y
  exact ⟨hzC,hz⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
