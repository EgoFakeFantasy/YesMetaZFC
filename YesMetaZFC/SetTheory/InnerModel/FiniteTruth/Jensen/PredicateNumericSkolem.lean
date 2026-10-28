import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateWitnessFiber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UnrestrictedCanonicalWithin
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LocalObjectTheorem

/-! # 原数码与参数赋值上的实际规范见证函数

固定同一个统一 Σ₁ 见证关系，以 Jensen 规范序选择完整输出/证书对再投影。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def predicateNumericSkolem_s : S1_binary 2 := canonicalPick_s pwitnessFiber_s

theorem predicateNumericSkolem_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (selected : predicateNumericSkolem_s.schema.denote ρ input y) :
    PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y :=
  (pwitnessFiber_sat_l hZF ρ input y hω).mp (canonicalPick_sound_l (ZF.models_kpi_l hZF) pwitnessFiber_s ρ
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) pwitnessFiber_s ρ input y).mp selected))

theorem predicateNumericSkolem_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input y z : M.Domain}
    (hy : predicateNumericSkolem_s.schema.denote ρ input y) (hz : predicateNumericSkolem_s.schema.denote ρ input z) : y = z :=
  canonicalPick_unique_l (ZF.models_kpi_l hZF) pwitnessFiber_s ρ
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) pwitnessFiber_s ρ input y).mp hy)
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) pwitnessFiber_s ρ input z).mp hz)

theorem predicateNumericSkolem_fromWithin_l (ρ : Env M 2) {input y C : M.Domain}
    (selected : Within_d predicateNumericSkolem_s ρ input y C) : predicateNumericSkolem_s.schema.denote ρ input y := by
  obtain ⟨w,_,hw⟩ := selected
  exact (predicateNumericSkolem_s.sat_l ρ input y).mpr ⟨w,hw⟩

/-- 任一层内原见证足以构造完整层内最小证书对；输出对全局规范图也唯一。 -/
theorem jh_predicateNumericSkolem_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ y, M.mem y C ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y) :
    ∃ z, M.mem z C ∧ Within_d predicateNumericSkolem_s ρ input z C ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input z ∧
      ∀ v, predicateNumericSkolem_s.schema.denote ρ input v → v = z := by
  have he : ∃ y, M.mem y C ∧ Within_d pwitnessFiber_s ρ input y C := by
    obtain ⟨y,hyC,hy⟩ := existsWitness
    exact ⟨y,hyC,(jh_pwitnessFiber_within_l hZF hα h ρ input y amenable hω hωC hinC hyC).mpr hy⟩
  obtain ⟨z,hzC,hz,_,_⟩ := jh_canonicalPick_within_function_l (ZF.models_kpi_l hZF) hα h pwitnessFiber_s ρ input he
  have selected : predicateNumericSkolem_s.schema.denote ρ input z := predicateNumericSkolem_fromWithin_l ρ hz
  exact ⟨z,hzC,hz,predicateNumericSkolem_sound_l hZF ρ hω selected,fun v hv => predicateNumericSkolem_unique_l hZF ρ hv selected⟩

/-- 已有低层原见证时，全局选取连同其完整证书均被该层捕获。 -/
theorem jh_predicateNumericSkolem_capture_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ z, M.mem z C ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input z)
    (selected : predicateNumericSkolem_s.schema.denote ρ input y) :
    M.mem y C ∧ Within_d predicateNumericSkolem_s ρ input y C ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y := by
  obtain ⟨z,hzC,hz,fiber,unique⟩ := jh_predicateNumericSkolem_function_l hZF hα h ρ amenable hω hωC hinC existsWitness
  have eq := unique y selected
  subst y
  exact ⟨hzC,hz,fiber⟩

theorem jh_predicateNumericSkolem_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (input y : M.Domain)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ z, M.mem z C ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input z) :
    Within_d predicateNumericSkolem_s ρ input y C ↔ predicateNumericSkolem_s.schema.denote ρ input y :=
  ⟨predicateNumericSkolem_fromWithin_l ρ,fun selected =>
    (jh_predicateNumericSkolem_capture_l hZF hα h ρ amenable hω hωC hinC existsWitness selected).2.1⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
