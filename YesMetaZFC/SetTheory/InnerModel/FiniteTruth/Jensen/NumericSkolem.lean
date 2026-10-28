import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.WitnessFiber
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

def numericSkolem_s : S1_binary 1 := canonicalPick_s witnessFiber_s

theorem numericSkolem_sound_l (hZF : M.Models ZF) (ρ : Env M 1) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (selected : numericSkolem_s.schema.denote ρ input y) :
    WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y :=
  (witnessFiber_sat_l hZF ρ input y hω).mp (canonicalPick_sound_l (ZF.models_kpi_l hZF) witnessFiber_s ρ
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) witnessFiber_s ρ input y).mp selected))

theorem numericSkolem_unique_l (hZF : M.Models ZF) (ρ : Env M 1) {input y z : M.Domain}
    (hy : numericSkolem_s.schema.denote ρ input y) (hz : numericSkolem_s.schema.denote ρ input z) : y = z :=
  canonicalPick_unique_l (ZF.models_kpi_l hZF) witnessFiber_s ρ
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) witnessFiber_s ρ input y).mp hy)
    ((canonicalPick_sat_l (ZF.models_kpi_l hZF) witnessFiber_s ρ input z).mp hz)

theorem numericSkolem_fromWithin_l (ρ : Env M 1) {input y C : M.Domain}
    (selected : Within_d numericSkolem_s ρ input y C) : numericSkolem_s.schema.denote ρ input y := by
  obtain ⟨w,_,hw⟩ := selected
  exact (numericSkolem_s.sat_l ρ input y).mpr ⟨w,hw⟩

/-- 任一层内原见证足以构造完整层内最小证书对；输出对全局规范图也唯一。 -/
theorem jh_numericSkolem_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {input : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (existsWitness : ∃ y, M.mem y C ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y) :
    ∃ z, M.mem z C ∧ Within_d numericSkolem_s ρ input z C ∧
      WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input z ∧
      ∀ v, numericSkolem_s.schema.denote ρ input v → v = z := by
  have he : ∃ y, M.mem y C ∧ Within_d witnessFiber_s ρ input y C := by
    obtain ⟨y,hyC,hy⟩ := existsWitness
    exact ⟨y,hyC,(jh_witnessFiber_within_l hZF hα h ρ input y hω hωC hinC hyC).mpr hy⟩
  obtain ⟨z,hzC,hz,_,_⟩ := jh_canonicalPick_bounded_function_l (ZF.models_kpi_l hZF) hα h witnessFiber_s ρ (Fin.cases hωC (fun i => Fin.elim0 i)) hinC he
  have selected : numericSkolem_s.schema.denote ρ input z := numericSkolem_fromWithin_l ρ hz
  exact ⟨z,hzC,hz,numericSkolem_sound_l hZF ρ hω selected,fun v hv => numericSkolem_unique_l hZF ρ hv selected⟩

/-- 已有低层原见证时，全局选取连同其完整证书均被该层捕获。 -/
theorem jh_numericSkolem_capture_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (existsWitness : ∃ z, M.mem z C ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input z)
    (selected : numericSkolem_s.schema.denote ρ input y) :
    M.mem y C ∧ Within_d numericSkolem_s ρ input y C ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y := by
  obtain ⟨z,hzC,hz,fiber,unique⟩ := jh_numericSkolem_function_l hZF hα h ρ hω hωC hinC existsWitness
  have eq := unique y selected
  subst y
  exact ⟨hzC,hz,fiber⟩

theorem jh_numericSkolem_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) (input y : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (existsWitness : ∃ z, M.mem z C ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input z) :
    Within_d numericSkolem_s ρ input y C ↔ numericSkolem_s.schema.denote ρ input y :=
  ⟨numericSkolem_fromWithin_l ρ,fun selected =>
    (jh_numericSkolem_capture_l hZF hα h ρ hω hωC hinC existsWitness selected).2.1⟩

/-- 同一个实际规范图在嵌套原 J 层中保值；不预设层间初等性。 -/
theorem jh_numericSkolem_up_l (hZF : M.Models ZF) {α β C D : M.Domain}
    (hα : M.IsOrdinal α) (hβ : M.IsOrdinal β) (hC : Jh_value_d α C) (hD : Jh_value_d β D)
    (sub : M.MemberSubset C D) (hnC : Nonempty {x : M.Domain // M.mem x C}) (hnD : Nonempty {x : M.Domain // M.mem x D})
    (ρ : Env (rt_model_l C hnC) 1) (input y : (rt_model_l C hnC).Domain)
    (selected : numericSkolem_s.schema.denote ρ input y) :
    numericSkolem_s.schema.denote (image_env_l (rt_include_l sub hnC hnD) ρ)
      (rt_include_l sub hnC hnD input) (rt_include_l sub hnC hnD y) :=
  jh_canonicalPick_up_l (ZF.models_kpi_l hZF) hα hβ hC hD sub hnC hnD witnessFiber_s ρ input y selected

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
