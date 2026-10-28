import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NumericSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalDelta0Compiler

/-! # 实际规范函数与原源公式的语义桥接

本模块给任意模型的源语义对应和自动同层源覆盖；原逐模板源句子的组合封装另行验收。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def WitnessSourceCorrect_d {d} (φ : Formula 1 (d+1)) (v : Fin (d+1) → M.Domain) (T ω n L F r : M.Domain) : Prop :=
  ∀ (X g : M.Domain) (η : Env M (d+1)), M.TransitiveSet X → Fn0_d n X g →
    (∀ j, Rd_entry_d (v j) (η.bound j) g) →
      (FiniteTruth_d true T ω n X F L r g ↔ Formula.satisfies η φ)

/-- 固定原解码后读取实际见证域和更新图，保留源程序及根不变。 -/
theorem witnessFiber_read_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r e f i input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f i) (fiber : witnessFiber_s.schema.denote ρ input y) :
    ∃ X g, M.TransitiveSet X ∧ M.mem i n ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X ∧
      M.mem y X ∧ Senv_update_d (kp_pair_l (ZF.modelsKP hZF)) f i y g ∧ FiniteTruth_d true T (ρ.bound 0) n X F L r g := by
  obtain ⟨U,m,K,G,s,X,a,b,j,g,other,hx,validU,codeU,hi,hf,hy,update,truth⟩ := (witnessFiber_sat_l hZF ρ input y hω).mp fiber
  obtain ⟨eqe,eqf,eqi⟩ := pc_triple_inj_l other packet
  subst a; subst b; subst j
  obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
  subst m; subst K; subst G; subst s
  exact ⟨X,g,hx,hi,hf,hy,update,(finiteTruth_container_choice_l (ZF.modelsKP hZF) true validU valid).mp truth⟩

theorem source_update_correspond_l (hKP : M.Models KP) {d} {v : Fin (d+1) → M.Domain}
    {σ : Env M d} {f g y : M.Domain} (injective : Function.Injective v)
    (corr : ∀ j : Fin d, Rd_entry_d (v j.succ) (σ.bound j) f)
    (update : Senv_update_d (kp_pair_l hKP) f (v 0) y g) :
    ∀ j, Rd_entry_d (v j) ((σ.push y).bound j) g := by
  have unused (j : Fin d) : v j.succ ≠ v 0 := by
    intro eq
    have h := congrArg Fin.val (injective eq)
    change j.val+1 = 0 at h
    omega
  have result := assignment_push_correspond_l hKP corr unused update
  have eq : Fin.cases (v 0) (fun j => v j.succ) = v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  intro j
  have eqj := congrFun eq j
  exact eqj ▸ result j

theorem witnessFiber_source_sound_l (hZF : M.Models ZF) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e f input y : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (injective : Function.Injective v)
    (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (corr : ∀ j : Fin d, Rd_entry_d (v j.succ) (σ.bound j) f)
    (fiber : witnessFiber_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ := by
  obtain ⟨X,g,hx,hi,hf,hy,update,truth⟩ := witnessFiber_read_l hZF ρ hω valid code packet fiber
  have hg := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hf hi hy
  exact (correct X g (σ.push y) hx (fn0_of_function_l (ZF.modelsKP hZF) hg)
    (source_update_correspond_l (ZF.modelsKP hZF) injective corr update)).mp truth

theorem numericSkolem_source_sound_l (hZF : M.Models ZF) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e f input y : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (injective : Function.Injective v)
    (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (corr : ∀ j : Fin d, Rd_entry_d (v j.succ) (σ.bound j) f)
    (selected : numericSkolem_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ :=
  witnessFiber_source_sound_l hZF ρ σ hω valid code packet injective correct corr
    ((witnessFiber_sat_l hZF ρ input y hω).mpr (numericSkolem_sound_l hZF ρ hω selected))

/-- 原层内的每个源见证均能生成真实更新与完整同层见证证书。 -/
theorem jh_witnessFiber_source_complete_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e f input y : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C) (hyC : M.mem y C)
    (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (bound : M.mem (v 0) n) (injective : Function.Injective v)
    (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ j : Fin d, Rd_entry_d (v j.succ) (σ.bound j) f) (source : Formula.satisfies (σ.push y) φ) :
    Within_d witnessFiber_s ρ input y C := by
  have details := packet
  obtain ⟨q,hq,hpacket⟩ := details
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hfC := (po_pair_bound_l trans (po_pair_bound_l trans hinC hpacket).2 hq).1
  obtain ⟨Y,hYC,hy,hfY,hyY⟩ := jh_assignmentDomain_withValue_l hZF hα h hfC hyC hf
  obtain ⟨g,update,hg⟩ := senv_update_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hfY bound hyY
  have truth := (correct Y g (σ.push y) hy (fn0_of_function_l (ZF.modelsKP hZF) hg)
    (source_update_correspond_l (ZF.modelsKP hZF) injective corr update)).mpr source
  have fiber := (witnessFiber_fixed_l hZF ρ hω valid code packet hy bound hfY hyY).mpr ⟨g,update,truth⟩
  exact (jh_witnessFiber_within_l hZF hα h ρ input y hω hωC hinC hyC).mpr ((witnessFiber_sat_l hZF ρ input y hω).mp fiber)

theorem jh_numericSkolem_source_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 1) {d} {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e f input : M.Domain} (σ : Env M d)
    (hω : M.IsOmega (ρ.bound 0)) (hωC : M.mem (ρ.bound 0) C) (hinC : M.mem input C)
    (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (bound : M.mem (v 0) n) (injective : Function.Injective v)
    (correct : WitnessSourceCorrect_d φ v T (ρ.bound 0) n L F r)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ j : Fin d, Rd_entry_d (v j.succ) (σ.bound j) f)
    (existsSource : ∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) :
    ∃ z, M.mem z C ∧ Within_d numericSkolem_s ρ input z C ∧ Formula.satisfies (σ.push z) φ ∧
      ∀ t, numericSkolem_s.schema.denote ρ input t → t = z := by
  have he : ∃ y, M.mem y C ∧ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y := by
    obtain ⟨y,hyC,source⟩ := existsSource
    obtain ⟨w,_,hw⟩ := jh_witnessFiber_source_complete_l hZF hα h ρ σ hω hωC hinC hyC valid code packet bound injective correct hf corr source
    exact ⟨y,hyC,(witnessFiber_sat_l hZF ρ input y hω).mp ((witnessFiber_s.sat_l ρ input y).mpr ⟨w,hw⟩)⟩
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_numericSkolem_function_l hZF hα h ρ hω hωC hinC he
  exact ⟨z,hzC,hz,numericSkolem_source_sound_l hZF ρ σ hω valid code packet injective correct corr
    (numericSkolem_fromWithin_l ρ hz),unique⟩

/-- 原完整编译器的规范前缀寄存器，槽零承担新源 binder 的见证。 -/
def numericSourceRegisters_l {d} (p : Cp_test (d+1)) (reserve : Nat)
    (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) : Fin (d+1) → M.Domain :=
  framePrefix_l (by unfold deltaSourceWidth_l; omega) slots

/-- 同一源程序和同一数码的实际源覆盖；语义模式由固定原模板索引。 -/
structure NumericSkolemSource_d (hKP : M.Models KP) {d} (reserve : Nat) (p : Cp_test (d+1)) (φ : Formula 1 (d+1))
    (C ω n : M.Domain) (slots : Fin (deltaSourceWidth_l p reserve) → M.Domain) (T F L r e : M.Domain) : Prop where
  compiled : CanonicalDelta0_d hKP reserve p φ C ω n slots T F L r
  number_natural : M.mem e ω
  number_mem : M.mem e C
  code : ProgramNumber_d (kp_pair_l hKP) ω n L F r e
  sound : ∀ (f input y : M.Domain) (σ : Env M d), Rd_triple_d input e f (numericSourceRegisters_l p reserve slots 0) →
    (∀ j, Rd_entry_d (numericSourceRegisters_l p reserve slots j.succ) (σ.bound j) f) →
    numericSkolem_s.schema.denote (⟨fun _ => ω,σ.free⟩ : Env M 1) input y → Formula.satisfies (σ.push y) φ
  realizes : ∀ X default, M.mem X C → M.TransitiveSet X → M.mem default X →
    ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l hKP) E n X ∧
      ∀ σ : Env M d, (∀ j, M.mem (σ.bound j) X) → ∃ f input, M.mem f E ∧ M.mem f C ∧ M.mem input C ∧ Fn0_d n X f ∧
        Rd_triple_d input e f (numericSourceRegisters_l p reserve slots 0) ∧
        ∀ j, Rd_entry_d (numericSourceRegisters_l p reserve slots j.succ) (σ.bound j) f
  local_total : ∀ (X f input : M.Domain) (σ : Env M d), M.mem input C →
    M.IsSetFunctionFromTo (kp_pair_l hKP) f n X → Rd_triple_d input e f (numericSourceRegisters_l p reserve slots 0) →
    (∀ j, Rd_entry_d (numericSourceRegisters_l p reserve slots j.succ) (σ.bound j) f) →
    (∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) →
      ∃ z, M.mem z C ∧ Within_d numericSkolem_s (⟨fun _ => ω,σ.free⟩ : Env M 1) input z C ∧ Formula.satisfies (σ.push z) φ ∧
        ∀ t, numericSkolem_s.schema.denote (⟨fun _ => ω,σ.free⟩ : Env M 1) input t → t = z

/-- 自动生成同层原数码、实际参数输入及规范函数的全部原源语义。 -/
theorem jh_numericSkolem_sourceCompile_l (hZF : M.Models ZF) {d} (reserve : Nat)
    (φ : Formula 1 (d+1)) (p : Cp_test (d+1)) (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ slots : Fin (deltaSourceWidth_l p reserve) → M.Domain, ∃ T F L r e,
      NumericSkolemSource_d (ZF.modelsKP hZF) reserve p φ C ω n slots T F L r e := by
  obtain ⟨n,slots,T,F,L,r,compiled⟩ := jh_canonicalDelta0_compile_l hZF reserve φ p hd hc parsed hα h hω hωC
  obtain ⟨e,he,code⟩ := programNumber_exists_l hZF hω compiled.valid compiled.root_bound
  have heC := jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC e he
  let v := numericSourceRegisters_l p reserve slots
  have vb : ∀ j, M.mem (v j) n := compiled.frame.prefix_bound_l hZF.1 (by unfold deltaSourceWidth_l; omega)
  have vi : Function.Injective v := compiled.frame.prefix_injective_l (ZF.modelsKP hZF) (by unfold deltaSourceWidth_l; omega)
  have correct : WitnessSourceCorrect_d φ v T ω n L F r := fun X g η hx fn corr => (compiled.correct X g η hx fn corr).1
  refine ⟨n,slots,T,F,L,r,e,compiled,he,heC,code,?_,?_,?_⟩
  · intro f input y σ packet corr selected
    exact numericSkolem_source_sound_l hZF (⟨fun _ => ω,σ.free⟩ : Env M 1) σ hω compiled.valid code packet vi correct corr selected
  · intro X default hXC hx inhabited
    obtain ⟨E,hEC,full,all⟩ := compiled.realizes X default hXC hx inhabited
    refine ⟨E,hEC,full,fun σ values => ?_⟩
    have allValues : ∀ j, M.mem ((σ.push default).bound j) X := Fin.cases inhabited values
    obtain ⟨f,hfE,hfC,fn,corr,_⟩ := all (σ.push default) allValues
    obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f (v 0)
    obtain ⟨input,hinput⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
    have packet : Rd_triple_d input e f (v 0) := ⟨q,hq,hinput⟩
    have hvC : M.mem (v 0) C := compiled.slots_mem ⟨0,by unfold deltaSourceWidth_l; omega⟩
    have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e f (v 0) heC hfC hvC input (rd_triple_value_l hZF.1 packet)
    exact ⟨f,input,hfE,hfC,hinC,fn,packet,fun j => corr j.succ⟩
  · intro X f input σ hinC hf packet corr he
    exact jh_numericSkolem_source_function_l hZF hα h (⟨fun _ => ω,σ.free⟩ : Env M 1) σ hω hωC hinC
      compiled.valid code packet (vb 0) vi correct hf corr he


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
