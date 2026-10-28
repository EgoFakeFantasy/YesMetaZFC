import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumericSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateBinder
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalPredicateCompiler

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

def PWitnessSourceCorrect_d {d} (a : Fin d) (φ : Formula 1 (d+1)) (v : Fin (d+1) → M.Domain) (T ω n L F r : M.Domain) : Prop :=
  ∀ (X g : M.Domain) (η : Env M (d+1)), M.TransitiveSet X → Fn0_d n X g →
    (∀ j, j ≠ a.succ → Rd_entry_d (v j) (η.bound j) g) →
      (PFiniteTruth_d true T (η.bound a.succ) ω n X F L r g ↔ Formula.satisfies η φ)

/-- 固定原解码后读取实际见证域和更新图，保留源程序及根不变。 -/
theorem pwitnessFiber_read_l (hZF : M.Models ZF) (ρ : Env M 2) {T n L F r e f i input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (packet : Rd_triple_d input e f i) (fiber : pwitnessFiber_s.schema.denote ρ input y) :
    ∃ X g, M.TransitiveSet X ∧ M.mem i n ∧ M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X ∧
      M.mem y X ∧ Senv_update_d (kp_pair_l (ZF.modelsKP hZF)) f i y g ∧ PFiniteTruth_d true T (ρ.bound 0) (ρ.bound 1) n X F L r g := by
  obtain ⟨U,m,K,G,s,X,a,b,j,g,other,hx,validU,codeU,hi,hf,hy,update,truth⟩ := (pwitnessFiber_sat_l hZF ρ input y hω).mp fiber
  obtain ⟨eqe,eqf,eqi⟩ := pc_triple_inj_l other packet
  subst a; subst b; subst j
  obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
  subst m; subst K; subst G; subst s
  exact ⟨X,g,hx,hi,hf,hy,update,(pfiniteTruth_container_choice_l (ZF.modelsKP hZF) true validU valid).mp truth⟩

theorem predicateSource_update_correspond_l (hKP : M.Models KP) {d} (a : Fin d) {v : Fin (d+1) → M.Domain}
    {σ : Env M d} {f g y : M.Domain} (injective : Function.Injective v)
    (corr : ∀ j : Fin d, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f)
    (update : Senv_update_d (kp_pair_l hKP) f (v 0) y g) :
    ∀ j, j ≠ a.succ → Rd_entry_d (v j) ((σ.push y).bound j) g := by
  have unused (j : Fin d) : v j.succ ≠ v 0 := by
    intro eq
    have h := congrArg Fin.val (injective eq)
    change j.val+1 = 0 at h
    omega
  have result := assignment_predicate_push_l hKP a corr unused update
  have eq : Fin.cases (v 0) (fun j => v j.succ) = v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  intro j hj
  have eqj := congrFun eq j
  exact eqj ▸ result j hj

theorem pwitnessFiber_source_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {d} (a : Fin d) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e f input y : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (injective : Function.Injective v)
    (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (corr : ∀ j : Fin d, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f)
    (fiber : pwitnessFiber_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ := by
  obtain ⟨X,g,hx,hi,hf,hy,update,truth⟩ := pwitnessFiber_read_l hZF ρ hω valid code packet fiber
  have hg := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hf hi hy
  exact (correct X g (σ.push y) hx (fn0_of_function_l (ZF.modelsKP hZF) hg)
    (predicateSource_update_correspond_l (ZF.modelsKP hZF) a injective corr update)).mp (by simpa only [predicateParam] using! truth)

theorem predicateNumericSkolem_source_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {d} (a : Fin d) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r e f input y : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (injective : Function.Injective v)
    (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (corr : ∀ j : Fin d, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f)
    (selected : predicateNumericSkolem_s.schema.denote ρ input y) : Formula.satisfies (σ.push y) φ :=
  pwitnessFiber_source_sound_l hZF ρ a σ predicateParam hω valid code packet injective correct corr
    ((pwitnessFiber_sat_l hZF ρ input y hω).mpr (predicateNumericSkolem_sound_l hZF ρ hω selected))

/-- 原层内的每个源见证均能生成真实更新与完整同层见证证书。 -/
theorem jh_pwitnessFiber_source_complete_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {d} (a : Fin d) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e f input y : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C) (hyC : M.mem y C)
    (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (bound : M.mem (v 0) n) (injective : Function.Injective v)
    (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ j : Fin d, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f) (source : Formula.satisfies (σ.push y) φ) :
    Within_d pwitnessFiber_s ρ input y C := by
  have details := packet
  obtain ⟨q,hq,hpacket⟩ := details
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hfC := (po_pair_bound_l trans (po_pair_bound_l trans hinC hpacket).2 hq).1
  obtain ⟨Y,hYC,hy,hfY,hyY⟩ := jh_assignmentDomain_withValue_l hZF hα h hfC hyC hf
  obtain ⟨g,update,hg⟩ := senv_update_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hfY bound hyY
  have truth := (correct Y g (σ.push y) hy (fn0_of_function_l (ZF.modelsKP hZF) hg)
    (predicateSource_update_correspond_l (ZF.modelsKP hZF) a injective corr update)).mpr source
  have truthA : PFiniteTruth_d true T (ρ.bound 0) (ρ.bound 1) n Y F L r g := by
    simpa only [predicateParam] using! truth
  have fiber := (pwitnessFiber_fixed_l hZF ρ hω valid code packet hy bound hfY hyY).mpr ⟨g,update,truthA⟩
  exact (jh_pwitnessFiber_within_l hZF hα h ρ input y amenable hω hωC hinC hyC).mpr ((pwitnessFiber_sat_l hZF ρ input y hω).mp fiber)

theorem jh_predicateNumericSkolem_source_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {d} (a : Fin d) {φ : Formula 1 (d+1)}
    {v : Fin (d+1) → M.Domain} {T n L F r X e f input : M.Domain} (σ : Env M d)
    (predicateParam : ρ.bound 0 = σ.bound a)
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (packet : Rd_triple_d input e f (v 0)) (bound : M.mem (v 0) n) (injective : Function.Injective v)
    (correct : PWitnessSourceCorrect_d a φ v T (ρ.bound 1) n L F r)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ j : Fin d, j ≠ a → Rd_entry_d (v j.succ) (σ.bound j) f)
    (existsSource : ∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) :
    ∃ z, M.mem z C ∧ Within_d predicateNumericSkolem_s ρ input z C ∧ Formula.satisfies (σ.push z) φ ∧
      ∀ t, predicateNumericSkolem_s.schema.denote ρ input t → t = z := by
  have he : ∃ y, M.mem y C ∧ PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) input y := by
    obtain ⟨y,hyC,source⟩ := existsSource
    obtain ⟨w,_,hw⟩ := jh_pwitnessFiber_source_complete_l hZF hα h ρ a σ predicateParam amenable hω hωC hinC hyC valid code packet bound injective correct hf corr source
    exact ⟨y,hyC,(pwitnessFiber_sat_l hZF ρ input y hω).mp ((pwitnessFiber_s.sat_l ρ input y).mpr ⟨w,hw⟩)⟩
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_predicateNumericSkolem_function_l hZF hα h ρ amenable hω hωC hinC he
  exact ⟨z,hzC,hz,predicateNumericSkolem_source_sound_l hZF ρ a σ predicateParam hω valid code packet injective correct corr
    (predicateNumericSkolem_fromWithin_l ρ hz),unique⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
