import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedTruthCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedTruthSigma1

/-! # 只保留实际集合谓词 A 与内部 ω 的数码操作真值源 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 参数槽为 A、ω；输入原通用程序数码，输出真实普通赋值图。 -/
def pnumberedTruth_s (positive : Bool) : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <|
          pnumberedTruthCheck_m positive (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 7) (.bound 6) (.bound 5)
            (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.existsMem _ (pnumberedTruthCheck_delta_l ..)))))))) }

def pnumberedTruth_env_l (A ω : M.Domain) : Env M 2 := ⟨Fin.cases A (fun _ => ω),fun _ => ω⟩

theorem pnumberedTruth_matrix_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 2) (e f w : M.Domain) :
    Formula.satisfies (((ρ.push e).push f).push w) (pnumberedTruth_s positive).matrix.body ↔
      ∃ T, M.mem T w ∧ ∃ n, M.mem n w ∧ ∃ L, M.mem L w ∧ ∃ F, M.mem F w ∧
        ∃ r, M.mem r w ∧ ∃ X, M.mem X w ∧ ∃ P, M.mem P w ∧ ∃ Q, M.mem Q w ∧
          PNumberedTruthCheck_d positive (ρ.bound 1) (ρ.bound 0) e f T n L F r X P Q := by
  simp only [pnumberedTruth_s,Formula.satisfies_existsMem_iff,pnumberedTruthCheck_sat_l hKP]
  rfl

theorem pnumberedTruth_sigma1_l (positive : Bool) : (pnumberedTruth_s positive).schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

theorem pnumberedTruth_sat_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 2) (e f : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) :
    (pnumberedTruth_s positive).schema.denote ρ e f ↔
      PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive (ρ.bound 0) (ρ.bound 1) e f := by
  rw [S1_binary.sat_l]
  simp only [pnumberedTruth_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,T,_,n,_,L,_,F,_,r,_,X,_,P,_,Q,_,cert⟩
    exact pnumberedTruthCheck_sound_l hZF positive hω cert
  · intro truth
    obtain ⟨T,n,L,F,r,X,P,Q,cert⟩ := pnumberedTruthCheck_exists_l hZF positive hω truth
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [T,n,L,F,r,X,P,Q]
    exact ⟨w,T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
      X,hw X (by simp),P,hw P (by simp),Q,hw Q (by simp),cert⟩

/-- 任意合法原解码和真实传递求值域都给相同数码真值。 -/
theorem pnumberedTruth_fixed_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 2) {T n L F r X e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (hx : M.TransitiveSet X) (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    (pnumberedTruth_s positive).schema.denote ρ e f ↔ PFiniteTruth_d positive T (ρ.bound 0) (ρ.bound 1) n X F L r f := by
  rw [pnumberedTruth_sat_l hZF positive ρ e f hω]
  constructor
  · rintro ⟨U,m,K,G,s,Y,hy,validU,codeU,truthU⟩
    obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
    subst m
    subst K
    subst G
    subst s
    have hfY := pfiniteTruth_function_l hZF positive hω truthU
    have truthT := (pfiniteTruth_container_choice_l (ZF.modelsKP hZF) positive validU valid).mp truthU
    exact (pfiniteTruth_domain_choice_l hZF positive hω hy hx valid code.2.2.1 hfY fn).mp truthT
  · exact fun truth => ⟨T,n,L,F,r,X,hx,valid,code,truth⟩

theorem pnumberedTruth_complement_l (hZF : M.Models ZF) (ρ : Env M 2) {T n L F r X e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e)
    (hx : M.TransitiveSet X) (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    (pnumberedTruth_s false).schema.denote ρ e f ↔ ¬ (pnumberedTruth_s true).schema.denote ρ e f := by
  rw [pnumberedTruth_fixed_l hZF false ρ hω valid code hx fn,pnumberedTruth_fixed_l hZF true ρ hω valid code hx fn]
  exact pfiniteTruth_complement_l hZF hω valid fn

theorem pnumberedTruth_code_natural_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 2) {e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (truth : (pnumberedTruth_s positive).schema.denote ρ e f) : M.mem e (ρ.bound 1) := by
  obtain ⟨_,_,_,_,_,_,_,_,code,_⟩ := (pnumberedTruth_sat_l hZF positive ρ e f hω).mp truth
  exact code.natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω

/-- 原四类合法程序的同一数码也保持原数码真值，谓词参数不影响它。 -/
theorem pnumberedTruth_legacy_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X F L r e f : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e)
    (hx : M.TransitiveSet X) (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    (pnumberedTruth_s positive).schema.denote (pnumberedTruth_env_l A ω) e f ↔
      (numberedTruth_s positive).schema.denote (⟨fun _ => ω,fun _ => ω⟩ : Env M 1) e f :=
  (pnumberedTruth_fixed_l hZF positive (pnumberedTruth_env_l A ω) hω valid.predicate_l code hx fn).trans
    ((pfiniteTruth_legacy_l (ZF.modelsKP hZF) positive valid).trans
      (numberedTruth_fixed_l hZF positive (⟨fun _ => ω,fun _ => ω⟩ : Env M 1) hω valid code hx fn).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
