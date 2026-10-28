import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedTruthCertificate

/-! # 仅以内部 ω 为参数的数码操作真值 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 输入原自然数程序码 e，输出实际赋值图 f；ω 为唯一参数。 -/
def numberedTruth_s (positive : Bool) : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <|
          numberedTruthCheck_m positive (.bound 11) (.bound 10) (.bound 9) (.bound 7) (.bound 6) (.bound 5)
            (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.existsMem _ (numberedTruthCheck_delta_l ..)))))))) }

theorem numberedTruth_matrix_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 1) (e f w : M.Domain) :
    Formula.satisfies (((ρ.push e).push f).push w) (numberedTruth_s positive).matrix.body ↔
      ∃ T, M.mem T w ∧ ∃ n, M.mem n w ∧ ∃ L, M.mem L w ∧ ∃ F, M.mem F w ∧
        ∃ r, M.mem r w ∧ ∃ X, M.mem X w ∧ ∃ P, M.mem P w ∧ ∃ Q, M.mem Q w ∧
          NumberedTruthCheck_d positive (ρ.bound 0) e f T n L F r X P Q := by
  simp only [numberedTruth_s,Formula.satisfies_existsMem_iff,numberedTruthCheck_sat_l hKP]
  rfl

theorem numberedTruth_sat_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 1) (e f : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) :
    (numberedTruth_s positive).schema.denote ρ e f ↔ NumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive (ρ.bound 0) e f := by
  rw [S1_binary.sat_l]
  simp only [numberedTruth_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,T,_,n,_,L,_,F,_,r,_,X,_,P,_,Q,_,cert⟩
    exact numberedTruthCheck_sound_l hZF positive hω cert
  · intro truth
    obtain ⟨T,n,L,F,r,X,P,Q,cert⟩ := numberedTruthCheck_exists_l hZF positive hω truth
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [T,n,L,F,r,X,P,Q]
    exact ⟨w,T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
      X,hw X (by simp),P,hw P (by simp),Q,hw Q (by simp),cert⟩

theorem finiteTruth_function_l (hZF : M.Models ZF) (positive : Bool) {T ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (truth : FiniteTruth_d positive T ω n X F L r f) :
    M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X := by
  obtain ⟨a,s,Z,S,E,_,_,space,hf,_,_⟩ := truth
  exact ((assignmentSpaceCert_sound_l hZF hω space) f).mp hf

/-- 给定任意一份原解码和任意合法传递求值域，数码图与原操作真值准确等价。 -/
theorem numberedTruth_fixed_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 1) {T n L F r X e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (hx : M.TransitiveSet X) (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    (numberedTruth_s positive).schema.denote ρ e f ↔ FiniteTruth_d positive T (ρ.bound 0) n X F L r f := by
  rw [numberedTruth_sat_l hZF positive ρ e f hω]
  constructor
  · rintro ⟨U,m,K,G,s,Y,hy,validU,codeU,truthU⟩
    obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
    subst m; subst K; subst G; subst s
    have hfY := finiteTruth_function_l hZF positive hω truthU
    have truthT := (finiteTruth_container_choice_l (ZF.modelsKP hZF) positive validU valid).mp truthU
    exact (finiteTruth_domain_choice_l hZF positive hω hy hx hfY hf valid code.2.2.1).mp truthT
  · intro truth
    exact ⟨T,n,L,F,r,X,hx,valid,code,truth⟩

/-- 正负数码图只在原合法程序及实际合法赋值范围内互补。 -/
theorem numberedTruth_complement_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r X e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (hx : M.TransitiveSet X) (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    (numberedTruth_s false).schema.denote ρ e f ↔ ¬ (numberedTruth_s true).schema.denote ρ e f := by
  rw [numberedTruth_fixed_l hZF false ρ hω valid code hx hf,numberedTruth_fixed_l hZF true ρ hω valid code hx hf]
  exact finiteTruth_complement_l hZF hω valid hf

theorem numberedTruth_code_natural_l (hZF : M.Models ZF) (positive : Bool) (ρ : Env M 1) {e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (truth : (numberedTruth_s positive).schema.denote ρ e f) : M.mem e (ρ.bound 0) := by
  obtain ⟨_,_,_,_,_,_,_,_,code,_⟩ := (numberedTruth_sat_l hZF positive ρ e f hω).mp truth
  exact code.natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
