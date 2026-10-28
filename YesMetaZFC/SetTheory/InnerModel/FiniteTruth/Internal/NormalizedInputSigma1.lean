import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NormalizedInputCertificate

/-! # 只有内部 ω 参数的唯一规范输入 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def normalizedInput_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <| Formula.existsMem (.bound 9) <| Formula.existsMem (.bound 10) <| Formula.existsMem (.bound 11) <|
      normalizedInputCheck_m (.bound 15) (.bound 14) (.bound 13) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
        (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (normalizedInputCheck_delta_l ..)))))))))))) }

theorem normalizedInput_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 1) (input packet w : M.Domain) :
    Formula.satisfies (((ρ.push input).push packet).push w) normalizedInput_s.matrix.body ↔
      ∃ T, M.mem T w ∧ ∃ n, M.mem n w ∧ ∃ L, M.mem L w ∧ ∃ F, M.mem F w ∧ ∃ r, M.mem r w ∧
        ∃ X, M.mem X w ∧ ∃ e, M.mem e w ∧ ∃ k, M.mem k w ∧ ∃ a, M.mem a w ∧ ∃ z, M.mem z w ∧
          ∃ f, M.mem f w ∧ ∃ P, M.mem P w ∧ NormalizedInputCheck_d (ρ.bound 0) input packet T n L F r X e k a z f P := by
  simp only [normalizedInput_s,Formula.satisfies_existsMem_iff,normalizedInputCheck_sat_l hKP]
  rfl

theorem normalizedInput_sat_l (hZF : M.Models ZF) (ρ : Env M 1) (input packet : M.Domain) (hω : M.IsOmega (ρ.bound 0)) :
    normalizedInput_s.schema.denote ρ input packet ↔ NormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input packet := by
  rw [S1_binary.sat_l]
  simp only [normalizedInput_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,T,_,n,_,L,_,F,_,r,_,X,_,e,_,k,_,a,_,z,_,f,_,P,_,cert⟩
    exact normalizedInputCheck_sound_l hZF hω cert
  · rintro ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩
    obtain ⟨P,cert⟩ := normalizedInputCheck_for_l hZF hω outer inner parameters valid code
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [T,n,L,F,r,X,e,k,a,z,f,P]
    exact ⟨w,T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
      X,hw X (by simp),e,hw e (by simp),k,hw k (by simp),a,hw a (by simp),z,hw z (by simp),
        f,hw f (by simp),P,hw P (by simp),cert⟩

/-- 给定原合法解码后，图只恢复唯一规范完整赋值及空见证槽。 -/
theorem normalizedInput_fixed_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r e k a input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e) (outer : Rd_triple_d input e k a) :
    normalizedInput_s.schema.denote ρ input packet ↔
      ∃ X z f, Rd_triple_d packet e f z ∧ ParameterCheck_d (ρ.bound 0) k n X a z f := by
  rw [normalizedInput_sat_l hZF ρ input packet hω]
  constructor
  · rintro ⟨U,m,K,G,s,X,b,j,c,z,f,other,inner,parameters,_,codeU⟩
    obtain ⟨eqe,eqk,eqa⟩ := pc_triple_inj_l other outer
    subst b; subst j; subst c
    obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
    subst m; subst K; subst G; subst s
    exact ⟨X,z,f,inner,parameters⟩
  · rintro ⟨X,z,f,inner,parameters⟩
    exact ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩

theorem normalizedInput_unique_l (hZF : M.Models ZF) (ρ : Env M 1) {input packet other : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (left : normalizedInput_s.schema.denote ρ input packet)
    (right : normalizedInput_s.schema.denote ρ input other) : packet = other := by
  obtain ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,_,code⟩ := (normalizedInput_sat_l hZF ρ input packet hω).mp left
  obtain ⟨U,m,K,G,s,Y,b,j,c,t,g,outer',inner',parameters',_,code'⟩ := (normalizedInput_sat_l hZF ρ input other hω).mp right
  obtain ⟨eqe,eqk,eqa⟩ := pc_triple_inj_l outer' outer
  subst b; subst j; subst c
  obtain ⟨eqn,eqL,eqF,eqr⟩ := code'.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
  subst m; subst K; subst G; subst s
  have zeq := num_unique_l hZF.1 parameters.zero parameters'.zero
  subst t
  have feq := parameters.unique_l (ZF.modelsKP hZF) parameters'
  subst g
  exact normalizedTriple_unique_l hZF.1 inner inner'

theorem normalizedInput_exists_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r X e k a z input : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e) (outer : Rd_triple_d input e k a)
    (kn : M.mem k n) (zero : Num_d 0 z) (hz : M.mem z X) (ha : Fn0_d k X a) :
    ∃ packet, normalizedInput_s.schema.denote ρ input packet := by
  obtain ⟨f,parameters⟩ := parameterCheck_exists_l hZF hω valid.variables kn zero hz ha
  obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f z
  obtain ⟨packet,hpacket⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
  exact ⟨packet,(normalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,X,e,k,a,z,f,outer,⟨q,hq,hpacket⟩,parameters,valid,code⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
