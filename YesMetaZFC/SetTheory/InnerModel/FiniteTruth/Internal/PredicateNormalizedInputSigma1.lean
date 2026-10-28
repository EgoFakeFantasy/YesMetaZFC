import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNormalizedInputCertificate

/-! # 只有内部 ω 参数的唯一规范输入 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def pnormalizedInput_s : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <| Formula.existsMem (.bound 9) <| Formula.existsMem (.bound 10) <| Formula.existsMem (.bound 11) <|
      pnormalizedInputCheck_m (.bound 16) (.bound 14) (.bound 13) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
        (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (pnormalizedInputCheck_delta_l ..)))))))))))) }

theorem pnormalizedInput_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 2) (input packet w : M.Domain) :
    Formula.satisfies (((ρ.push input).push packet).push w) pnormalizedInput_s.matrix.body ↔
      ∃ T, M.mem T w ∧ ∃ n, M.mem n w ∧ ∃ L, M.mem L w ∧ ∃ F, M.mem F w ∧ ∃ r, M.mem r w ∧
        ∃ X, M.mem X w ∧ ∃ e, M.mem e w ∧ ∃ k, M.mem k w ∧ ∃ a, M.mem a w ∧ ∃ z, M.mem z w ∧
          ∃ f, M.mem f w ∧ ∃ P, M.mem P w ∧ PNormalizedInputCheck_d (ρ.bound 1) input packet T n L F r X e k a z f P := by
  simp only [pnormalizedInput_s,Formula.satisfies_existsMem_iff,pnormalizedInputCheck_sat_l hKP]
  rfl

theorem pnormalizedInput_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (input packet : M.Domain) (hω : M.IsOmega (ρ.bound 1)) :
    pnormalizedInput_s.schema.denote ρ input packet ↔ PNormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) input packet := by
  rw [S1_binary.sat_l]
  simp only [pnormalizedInput_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,T,_,n,_,L,_,F,_,r,_,X,_,e,_,k,_,a,_,z,_,f,_,P,_,cert⟩
    exact pnormalizedInputCheck_sound_l hZF hω cert
  · rintro ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩
    obtain ⟨P,cert⟩ := pnormalizedInputCheck_for_l hZF hω outer inner parameters valid code
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [T,n,L,F,r,X,e,k,a,z,f,P]
    exact ⟨w,T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
      X,hw X (by simp),e,hw e (by simp),k,hw k (by simp),a,hw a (by simp),z,hw z (by simp),
        f,hw f (by simp),P,hw P (by simp),cert⟩

/-- 给定原合法解码后，图只恢复唯一规范完整赋值及空见证槽。 -/
theorem pnormalizedInput_fixed_l (hZF : M.Models ZF) (ρ : Env M 2) {T n L F r e k a input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e) (outer : Rd_triple_d input e k a) :
    pnormalizedInput_s.schema.denote ρ input packet ↔
      ∃ X z f, Rd_triple_d packet e f z ∧ ParameterCheck_d (ρ.bound 1) k n X a z f := by
  rw [pnormalizedInput_sat_l hZF ρ input packet hω]
  constructor
  · rintro ⟨U,m,K,G,s,X,b,j,c,z,f,other,inner,parameters,_,codeU⟩
    obtain ⟨eqe,eqk,eqa⟩ := pc_triple_inj_l other outer
    subst b; subst j; subst c
    obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
    subst m; subst K; subst G; subst s
    exact ⟨X,z,f,inner,parameters⟩
  · rintro ⟨X,z,f,inner,parameters⟩
    exact ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩

theorem pnormalizedInput_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input packet other : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (left : pnormalizedInput_s.schema.denote ρ input packet)
    (right : pnormalizedInput_s.schema.denote ρ input other) : packet = other := by
  obtain ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,_,code⟩ := (pnormalizedInput_sat_l hZF ρ input packet hω).mp left
  obtain ⟨U,m,K,G,s,Y,b,j,c,t,g,outer',inner',parameters',_,code'⟩ := (pnormalizedInput_sat_l hZF ρ input other hω).mp right
  obtain ⟨eqe,eqk,eqa⟩ := pc_triple_inj_l outer' outer
  subst b; subst j; subst c
  obtain ⟨eqn,eqL,eqF,eqr⟩ := code'.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
  subst m; subst K; subst G; subst s
  have zeq := num_unique_l hZF.1 parameters.zero parameters'.zero
  subst t
  have feq := parameters.unique_l (ZF.modelsKP hZF) parameters'
  subst g
  exact normalizedTriple_unique_l hZF.1 inner inner'

theorem pnormalizedInput_exists_l (hZF : M.Models ZF) (ρ : Env M 2) {T n L F r X e k a z input : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (valid : PBoundedFormula_d T (ρ.bound 1) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) n L F r e) (outer : Rd_triple_d input e k a)
    (kn : M.mem k n) (zero : Num_d 0 z) (hz : M.mem z X) (ha : Fn0_d k X a) :
    ∃ packet, pnormalizedInput_s.schema.denote ρ input packet := by
  obtain ⟨f,parameters⟩ := parameterCheck_exists_l hZF hω valid.variables kn zero hz ha
  obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total f z
  obtain ⟨packet,hpacket⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
  exact ⟨packet,(pnormalizedInput_sat_l hZF ρ input packet hω).mpr ⟨T,n,L,F,r,X,e,k,a,z,f,outer,⟨q,hq,hpacket⟩,parameters,valid,code⟩⟩


/-- 规范化完全忽略外部谓词参数与自由环境，只读取同一个内部 ω。 -/
theorem pnormalizedInput_background_independent_l (hZF : M.Models ZF) (ρ η : Env M 2) (input packet : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (sameOmega : ρ.bound 1 = η.bound 1) :
    pnormalizedInput_s.schema.denote ρ input packet ↔ pnormalizedInput_s.schema.denote η input packet := by
  have hωη : M.IsOmega (η.bound 1) := sameOmega ▸ hω
  exact (pnormalizedInput_sat_l hZF ρ input packet hω).trans
    (by simpa only [sameOmega] using (pnormalizedInput_sat_l hZF η input packet hωη).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
