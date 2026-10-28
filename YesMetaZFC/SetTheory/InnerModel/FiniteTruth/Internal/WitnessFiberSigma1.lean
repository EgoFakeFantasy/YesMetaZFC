import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.WitnessFiberCertificate

/-! # 原数码和参数赋值上的统一见证关系 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def witnessFiber_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <| Formula.existsMem (.bound 9) <| Formula.existsMem (.bound 10) <| Formula.existsMem (.bound 11) <|
      witnessFiberCheck_m (.bound 15) (.bound 14) (.bound 13) (.bound 11) (.bound 10) (.bound 9)
        (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (witnessFiberCheck_delta_l ..)))))))))))) }

theorem witnessFiber_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 1) (input y w : M.Domain) :
    Formula.satisfies (((ρ.push input).push y).push w) witnessFiber_s.matrix.body ↔
      ∃ T, M.mem T w ∧ ∃ n, M.mem n w ∧ ∃ L, M.mem L w ∧ ∃ F, M.mem F w ∧ ∃ r, M.mem r w ∧
        ∃ X, M.mem X w ∧ ∃ e, M.mem e w ∧ ∃ f, M.mem f w ∧ ∃ i, M.mem i w ∧ ∃ g, M.mem g w ∧
          ∃ P, M.mem P w ∧ ∃ Q, M.mem Q w ∧ WitnessFiberCheck_d (ρ.bound 0) input y T n L F r X e f i g P Q := by
  simp only [witnessFiber_s,Formula.satisfies_existsMem_iff,witnessFiberCheck_sat_l hKP]
  rfl

theorem witnessFiber_sat_l (hZF : M.Models ZF) (ρ : Env M 1) (input y : M.Domain) (hω : M.IsOmega (ρ.bound 0)) :
    witnessFiber_s.schema.denote ρ input y ↔ WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) input y := by
  rw [S1_binary.sat_l]
  simp only [witnessFiber_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,T,_,n,_,L,_,F,_,r,_,X,_,e,_,f,_,i,_,g,_,P,_,Q,_,cert⟩
    exact witnessFiberCheck_sound_l hZF hω cert
  · intro fiber
    obtain ⟨T,n,L,F,r,X,e,f,i,g,P,Q,cert⟩ := witnessFiberCheck_exists_l hZF hω fiber
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [T,n,L,F,r,X,e,f,i,g,P,Q]
    exact ⟨w,T,hw T (by simp),n,hw n (by simp),L,hw L (by simp),F,hw F (by simp),r,hw r (by simp),
      X,hw X (by simp),e,hw e (by simp),f,hw f (by simp),i,hw i (by simp),g,hw g (by simp),
      P,hw P (by simp),Q,hw Q (by simp),cert⟩

/-- 原数码、参数赋值与槽固定后，统一关系只断言该槽更新使原程序为真。 -/
theorem witnessFiber_fixed_l (hZF : M.Models ZF) (ρ : Env M 1) {T n L F r X e f i input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (valid : BoundedFormula_d T (ρ.bound 0) n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) n L F r e)
    (packet : Rd_triple_d input e f i) (hx : M.TransitiveSet X) (hi : M.mem i n)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) (hy : M.mem y X) :
    witnessFiber_s.schema.denote ρ input y ↔ ∃ g, Senv_update_d (kp_pair_l (ZF.modelsKP hZF)) f i y g ∧
      FiniteTruth_d true T (ρ.bound 0) n X F L r g := by
  rw [witnessFiber_sat_l hZF ρ input y hω]
  constructor
  · rintro ⟨U,m,K,G,s,Y,a,b,j,g,other,hy',validU,codeU,_,_,_,update,truthY⟩
    obtain ⟨eqe,eqf,eqi⟩ := pc_triple_inj_l other packet
    subst a; subst b; subst j
    obtain ⟨eqn,eqL,eqF,eqr⟩ := codeU.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code
    subst m; subst K; subst G; subst s
    have hgX := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hf hi hy
    have hgY := finiteTruth_function_l hZF true hω truthY
    have truthT := (finiteTruth_container_choice_l (ZF.modelsKP hZF) true validU valid).mp truthY
    exact ⟨g,update,(finiteTruth_domain_choice_l hZF true hω hy' hx hgY hgX valid code.2.2.1).mp truthT⟩
  · rintro ⟨g,update,truth⟩
    exact ⟨T,n,L,F,r,X,e,f,i,g,packet,hx,valid,code,hi,hf,hy,update,truth⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
