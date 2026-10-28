import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignment
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedTruthCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NormalizedInputCertificate

/-! # 原数码与参数列到唯一规范见证输入的完整证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PNormalizedInput_d (I : kpair_convention_l.Interpretation M) (ω input packet : M.Domain) : Prop :=
  ∃ T n L F r X e k a z f, Rd_triple_d input e k a ∧ Rd_triple_d packet e f z ∧
    ParameterCheck_d ω k n X a z f ∧ PBoundedFormula_d T ω n L F ∧ ProgramNumber_d I ω n L F r e

def PNormalizedInputCheck_d (ω input packet T n L F r X e k a z f P : M.Domain) : Prop :=
  Rd_triple_d input e k a ∧ Rd_triple_d packet e f z ∧ ParameterCheck_d ω k n X a z f ∧ PProgramWitness_d T ω n L F r e P

def pnormalizedInputCheck_m {d} (ω input packet T n L F r X e k a z f P : Term d) : Formula 1 d :=
  .conj (rd_triple0_m input e k a) <| .conj (rd_triple0_m packet e f z) <|
    .conj (parameterCheck_m ω k n X a z f) (pprogramWitness_m T ω n L F r e P)
derive_free_closed pnormalizedInputCheck_m

theorem pnormalizedInputCheck_delta_l {d} (ω input packet T n L F r X e k a z f P : Term d) :
    (pnormalizedInputCheck_m ω input packet T n L F r X e k a z f P).IsDelta0 :=
  .conj (rd_triple0_delta_l ..) (.conj (rd_triple0_delta_l ..) (.conj (parameterCheck_delta_l ..) (pprogramWitness_delta_l ..)))

theorem pnormalizedInputCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω input packet T n L F r X e k a z f P : Term d) :
    Formula.satisfies ρ (pnormalizedInputCheck_m ω input packet T n L F r X e k a z f P) ↔
      PNormalizedInputCheck_d (ω.eval ρ) (input.eval ρ) (packet.eval ρ) (T.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ)
        (r.eval ρ) (X.eval ρ) (e.eval ρ) (k.eval ρ) (a.eval ρ) (z.eval ρ) (f.eval ρ) (P.eval ρ) := by
  simp only [pnormalizedInputCheck_m,PNormalizedInputCheck_d,Formula.satisfies_conj_iff,rd_triple0_sat_l hKP.1,
    parameterCheck_sat_l hKP.1,pprogramWitness_sat_l hKP]

theorem pnormalizedInputCheck_sound_l (hZF : M.Models ZF) {ω input packet T n L F r X e k a z f P : M.Domain}
    (hω : M.IsOmega ω) (cert : PNormalizedInputCheck_d ω input packet T n L F r X e k a z f P) :
    PNormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) ω input packet := by
  obtain ⟨outer,inner,parameters,G,_,c,_,d,_,R,_,Q,_,p,_,q,_,program⟩ := cert
  obtain ⟨valid,code⟩ := pprogramCheck_sound_l hZF hω program
  exact ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩

theorem pnormalizedInputCheck_for_l (hZF : M.Models ZF) {ω input packet T n L F r X e k a z f : M.Domain}
    (hω : M.IsOmega ω) (outer : Rd_triple_d input e k a) (inner : Rd_triple_d packet e f z)
    (parameters : ParameterCheck_d ω k n X a z f) (valid : PBoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e) :
    ∃ P, PNormalizedInputCheck_d ω input packet T n L F r X e k a z f P := by
  obtain ⟨G,c,d,R,Q,p,q,cert⟩ := pprogramCheck_exists_l hZF hω valid code
  obtain ⟨P,hP⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q,p,q]
  exact ⟨P,outer,inner,parameters,G,hP G (by simp),c,hP c (by simp),d,hP d (by simp),R,hP R (by simp),
    Q,hP Q (by simp),p,hP p (by simp),q,hP q (by simp),cert⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
