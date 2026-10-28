import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignment
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedTruthCertificate

/-! # 原数码与参数列到唯一规范见证输入的完整证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def NormalizedInput_d (I : kpair_convention_l.Interpretation M) (ω input packet : M.Domain) : Prop :=
  ∃ T n L F r X e k a z f, Rd_triple_d input e k a ∧ Rd_triple_d packet e f z ∧
    ParameterCheck_d ω k n X a z f ∧ BoundedFormula_d T ω n L F ∧ ProgramNumber_d I ω n L F r e

def NormalizedInputCheck_d (ω input packet T n L F r X e k a z f P : M.Domain) : Prop :=
  Rd_triple_d input e k a ∧ Rd_triple_d packet e f z ∧ ParameterCheck_d ω k n X a z f ∧ ProgramWitness_d T ω n L F r e P

def normalizedInputCheck_m {d} (ω input packet T n L F r X e k a z f P : Term d) : Formula 1 d :=
  .conj (rd_triple0_m input e k a) <| .conj (rd_triple0_m packet e f z) <|
    .conj (parameterCheck_m ω k n X a z f) (programWitness_m T ω n L F r e P)
derive_free_closed normalizedInputCheck_m

theorem normalizedInputCheck_delta_l {d} (ω input packet T n L F r X e k a z f P : Term d) :
    (normalizedInputCheck_m ω input packet T n L F r X e k a z f P).IsDelta0 :=
  .conj (rd_triple0_delta_l ..) (.conj (rd_triple0_delta_l ..) (.conj (parameterCheck_delta_l ..) (programWitness_delta_l ..)))

theorem normalizedInputCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω input packet T n L F r X e k a z f P : Term d) :
    Formula.satisfies ρ (normalizedInputCheck_m ω input packet T n L F r X e k a z f P) ↔
      NormalizedInputCheck_d (ω.eval ρ) (input.eval ρ) (packet.eval ρ) (T.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ)
        (r.eval ρ) (X.eval ρ) (e.eval ρ) (k.eval ρ) (a.eval ρ) (z.eval ρ) (f.eval ρ) (P.eval ρ) := by
  simp only [normalizedInputCheck_m,NormalizedInputCheck_d,Formula.satisfies_conj_iff,rd_triple0_sat_l hKP.1,
    parameterCheck_sat_l hKP.1,programWitness_sat_l hKP]

theorem normalizedInputCheck_sound_l (hZF : M.Models ZF) {ω input packet T n L F r X e k a z f P : M.Domain}
    (hω : M.IsOmega ω) (cert : NormalizedInputCheck_d ω input packet T n L F r X e k a z f P) :
    NormalizedInput_d (kp_pair_l (ZF.modelsKP hZF)) ω input packet := by
  obtain ⟨outer,inner,parameters,G,_,c,_,d,_,R,_,Q,_,p,_,q,_,program⟩ := cert
  obtain ⟨valid,code⟩ := programCheck_sound_l hZF hω program
  exact ⟨T,n,L,F,r,X,e,k,a,z,f,outer,inner,parameters,valid,code⟩

theorem normalizedInputCheck_for_l (hZF : M.Models ZF) {ω input packet T n L F r X e k a z f : M.Domain}
    (hω : M.IsOmega ω) (outer : Rd_triple_d input e k a) (inner : Rd_triple_d packet e f z)
    (parameters : ParameterCheck_d ω k n X a z f) (valid : BoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e) :
    ∃ P, NormalizedInputCheck_d ω input packet T n L F r X e k a z f P := by
  obtain ⟨G,c,d,R,Q,p,q,cert⟩ := programCheck_exists_l hZF hω valid code
  obtain ⟨P,hP⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q,p,q]
  exact ⟨P,outer,inner,parameters,G,hP G (by simp),c,hP c (by simp),d,hP d (by simp),R,hP R (by simp),
    Q,hP Q (by simp),p,hP p (by simp),q,hP q (by simp),cert⟩

theorem normalizedTriple_unique_l (hE : Extensional M) {p q a b c : M.Domain}
    (hp : Rd_triple_d p a b c) (hq : Rd_triple_d q a b c) : p = q := by
  obtain ⟨x,hx,hp⟩ := hp
  obtain ⟨y,hy,hq⟩ := hq
  have eq := kpair_unique_l M hE hx hy
  subst y
  exact kpair_unique_l M hE hp hq

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
