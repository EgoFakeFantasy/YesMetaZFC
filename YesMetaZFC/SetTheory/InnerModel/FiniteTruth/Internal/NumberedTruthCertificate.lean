import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumberSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramContainerChoice
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthDomain

/-! # 数码和赋值上的统一操作真值证书

语法容器、程序参数及传递求值域全部进入存在见证；原数码和原操作解释不变。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def ProgramWitness_d (T ω n L F r e W : M.Domain) : Prop :=
  ∃ G, M.mem G W ∧ ∃ c, M.mem c W ∧ ∃ d, M.mem d W ∧ ∃ R, M.mem R W ∧
    ∃ Q, M.mem Q W ∧ ∃ p, M.mem p W ∧ ∃ q, M.mem q W ∧ ProgramCheck_d T ω n L F r e G c d R Q p q

def programWitness_m {k} (T ω n L F r e W : Term k) : Formula 1 k :=
  Formula.existsMem W <| Formula.existsMem W.weaken <| Formula.existsMem W.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken <| programCheck_m T.weaken.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed programWitness_m

theorem programWitness_delta_l {k} (T ω n L F r e W : Term k) : (programWitness_m T ω n L F r e W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (programCheck_delta_l ..)))))))

theorem programWitness_sat_l (hKP : M.Models KP) {k} (ρ : Env M k) (T ω n L F r e W : Term k) :
    Formula.satisfies ρ (programWitness_m T ω n L F r e W) ↔
      ProgramWitness_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (r.eval ρ) (e.eval ρ) (W.eval ρ) := by
  simp only [programWitness_m,ProgramWitness_d,Formula.satisfies_existsMem_iff,programCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def TruthWitness_d (positive : Bool) (T ω n X F L r f W : M.Domain) : Prop :=
  ∃ e, M.mem e W ∧ ∃ s, M.mem s W ∧ ∃ Z, M.mem Z W ∧ ∃ S, M.mem S W ∧
    ∃ E, M.mem E W ∧ ∃ V, M.mem V W ∧ ∃ H, M.mem H W ∧ FiniteTruthCert_d positive T ω n X F L r f e s Z S E V H

def finiteTruthCert_m {k} (positive : Bool) (T ω n X F L r f e s Z S E V H : Term k) : Formula 1 k :=
  .conj (assignmentSpaceCert_m ω n X e s Z S E) <| .conj (.mem f E) <|
    .conj (btruthCheck_m T n X E F L V H) (btruthAnswer_m positive H r f)
derive_free_closed finiteTruthCert_m

theorem finiteTruthCert_delta_l {k} (positive : Bool) (T ω n X F L r f e s Z S E V H : Term k) :
    (finiteTruthCert_m positive T ω n X F L r f e s Z S E V H).IsDelta0 :=
  .conj (assignmentSpaceCert_delta_l ..) (.conj (.mem _ _) (.conj (btruthCheck_delta_l ..) (btruthAnswer_delta_l ..)))

theorem finiteTruthCert_sat_l (hE : Extensional M) {k} (positive : Bool) (ρ : Env M k)
    (T ω n X F L r f e s Z S E V H : Term k) :
    Formula.satisfies ρ (finiteTruthCert_m positive T ω n X F L r f e s Z S E V H) ↔
      FiniteTruthCert_d positive (T.eval ρ) (ω.eval ρ) (n.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ)
        (e.eval ρ) (s.eval ρ) (Z.eval ρ) (S.eval ρ) (E.eval ρ) (V.eval ρ) (H.eval ρ) := by
  simp only [finiteTruthCert_m,FiniteTruthCert_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    assignmentSpaceCert_sat_l hE,btruthCheck_sat_l hE,btruthAnswer_sat_l hE]

def truthWitness_m {k} (positive : Bool) (T ω n X F L r f W : Term k) : Formula 1 k :=
  Formula.existsMem W <| Formula.existsMem W.weaken <| Formula.existsMem W.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken <| finiteTruthCert_m positive T.weaken.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed truthWitness_m

theorem truthWitness_delta_l {k} (positive : Bool) (T ω n X F L r f W : Term k) :
    (truthWitness_m positive T ω n X F L r f W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (finiteTruthCert_delta_l ..)))))))

theorem truthWitness_sat_l (hE : Extensional M) {k} (positive : Bool) (ρ : Env M k) (T ω n X F L r f W : Term k) :
    Formula.satisfies ρ (truthWitness_m positive T ω n X F L r f W) ↔
      TruthWitness_d positive (T.eval ρ) (ω.eval ρ) (n.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ) (W.eval ρ) := by
  simp only [truthWitness_m,TruthWitness_d,Formula.satisfies_existsMem_iff,finiteTruthCert_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def NumberedTruthCheck_d (positive : Bool) (ω e f T n L F r X P Q : M.Domain) : Prop :=
  M.TransitiveSet X ∧ ProgramWitness_d T ω n L F r e P ∧ TruthWitness_d positive T ω n X F L r f Q

def numberedTruthCheck_m {k} (positive : Bool) (ω e f T n L F r X P Q : Term k) : Formula 1 k :=
  .conj (Formula.isTransitive X) (.conj (programWitness_m T ω n L F r e P) (truthWitness_m positive T ω n X F L r f Q))
derive_free_closed numberedTruthCheck_m

theorem numberedTruthCheck_delta_l {k} (positive : Bool) (ω e f T n L F r X P Q : Term k) :
    (numberedTruthCheck_m positive ω e f T n L F r X P Q).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (programWitness_delta_l ..) (truthWitness_delta_l ..))

theorem numberedTruthCheck_sat_l (hKP : M.Models KP) {k} (positive : Bool) (ρ : Env M k) (ω e f T n L F r X P Q : Term k) :
    Formula.satisfies ρ (numberedTruthCheck_m positive ω e f T n L F r X P Q) ↔
      NumberedTruthCheck_d positive (ω.eval ρ) (e.eval ρ) (f.eval ρ) (T.eval ρ) (n.eval ρ) (L.eval ρ)
        (F.eval ρ) (r.eval ρ) (X.eval ρ) (P.eval ρ) (Q.eval ρ) := by
  simp only [numberedTruthCheck_m,NumberedTruthCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,
    programWitness_sat_l hKP,truthWitness_sat_l hKP.1]

def NumberedTruth_d (I : kpair_convention_l.Interpretation M) (positive : Bool) (ω e f : M.Domain) : Prop :=
  ∃ T n L F r X, M.TransitiveSet X ∧ BoundedFormula_d T ω n L F ∧ ProgramNumber_d I ω n L F r e ∧
    FiniteTruth_d positive T ω n X F L r f

theorem numberedTruthCheck_sound_l (hZF : M.Models ZF) (positive : Bool) {ω e f T n L F r X P Q : M.Domain}
    (hω : M.IsOmega ω) (cert : NumberedTruthCheck_d positive ω e f T n L F r X P Q) :
    NumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive ω e f := by
  obtain ⟨hx,⟨G,_,c,_,d,_,R,_,Q',_,p,_,q,_,pcert⟩,⟨a,_,s,_,Z,_,S,_,E,_,V,_,H,_,tcert⟩⟩ := cert
  obtain ⟨valid,code⟩ := programCheck_sound_l hZF hω pcert
  exact ⟨T,n,L,F,r,X,hx,valid,code,a,s,Z,S,E,V,H,tcert⟩

theorem numberedTruthCheck_exists_l (hZF : M.Models ZF) (positive : Bool) {ω e f : M.Domain}
    (hω : M.IsOmega ω) (truth : NumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive ω e f) :
    ∃ T n L F r X P Q, NumberedTruthCheck_d positive ω e f T n L F r X P Q := by
  obtain ⟨T,n,L,F,r,X,hx,valid,code,a,s,Z,S,E,V,H,tcert⟩ := truth
  obtain ⟨G,c,d,R,Q',p,q,pcert⟩ := programCheck_exists_l hZF hω valid code
  obtain ⟨P,hP⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q',p,q]
  obtain ⟨Q,hQ⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [a,s,Z,S,E,V,H]
  exact ⟨T,n,L,F,r,X,P,Q,hx,
    ⟨G,hP G (by simp),c,hP c (by simp),d,hP d (by simp),R,hP R (by simp),Q',hP Q' (by simp),p,hP p (by simp),q,hP q (by simp),pcert⟩,
    ⟨a,hQ a (by simp),s,hQ s (by simp),Z,hQ Z (by simp),S,hQ S (by simp),E,hQ E (by simp),V,hQ V (by simp),H,hQ H (by simp),tcert⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
