import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramNumberSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramContainerChoice
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthDomain

/-! # 仅余背景集合谓词和内部 ω 参数的数码真值证书

全部代码参数、传递求值域和完整证书在原有界见证中恢复；A 不进入赋值或见证束。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PProgramWitness_d (T ω n L F r e W : M.Domain) : Prop :=
  ∃ G, M.mem G W ∧ ∃ c, M.mem c W ∧ ∃ d, M.mem d W ∧ ∃ R, M.mem R W ∧
    ∃ Q, M.mem Q W ∧ ∃ p, M.mem p W ∧ ∃ q, M.mem q W ∧ PProgramCheck_d T ω n L F r e G c d R Q p q

def pprogramWitness_m {k} (T ω n L F r e W : Term k) : Formula 1 k :=
  Formula.existsMem W <| Formula.existsMem W.weaken <| Formula.existsMem W.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken <| pprogramCheck_m T.weaken.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken.weaken.weaken.weaken e.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed pprogramWitness_m

theorem pprogramWitness_delta_l {k} (T ω n L F r e W : Term k) : (pprogramWitness_m T ω n L F r e W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (pprogramCheck_delta_l ..)))))))

theorem pprogramWitness_sat_l (hKP : M.Models KP) {k} (ρ : Env M k) (T ω n L F r e W : Term k) :
    Formula.satisfies ρ (pprogramWitness_m T ω n L F r e W) ↔
      PProgramWitness_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (r.eval ρ) (e.eval ρ) (W.eval ρ) := by
  simp only [pprogramWitness_m,PProgramWitness_d,Formula.satisfies_existsMem_iff,pprogramCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def PTruthWitness_d (positive : Bool) (T A ω n X F L r f W : M.Domain) : Prop :=
  ∃ e, M.mem e W ∧ ∃ s, M.mem s W ∧ ∃ Z, M.mem Z W ∧ ∃ S, M.mem S W ∧
    ∃ E, M.mem E W ∧ ∃ V, M.mem V W ∧ ∃ H, M.mem H W ∧ PFiniteTruthCert_d positive T A ω n X F L r f e s Z S E V H

def pfiniteTruthCert_m {k} (positive : Bool) (T A ω n X F L r f e s Z S E V H : Term k) : Formula 1 k :=
  .conj (assignmentSpaceCert_m ω n X e s Z S E) <| .conj (.mem f E) <|
    .conj (ptruthCheck_m T A n X E F L V H) (btruthAnswer_m positive H r f)
derive_free_closed pfiniteTruthCert_m

theorem pfiniteTruthCert_delta_l {k} (positive : Bool) (T A ω n X F L r f e s Z S E V H : Term k) :
    (pfiniteTruthCert_m positive T A ω n X F L r f e s Z S E V H).IsDelta0 :=
  .conj (assignmentSpaceCert_delta_l ..) (.conj (.mem _ _) (.conj (ptruthCheck_delta_l ..) (btruthAnswer_delta_l ..)))

theorem pfiniteTruthCert_sat_l (hE : Extensional M) {k} (positive : Bool) (ρ : Env M k)
    (T A ω n X F L r f e s Z S E V H : Term k) :
    Formula.satisfies ρ (pfiniteTruthCert_m positive T A ω n X F L r f e s Z S E V H) ↔
      PFiniteTruthCert_d positive (T.eval ρ) (A.eval ρ) (ω.eval ρ) (n.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ)
        (e.eval ρ) (s.eval ρ) (Z.eval ρ) (S.eval ρ) (E.eval ρ) (V.eval ρ) (H.eval ρ) := by
  simp only [pfiniteTruthCert_m,PFiniteTruthCert_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    assignmentSpaceCert_sat_l hE,ptruthCheck_sat_l hE,btruthAnswer_sat_l hE]

def ptruthWitness_m {k} (positive : Bool) (T A ω n X F L r f W : Term k) : Formula 1 k :=
  Formula.existsMem W <| Formula.existsMem W.weaken <| Formula.existsMem W.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken <| Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken <| pfiniteTruthCert_m positive T.weaken.weaken.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken.weaken.weaken F.weaken.weaken.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed ptruthWitness_m

theorem ptruthWitness_delta_l {k} (positive : Bool) (T A ω n X F L r f W : Term k) :
    (ptruthWitness_m positive T A ω n X F L r f W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (pfiniteTruthCert_delta_l ..)))))))

theorem ptruthWitness_sat_l (hE : Extensional M) {k} (positive : Bool) (ρ : Env M k) (T A ω n X F L r f W : Term k) :
    Formula.satisfies ρ (ptruthWitness_m positive T A ω n X F L r f W) ↔
      PTruthWitness_d positive (T.eval ρ) (A.eval ρ) (ω.eval ρ) (n.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (r.eval ρ) (f.eval ρ) (W.eval ρ) := by
  simp only [ptruthWitness_m,PTruthWitness_d,Formula.satisfies_existsMem_iff,pfiniteTruthCert_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def PNumberedTruthCheck_d (positive : Bool) (ω A e f T n L F r X P Q : M.Domain) : Prop :=
  M.TransitiveSet X ∧ PProgramWitness_d T ω n L F r e P ∧ PTruthWitness_d positive T A ω n X F L r f Q

def pnumberedTruthCheck_m {k} (positive : Bool) (ω A e f T n L F r X P Q : Term k) : Formula 1 k :=
  .conj (Formula.isTransitive X) (.conj (pprogramWitness_m T ω n L F r e P) (ptruthWitness_m positive T A ω n X F L r f Q))
derive_free_closed pnumberedTruthCheck_m

theorem pnumberedTruthCheck_delta_l {k} (positive : Bool) (ω A e f T n L F r X P Q : Term k) :
    (pnumberedTruthCheck_m positive ω A e f T n L F r X P Q).IsDelta0 :=
  .conj (Formula.isTransitive_delta0 _) (.conj (pprogramWitness_delta_l ..) (ptruthWitness_delta_l ..))

theorem pnumberedTruthCheck_sat_l (hKP : M.Models KP) {k} (positive : Bool) (ρ : Env M k) (ω A e f T n L F r X P Q : Term k) :
    Formula.satisfies ρ (pnumberedTruthCheck_m positive ω A e f T n L F r X P Q) ↔
      PNumberedTruthCheck_d positive (ω.eval ρ) (A.eval ρ) (e.eval ρ) (f.eval ρ) (T.eval ρ) (n.eval ρ) (L.eval ρ)
        (F.eval ρ) (r.eval ρ) (X.eval ρ) (P.eval ρ) (Q.eval ρ) := by
  simp only [pnumberedTruthCheck_m,PNumberedTruthCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,
    pprogramWitness_sat_l hKP,ptruthWitness_sat_l hKP.1]

def PNumberedTruth_d (I : kpair_convention_l.Interpretation M) (positive : Bool) (A ω e f : M.Domain) : Prop :=
  ∃ T n L F r X, M.TransitiveSet X ∧ PBoundedFormula_d T ω n L F ∧ ProgramNumber_d I ω n L F r e ∧
    PFiniteTruth_d positive T A ω n X F L r f

theorem pnumberedTruthCheck_sound_l (hZF : M.Models ZF) (positive : Bool) {ω A e f T n L F r X P Q : M.Domain}
    (hω : M.IsOmega ω) (cert : PNumberedTruthCheck_d positive ω A e f T n L F r X P Q) :
    PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive A ω e f := by
  obtain ⟨hx,⟨G,_,c,_,d,_,R,_,Q',_,p,_,q,_,pcert⟩,⟨a,_,s,_,Z,_,S,_,E,_,V,_,H,_,tcert⟩⟩ := cert
  obtain ⟨valid,code⟩ := pprogramCheck_sound_l hZF hω pcert
  exact ⟨T,n,L,F,r,X,hx,valid,code,a,s,Z,S,E,V,H,tcert⟩

theorem pnumberedTruthCheck_exists_l (hZF : M.Models ZF) (positive : Bool) {ω A e f : M.Domain}
    (hω : M.IsOmega ω) (truth : PNumberedTruth_d (kp_pair_l (ZF.modelsKP hZF)) positive A ω e f) :
    ∃ T n L F r X P Q, PNumberedTruthCheck_d positive ω A e f T n L F r X P Q := by
  obtain ⟨T,n,L,F,r,X,hx,valid,code,a,s,Z,S,E,V,H,tcert⟩ := truth
  obtain ⟨G,c,d,R,Q',p,q,pcert⟩ := pprogramCheck_exists_l hZF hω valid code
  obtain ⟨P,hP⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q',p,q]
  obtain ⟨Q,hQ⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [a,s,Z,S,E,V,H]
  exact ⟨T,n,L,F,r,X,P,Q,hx,
    ⟨G,hP G (by simp),c,hP c (by simp),d,hP d (by simp),R,hP R (by simp),Q',hP Q' (by simp),p,hP p (by simp),q,hP q (by simp),pcert⟩,
    ⟨a,hQ a (by simp),s,hQ s (by simp),Z,hQ Z (by simp),S,hQ S (by simp),E,hQ E (by simp),V,hQ V (by simp),H,hQ H (by simp),tcert⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
