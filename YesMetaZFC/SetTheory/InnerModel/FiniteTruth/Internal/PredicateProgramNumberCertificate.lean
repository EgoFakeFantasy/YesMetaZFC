import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumberCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedRowsSigma1

/-! # 同一个原程序编号关系的五类程序完整有界证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PRowsWitness_d (T ω n L F G R : M.Domain) : Prop := ∃ V, M.mem V R ∧ PRowsNumberCheck_d T ω n L F G V

def prowsWitness_m {d} (T ω n L F G R : Term d) : Formula 1 d :=
  Formula.existsMem R (prowsNumberCheck_m T.weaken ω.weaken n.weaken L.weaken F.weaken G.weaken .newest)
derive_free_closed prowsWitness_m

theorem prowsWitness_delta_l {d} (T ω n L F G R : Term d) : (prowsWitness_m T ω n L F G R).IsDelta0 :=
  .existsMem _ (prowsNumberCheck_delta_l ..)

theorem prowsWitness_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n L F G R : Term d) :
    Formula.satisfies ρ (prowsWitness_m T ω n L F G R) ↔
      PRowsWitness_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (G.eval ρ) (R.eval ρ) := by
  simp only [prowsWitness_m,PRowsWitness_d,Formula.satisfies_existsMem_iff,prowsNumberCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def PProgramCheck_d (T ω n L F r e G c d R Q p q : M.Domain) : Prop :=
  M.mem c ω ∧ M.mem d ω ∧ M.mem r L ∧ PRowsWitness_d T ω n L F G R ∧
    SequenceWitness_d ω G c Q ∧ PairWitness_d ω n c d p ∧ PairWitness_d ω d r e q

def pprogramCheck_m {k} (T ω n L F r e G c d R Q p q : Term k) : Formula 1 k :=
  .conj (.mem c ω) <| .conj (.mem d ω) <| .conj (.mem r L) <|
    .conj (prowsWitness_m T ω n L F G R) <| .conj (sequenceWitness_m ω G c Q) <|
      .conj (pairWitness_m ω n c d p) (pairWitness_m ω d r e q)
derive_free_closed pprogramCheck_m

theorem pprogramCheck_delta_l {k} (T ω n L F r e G c d R Q p q : Term k) :
    (pprogramCheck_m T ω n L F r e G c d R Q p q).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (prowsWitness_delta_l ..)
    (.conj (sequenceWitness_delta_l ..) (.conj (pairWitness_delta_l ..) (pairWitness_delta_l ..))))))

theorem pprogramCheck_sat_l (hKP : M.Models KP) {k} (ρ : Env M k) (T ω n L F r e G c d R Q p q : Term k) :
    Formula.satisfies ρ (pprogramCheck_m T ω n L F r e G c d R Q p q) ↔
      PProgramCheck_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (r.eval ρ) (e.eval ρ)
        (G.eval ρ) (c.eval ρ) (d.eval ρ) (R.eval ρ) (Q.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [pprogramCheck_m,PProgramCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    prowsWitness_sat_l hKP,sequenceWitness_sat_l hKP,pairWitness_sat_l hKP]

theorem pprogramCheck_sound_l (hZF : M.Models ZF) {T ω n L F r e G c d R Q p q : M.Domain}
    (hω : M.IsOmega ω) (cert : PProgramCheck_d T ω n L F r e G c d R Q p q) :
    PBoundedFormula_d T ω n L F ∧ ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e := by
  obtain ⟨_,_,hr,⟨V,_,rowsCert⟩,⟨m,_,b,_,z,_,s,_,H,_,V',_,p',_,seqCert⟩,pair1,pair2⟩ := cert
  obtain ⟨valid,rows⟩ := prowsNumberCheck_sound_l hZF rowsCert
  have seq := (sequenceCheck_sound_l hZF hω seqCert).2
  have ff := fn0_function_l (ZF.modelsKP hZF) valid.graph
  exact ⟨valid,valid.variables,valid.finite,hr,⟨valid.ordinal,ff.1,ff.2.1⟩,G,c,d,rows,seq,
    pairWitness_sound_l hZF pair1,pairWitness_sound_l hZF pair2⟩

theorem pprogramCheck_exists_l (hZF : M.Models ZF) {T ω n L F r e : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e) :
    ∃ G c d R Q p q, PProgramCheck_d T ω n L F r e G c d R Q p q := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨_,_,hr,_,G,c,d,rows,seq,pair1,pair2⟩ := code
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  have hd := oc_pair_natural_l I hZF hω valid.variables hc pair1
  have hrω := hω.transitive hZF L valid.finite r hr
  obtain ⟨V,rowsCert⟩ := prowsNumberCheck_exists_l hZF hω valid rows
  obtain ⟨R,hR⟩ := finiteTruth_cover_l hKP [V]
  have input : NaturalSequence_d ω G := ⟨L,valid.finite,fn0_of_function_l hKP rows.1⟩
  obtain ⟨m,b,z,s,H,V',p',seqCert⟩ := sequenceCheck_exists_l hZF hω input seq
  obtain ⟨Q,hQ⟩ := finiteTruth_cover_l hKP [m,b,z,s,H,V',p']
  obtain ⟨p,pcert⟩ := pairWitness_exists_l hZF hω valid.variables hc pair1
  obtain ⟨q,qcert⟩ := pairWitness_exists_l hZF hω hd hrω pair2
  exact ⟨G,c,d,R,Q,p,q,hc,hd,hr,⟨V,hR V (by simp),rowsCert⟩,
    ⟨m,hQ m (by simp),b,hQ b (by simp),z,hQ z (by simp),s,hQ s (by simp),H,hQ H (by simp),
      V',hQ V' (by simp),p',hQ p' (by simp),seqCert⟩,pcert,qcert⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
