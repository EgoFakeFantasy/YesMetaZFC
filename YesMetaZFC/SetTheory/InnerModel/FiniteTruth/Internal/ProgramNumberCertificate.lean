import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SequenceSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedRowsSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumber

/-! # 原合法程序自然数编号的完整有界证书

保留原编号列、原序列码及两次末尾规范配对；原程序图和给定根不变。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def RowsWitness_d (T ω n L F G R : M.Domain) : Prop := ∃ V, M.mem V R ∧ RowsNumberCheck_d T ω n L F G V

def rowsWitness_m {d} (T ω n L F G R : Term d) : Formula 1 d :=
  Formula.existsMem R (rowsNumberCheck_m T.weaken ω.weaken n.weaken L.weaken F.weaken G.weaken .newest)
derive_free_closed rowsWitness_m

theorem rowsWitness_delta_l {d} (T ω n L F G R : Term d) : (rowsWitness_m T ω n L F G R).IsDelta0 :=
  .existsMem _ (rowsNumberCheck_delta_l ..)

theorem rowsWitness_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n L F G R : Term d) :
    Formula.satisfies ρ (rowsWitness_m T ω n L F G R) ↔
      RowsWitness_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (G.eval ρ) (R.eval ρ) := by
  simp only [rowsWitness_m,RowsWitness_d,Formula.satisfies_existsMem_iff,rowsNumberCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def SequenceWitness_d (ω F c Q : M.Domain) : Prop :=
  ∃ n, M.mem n Q ∧ ∃ b, M.mem b Q ∧ ∃ e, M.mem e Q ∧ ∃ s, M.mem s Q ∧
    ∃ H, M.mem H Q ∧ ∃ V, M.mem V Q ∧ ∃ p, M.mem p Q ∧ SequenceCheck_d ω F c n b e s H V p

def sequenceWitness_m {d} (ω F c Q : Term d) : Formula 1 d :=
  Formula.existsMem Q <| Formula.existsMem Q.weaken <| Formula.existsMem Q.weaken.weaken <|
    Formula.existsMem Q.weaken.weaken.weaken <| Formula.existsMem Q.weaken.weaken.weaken.weaken <|
      Formula.existsMem Q.weaken.weaken.weaken.weaken.weaken <| Formula.existsMem Q.weaken.weaken.weaken.weaken.weaken.weaken <|
        sequenceCheck_m ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          F.weaken.weaken.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed sequenceWitness_m

theorem sequenceWitness_delta_l {d} (ω F c Q : Term d) : (sequenceWitness_m ω F c Q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (sequenceCheck_delta_l ..)))))))

theorem sequenceWitness_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω F c Q : Term d) :
    Formula.satisfies ρ (sequenceWitness_m ω F c Q) ↔ SequenceWitness_d (ω.eval ρ) (F.eval ρ) (c.eval ρ) (Q.eval ρ) := by
  simp only [sequenceWitness_m,SequenceWitness_d,Formula.satisfies_existsMem_iff,sequenceCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def ProgramCheck_d (T ω n L F r e G c d R Q p q : M.Domain) : Prop :=
  M.mem c ω ∧ M.mem d ω ∧ M.mem r L ∧ RowsWitness_d T ω n L F G R ∧
    SequenceWitness_d ω G c Q ∧ PairWitness_d ω n c d p ∧ PairWitness_d ω d r e q

def programCheck_m {k} (T ω n L F r e G c d R Q p q : Term k) : Formula 1 k :=
  .conj (.mem c ω) <| .conj (.mem d ω) <| .conj (.mem r L) <|
    .conj (rowsWitness_m T ω n L F G R) <| .conj (sequenceWitness_m ω G c Q) <|
      .conj (pairWitness_m ω n c d p) (pairWitness_m ω d r e q)
derive_free_closed programCheck_m

theorem programCheck_delta_l {k} (T ω n L F r e G c d R Q p q : Term k) :
    (programCheck_m T ω n L F r e G c d R Q p q).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (rowsWitness_delta_l ..)
    (.conj (sequenceWitness_delta_l ..) (.conj (pairWitness_delta_l ..) (pairWitness_delta_l ..))))))

theorem programCheck_sat_l (hKP : M.Models KP) {k} (ρ : Env M k) (T ω n L F r e G c d R Q p q : Term k) :
    Formula.satisfies ρ (programCheck_m T ω n L F r e G c d R Q p q) ↔
      ProgramCheck_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (r.eval ρ) (e.eval ρ)
        (G.eval ρ) (c.eval ρ) (d.eval ρ) (R.eval ρ) (Q.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [programCheck_m,ProgramCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    rowsWitness_sat_l hKP,sequenceWitness_sat_l hKP,pairWitness_sat_l hKP]

theorem programCheck_sound_l (hZF : M.Models ZF) {T ω n L F r e G c d R Q p q : M.Domain}
    (hω : M.IsOmega ω) (cert : ProgramCheck_d T ω n L F r e G c d R Q p q) :
    BoundedFormula_d T ω n L F ∧ ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e := by
  obtain ⟨_,_,hr,⟨V,_,rowsCert⟩,⟨m,_,b,_,z,_,s,_,H,_,V',_,p',_,seqCert⟩,pair1,pair2⟩ := cert
  obtain ⟨valid,rows⟩ := rowsNumberCheck_sound_l hZF rowsCert
  have seq := (sequenceCheck_sound_l hZF hω seqCert).2
  have ff := fn0_function_l (ZF.modelsKP hZF) valid.graph
  exact ⟨valid,valid.variables,valid.finite,hr,⟨valid.ordinal,ff.1,ff.2.1⟩,G,c,d,rows,seq,
    pairWitness_sound_l hZF pair1,pairWitness_sound_l hZF pair2⟩

theorem programCheck_exists_l (hZF : M.Models ZF) {T ω n L F r e : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e) :
    ∃ G c d R Q p q, ProgramCheck_d T ω n L F r e G c d R Q p q := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨_,_,hr,_,G,c,d,rows,seq,pair1,pair2⟩ := code
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  have hd := oc_pair_natural_l I hZF hω valid.variables hc pair1
  have hrω := hω.transitive hZF L valid.finite r hr
  obtain ⟨V,rowsCert⟩ := rowsNumberCheck_exists_l hZF hω valid rows
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
