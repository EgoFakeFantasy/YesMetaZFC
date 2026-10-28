import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldSigma1

/-! # 原自然数列编号的完整有界证书

原数码仍是规范配对〈内部长度，原折叠值〉，保留原 Oc_seq 定义。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def NaturalSequence_d (ω F : M.Domain) : Prop := ∃ n, M.mem n ω ∧ Fn0_d n ω F

def naturalSequence_m {d} (ω F : Term d) : Formula 1 d :=
  Formula.existsMem ω (fn0_m .newest ω.weaken F.weaken)
derive_free_closed naturalSequence_m

theorem naturalSequence_delta_l {d} (ω F : Term d) : (naturalSequence_m ω F).IsDelta0 :=
  .existsMem _ (fn0_delta_l ..)

theorem naturalSequence_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F : Term d) :
    Formula.satisfies ρ (naturalSequence_m ω F) ↔ NaturalSequence_d (ω.eval ρ) (F.eval ρ) := by
  simp only [naturalSequence_m,NaturalSequence_d,Formula.satisfies_existsMem_iff,fn0_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

/-- 原序列码的长度与实际自然数值函数图的长度准确一致。 -/
theorem naturalSequence_decompose_l (hZF : M.Models ZF) {ω F c : M.Domain}
    (hω : M.IsOmega ω) (input : NaturalSequence_d ω F)
    (code : Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) ω F c) :
    ∃ n b, M.mem n ω ∧ Fn0_d n ω F ∧ M.mem b ω ∧
      Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n b ∧ Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) n b c := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨m,_,fn⟩ := input
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  obtain ⟨n,b,hn,seq,fold,pair⟩ := code
  have eq := ff.2.1.eq hZF.1 seq.1.2.2
  have fnn : Fn0_d n ω F := eq ▸ fn
  have hb := oc_fold_natural_l I hZF hω n hn F b (oc_seq_prefix_l I seq)
    (fun _ _ _ entry => ff.output_mem_of_pairMember entry) fold
  exact ⟨n,b,hn,fnn,hb,fold,pair⟩

def SequenceCheck_d (ω F c n b e s H V p : M.Domain) : Prop :=
  FoldCheck_d ω F n b e s H V ∧ PairWitness_d ω n b c p

def sequenceCheck_m {d} (ω F c n b e s H V p : Term d) : Formula 1 d :=
  .conj (foldCheck_m ω F n b e s H V) (pairWitness_m ω n b c p)
derive_free_closed sequenceCheck_m

theorem sequenceCheck_delta_l {d} (ω F c n b e s H V p : Term d) :
    (sequenceCheck_m ω F c n b e s H V p).IsDelta0 :=
  .conj (foldCheck_delta_l ..) (pairWitness_delta_l ..)

theorem sequenceCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω F c n b e s H V p : Term d) :
    Formula.satisfies ρ (sequenceCheck_m ω F c n b e s H V p) ↔
      SequenceCheck_d (ω.eval ρ) (F.eval ρ) (c.eval ρ) (n.eval ρ) (b.eval ρ) (e.eval ρ)
        (s.eval ρ) (H.eval ρ) (V.eval ρ) (p.eval ρ) := by
  simp only [sequenceCheck_m,SequenceCheck_d,Formula.satisfies_conj_iff,foldCheck_sat_l hKP,pairWitness_sat_l hKP]

theorem sequenceCheck_sound_l (hZF : M.Models ZF) {ω F c n b e s H V p : M.Domain}
    (hω : M.IsOmega ω) (cert : SequenceCheck_d ω F c n b e s H V p) :
    NaturalSequence_d ω F ∧ Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) ω F c := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hn := cert.1.1
  have fn := cert.1.2.2.2.1
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  have seq : M.IsOrdinalValuedSequence I F n :=
    ⟨⟨hω.members_areOrdinals hZF n hn,ff.1,ff.2.1⟩,
      fun _ _ a entry => hω.members_areOrdinals hZF a (ff.output_mem_of_pairMember entry)⟩
  exact ⟨⟨n,hn,fn⟩,n,b,hn,seq,foldCheck_sound_l hZF hω cert.1,pairWitness_sound_l hZF cert.2⟩

theorem sequenceCheck_exists_l (hZF : M.Models ZF) {ω F c : M.Domain}
    (hω : M.IsOmega ω) (input : NaturalSequence_d ω F)
    (code : Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) ω F c) :
    ∃ n b e s H V p, SequenceCheck_d ω F c n b e s H V p := by
  obtain ⟨n,b,hn,fn,hb,fold,pair⟩ := naturalSequence_decompose_l hZF hω input code
  obtain ⟨e,s,H,V,cert⟩ := foldCheck_exists_l hZF hω hn fn fold
  obtain ⟨p,pcert⟩ := pairWitness_exists_l hZF hω hn hb pair
  exact ⟨n,b,e,s,H,V,p,cert,pcert⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
