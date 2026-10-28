import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NaturalPairSigma1

/-! # 原规范折叠的完整自然数值历史

历史包括零位置及给定根，逐内部索引核验后继配对。恢复原递归时使用
模型内部自然数的零／后继分类，未对外部良基性或标准长度作假设。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure FoldRun_d (I : kpair_convention_l.Interpretation M) (ω F n c e s H : M.Domain) : Prop where
  finite : M.mem n ω
  successor_finite : M.mem s ω
  successor : M.SuccessorOf s n
  input : Fn0_d n ω F
  history : Fn0_d s ω H
  zero : Num_d 0 e
  initial : Rd_entry_d e e H
  final : Rd_entry_d n c H
  step : ∀ r, M.mem r n → ∃ a, M.mem a ω ∧ ∃ b, M.mem b ω ∧
    ∃ t, M.mem t s ∧ ∃ d, M.mem d ω ∧ Rd_entry_d r a F ∧ Rd_entry_d r b H ∧
      M.SuccessorOf t r ∧ Rd_entry_d t d H ∧ Oc_pair_d I b a d

theorem FoldRun_d.sound_l (hZF : M.Models ZF) {ω F n c e s H : M.Domain}
    (hω : M.IsOmega ω) (run : FoldRun_d (kp_pair_l (ZF.modelsKP hZF)) ω F n c e s H) :
    Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n c := by
  classical
  let I := kp_pair_l (ZF.modelsKP hZF)
  have fh := fn0_function_l (ZF.modelsKP hZF) run.history
  have so := hω.members_areOrdinals hZF s run.successor_finite
  have no := hω.members_areOrdinals hZF n run.finite
  have seq : M.IsSequenceOfLength I H s := ⟨so,fh.1,fh.2.1⟩
  have historyRec : M.IsRecursiveSequence I (Oc_step_d I F) H s := by
    refine ⟨seq,?_⟩
    intro k hk y hky
    obtain ⟨P,hP⟩ := ZF.exists_restriction hZF I H k
    have seqP := seq.restriction hk hP
    by_cases nonempty : ∃ z, M.mem z k
    · have hkω := hω.transitive hZF s run.successor_finite k hk
      obtain ⟨r,hrω,hkr⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hkω nonempty
      have hrn : M.mem r n := by
        rcases (run.successor k).mp hk with hkn | eq
        · exact no.transitive k hkn r hkr.predecessor_mem
        · exact (hZF.1.eq_of_same_members k n eq) ▸ hkr.predecessor_mem
      obtain ⟨a,ha,b,hb,t,_,d,_,hra,hrb,ht,htd,pair⟩ := run.step r hrn
      have eq := Structure.SuccessorOf.eq hZF.1 ht hkr
      subst t
      have dy : d = y := fh.1.2 k d y htd hky
      have read : Oc_read_d I F P b a := ⟨k,r,seqP.2.2,hkr,hω.members_areOrdinals hZF r hrω,
        (hP.2 r b).mpr ⟨hkr.predecessor_mem,hrb⟩,hra,
        hω.members_areOrdinals hZF b hb,hω.members_areOrdinals hZF a ha⟩
      exact ⟨P,hP,Or.inl ⟨b,a,read,dy ▸ pair⟩⟩
    · have empty : ∀ z, ¬ M.mem z k := fun z hz => nonempty ⟨z,hz⟩
      have ke : k = e := hZF.1.eq_of_same_members k e (fun z => iff_of_false (empty z) (run.zero z))
      have ye : y = e := fh.1.2 e y e (ke ▸ hky) run.initial
      have noRead : ¬ ∃ b a, Oc_read_d I F P b a := by
        rintro ⟨b,a,m,i,dom,_,_,hib,_⟩
        have eq := dom.eq hZF.1 seqP.2.2
        exact empty i (eq ▸ (dom i).mpr ⟨b,hib⟩)
      exact ⟨P,hP,Or.inr ⟨noRead,fun z hz => run.zero z (ye ▸ hz)⟩⟩
  exact historyRec.recursionValue_of_pairMember run.successor.predecessor_mem run.final

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
