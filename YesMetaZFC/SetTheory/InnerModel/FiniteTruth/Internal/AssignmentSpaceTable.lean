import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceCertificateObjectTheorems

/-! # 完整赋值空间表及其有界证书

空间表是实际序列，每行是对应长度的完整函数空间。先建立同层序列，再由其
真实行性质恢复已有 Δ₀ 证书，避免把背景收集所得的整张表直接当作层内集合。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def SpaceTable_d (I : kpair_convention_l.Interpretation M) (r X S : M.Domain) : Prop :=
  M.IsSequenceOfLength I S r ∧ ∀ i A, M.PairMember I i A S → M.IsFunctionSpace I A i X

def spaceTable_m {d} (r X S : Term d) : Formula 1 d :=
  .conj (Formula.isSequenceOfLength kpair_convention_l S r)
    (.forallE (.forallE (.imp
      (Formula.orderedPairMem kpair_convention_l (.bound 1) .newest S.weaken.weaken)
      (Formula.isFunctionSpace kpair_convention_l .newest (.bound 1) X.weaken.weaken))))
derive_free_closed spaceTable_m

theorem spaceTable_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r X S : Term d) :
    Formula.satisfies ρ (spaceTable_m r X S) ↔ SpaceTable_d (kp_pair_l hKP) (r.eval ρ) (X.eval ρ) (S.eval ρ) := by
  simp only [spaceTable_m, SpaceTable_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isSequenceOfLength_iff (kp_pair_l hKP) hKP.1, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff (kp_pair_l hKP),
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l hKP) hKP.1,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

/-- 满足完整追加方程的实际图保留精确后继长度。 -/
theorem snoc_sequence_l (hKP : M.Models KP) {S r s A K : M.Domain}
    (hs : M.IsOrdinal s) (hrs : M.SuccessorOf s r)
    (seq : M.IsSequenceOfLength (kp_pair_l hKP) S r) (snoc : Snoc_d (kp_pair_l hKP) S r A K) :
    M.IsSequenceOfLength (kp_pair_l hKP) K s := by
  let I := kp_pair_l hKP
  obtain ⟨G, hg, entries⟩ := Structure.IsSequenceOfLength.exists_append hKP I seq hs hrs (value := A)
  obtain ⟨hk, hke⟩ := (snoc_iff_entries_l I seq.2.1.1).mp snoc
  have eq := hk.eq_of_pairMember_iff hKP.1 hg.2.1.1 (fun i a => (hke i a).trans (entries i a).symm)
  exact eq.symm ▸ hg

/-- 真实完整空间表准确恢复已有有界证书。 -/
theorem assignmentSpaceCert_of_table_l (hZF : M.Models ZF) {ω n X e s Z S E : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (he : ∀ p, ¬ M.mem p e) (hns : M.SuccessorOf s n)
    (table : SpaceTable_d (kp_pair_l (ZF.modelsKP hZF)) s X S)
    (range : ∀ A, M.mem A Z ↔ ∃ i, Rd_entry_d i A S) (output : Rd_entry_d n E S) :
    AssignmentSpaceCert_d ω n X e s Z S E := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have fn : Fn0_d s Z S := fn0_of_function_l hKP ⟨table.1.2.1, table.1.2.2, fun r hr => by
    obtain ⟨A, hA⟩ := (table.1.2.2 r).mp hr
    exact ⟨A, (range A).mpr ⟨r,hA⟩,hA⟩⟩
  refine ⟨hn,he,hns,fn,output,?_,?_,?_⟩
  · exact fun r _ A _ hA f hf => fn0_of_function_l hKP ((table.2 r A hA f).mp hf)
  · intro A _ hA
    have emptyFn : M.IsSetFunctionFromTo I e e X :=
      ⟨(Structure.IsSequenceOfLength.empty I he).2.1,
        (Structure.IsSequenceOfLength.empty I he).2.2, fun i hi => (he i hi).elim⟩
    exact (table.2 e A hA e).mpr emptyFn
  · intro r hr t _ hrt A _ hA B _ hB f hf x hx
    have ff := (table.2 r A hA f).mp hf
    have hrOrd := hω.members_areOrdinals hZF r (hω.transitive hZF n hn r hr)
    have htOrd := KP.successor_isOrdinal hKP hrOrd hrt
    obtain ⟨p,hp⟩ := I.total r x
    obtain ⟨g,hg⟩ := KP.exists_insert hKP f p
    have snoc : Snoc_d I f r x g := fun q => (hg q).trans
      (or_congr Iff.rfl ⟨fun eq => eq.symm ▸ hp, fun hq => I.unique hq hp⟩)
    have gf := snoc.function_l I hKP hrOrd htOrd hrt ff hx
    exact ⟨g,(table.2 t B hB g).mpr gf,(snocCheck_correct_l hKP).mpr snoc⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
