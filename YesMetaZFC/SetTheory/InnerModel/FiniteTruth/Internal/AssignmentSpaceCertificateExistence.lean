import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceCertificateSound

/-! # 完整赋值空间有界证书的背景存在性

背景 ZF 收集各个内部前缀的完整函数空间，构造实际表图，再验证所有有界字段。
这里不宣称整张空间表已属于给定小 J 层；其同层预算仍须独立构造。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem assignmentSpaceCert_exists_l (hZF : M.Models ZF) {ω n : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (X : M.Domain) :
    ∃ e s Z S E, AssignmentSpaceCert_d ω n X e s Z S E := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  have hnOrd := hω.members_areOrdinals hZF n hn
  obtain ⟨s, _, hns⟩ := KP.ordinal_successor_l hKP hnOrd
  let ρ : Env M 1 := ⟨fun _ => X, fun _ => X⟩
  let φ : BinarySchema 1 := {
    body := Formula.isFunctionSpace kpair_convention_l .newest (.bound 1) (.bound 2) }
  have sat r A : φ.denote ρ r A ↔ M.IsFunctionSpace I A r X := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_isFunctionSpace_iff I hZF.1]
    rfl
  have total r (_ : M.mem r s) : ∃ A, φ.denote ρ r A := by
    obtain ⟨A, hA⟩ := ZF.exists_functionSpace hZF I r X
    exact ⟨A, (sat r A).mpr hA⟩
  have unique r (_ : M.mem r s) A B (ha : φ.denote ρ r A) (hb : φ.denote ρ r B) : A = B :=
    hZF.1.eq_of_same_members A B (fun f => ((sat r A).mp ha f).trans ((sat r B).mp hb f).symm)
  obtain ⟨Z, hZ⟩ := ZF.exists_functionalImageOn hZF φ ρ s total unique
  obtain ⟨S, hS, entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := s) (target := Z) total unique (fun r A hr ha => (hZ A).mpr ⟨r, hr, ha⟩)
  have full r A (entry : Rd_entry_d r A S) : M.IsFunctionSpace I A r X :=
    (sat r A).mp ((entries r A).mp entry).2
  obtain ⟨E, _, hEn⟩ := hS.2.2 n hns.predecessor_mem
  refine ⟨e, s, Z, S, E, hn, he, hns, fn0_of_function_l hKP hS, hEn, ?_, ?_, ?_⟩
  · exact fun r _ A _ hA f hf => fn0_of_function_l hKP ((full r A hA f).mp hf)
  · intro A _ hA
    have emptyFn : M.IsSetFunctionFromTo I e e X :=
      ⟨(Structure.IsSequenceOfLength.empty I he).2.1,
        (Structure.IsSequenceOfLength.empty I he).2.2, fun i hi => (he i hi).elim⟩
    exact (full e A hA e).mpr emptyFn
  · intro r hr t _ hrt A _ hA B _ hB f hf x hx
    have ff := (full r A hA f).mp hf
    have hrOrd := hω.members_areOrdinals hZF r (hω.transitive hZF n hn r hr)
    have htOrd := KP.successor_isOrdinal hKP hrOrd hrt
    obtain ⟨p, hp⟩ := I.total r x
    obtain ⟨g, hg⟩ := KP.exists_insert hKP f p
    have snoc : Snoc_d I f r x g := fun q => (hg q).trans
      (or_congr Iff.rfl ⟨fun eq => eq.symm ▸ hp, fun hq => I.unique hq hp⟩)
    have gf := snoc.function_l I hKP hrOrd htOrd hrt ff hx
    exact ⟨g, (full t B hB g).mpr gf, (snocCheck_correct_l hKP).mpr snoc⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
