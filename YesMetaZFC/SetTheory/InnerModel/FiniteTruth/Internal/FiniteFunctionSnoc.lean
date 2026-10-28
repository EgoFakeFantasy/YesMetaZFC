import YesMetaZFC.SetTheory.Ord.Natural

/-! # 内部有限函数图的追加

追加规格在原集合成员关系上陈述，长度是模型对象，允许非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project

universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}

def Snoc_d (I : 𝒞.Interpretation M) (f n x g : M.Domain) : Prop :=
  ∀ p, M.mem p g ↔ M.mem p f ∨ I.Codes p n x

theorem snoc_iff_entries_l (I : 𝒞.Interpretation M) {f n x g : M.Domain}
    (hf : M.IsSetRelation I f) :
    Snoc_d I f n x g ↔ M.IsSetRelation I g ∧
      ∀ i v, M.PairMember I i v g ↔ M.PairMember I i v f ∨ (i = n ∧ v = x) := by
  constructor
  · intro h
    refine ⟨fun p hp => ((h p).mp hp).elim (hf p) (fun hc => ⟨n, x, hc⟩), ?_⟩
    intro i v
    constructor
    · rintro ⟨p, hp, hpg⟩
      exact ((h p).mp hpg).elim (fun hpf => Or.inl ⟨p, hp, hpf⟩)
        (fun hpn => Or.inr (I.injective hp hpn))
    · rintro (⟨p, hp, hpf⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, hp, (h p).mpr (Or.inl hpf)⟩
      · obtain ⟨p, hp⟩ := I.total i v
        exact ⟨p, hp, (h p).mpr (Or.inr hp)⟩
  · rintro ⟨hg, he⟩ p
    constructor
    · intro hp
      obtain ⟨i, v, hpi⟩ := hg p hp
      rcases (he i v).mp ⟨p, hpi, hp⟩ with ⟨q, hq, hqf⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ((I.unique hpi hq).symm ▸ hqf)
      · exact Or.inr hpi
    · rintro (hpf | hpn)
      · obtain ⟨i, v, hpi⟩ := hf p hpf
        obtain ⟨q, hq, hqg⟩ := (he i v).mpr (Or.inl ⟨p, hpi, hpf⟩)
        exact (I.unique hpi hq).symm ▸ hqg
      · obtain ⟨q, hq, hqg⟩ := (he n x).mpr (Or.inr ⟨rfl, rfl⟩)
        exact (I.unique hpn hq).symm ▸ hqg

/-- 满足追加方程的图恰有给定后继定义域，且值仍在原字母表内。 -/
theorem Snoc_d.function_l (I : 𝒞.Interpretation M) (hKP : M.Models KP)
    {f n s X x g : M.Domain} (hn : M.IsOrdinal n) (hs : M.IsOrdinal s)
    (hns : M.SuccessorOf s n) (hf : M.IsSetFunctionFromTo I f n X)
    (hx : M.mem x X) (hg : Snoc_d I f n x g) : M.IsSetFunctionFromTo I g s X := by
  obtain ⟨A, hA, he⟩ := Structure.IsSequenceOfLength.exists_append hKP I
    (show M.IsSequenceOfLength I f n from ⟨hn, hf.1, hf.2.1⟩) hs hns (value := x)
  obtain ⟨hgr, hge⟩ := (snoc_iff_entries_l I hf.1.1).mp hg
  have eq := hgr.eq_of_pairMember_iff hKP.1 hA.2.1.1 (fun i v => (hge i v).trans (he i v).symm)
  subst g
  refine ⟨hA.2.1, hA.2.2, ?_⟩
  intro i hi
  obtain ⟨v, hv⟩ := (hA.2.2 i).mp hi
  exact ⟨v, ((he i v).mp hv).elim (hf.output_mem_of_pairMember) (fun h => h.2 ▸ hx), hv⟩

/-- 任意后继定义域的函数都分解成前缀和末项，完整保留原图。 -/
theorem function_snoc_exists_l (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {g n s X : M.Domain} (hns : M.SuccessorOf s n) (hg : M.IsSetFunctionFromTo I g s X) :
    ∃ f x, M.IsSetFunctionFromTo I f n X ∧ M.mem x X ∧ Snoc_d I f n x g := by
  obtain ⟨f, hfg⟩ := ZF.exists_restriction hZF I g n
  have hsub : M.MemberSubset n s := fun i hi => (hns i).mpr (Or.inl hi)
  have hfn := hfg.isSetFunction hg.1
  have hfd := hfg.isDomainOf hg.2.1 hsub
  have hf : M.IsSetFunctionFromTo I f n X := by
    refine ⟨hfn, hfd, ?_⟩
    intro i hi
    obtain ⟨v, hvX, hv⟩ := hg.2.2 i (hsub i hi)
    exact ⟨v, hvX, (hfg.2 i v).mpr ⟨hi, hv⟩⟩
  obtain ⟨x, hxX, hx⟩ := hg.2.2 n ((hns n).mpr (Or.inr (fun _ => Iff.rfl)))
  refine ⟨f, x, hf, hxX, (snoc_iff_entries_l I hfn.1).mpr ⟨hg.1.1, ?_⟩⟩
  intro i v
  constructor
  · intro hv
    rcases (hns i).mp (hg.input_mem_of_pairMember hv) with hi | he
    · exact Or.inl ((hfg.2 i v).mpr ⟨hi, hv⟩)
    · have eq := hZF.1.eq_of_same_members i n he
      subst i
      exact Or.inr ⟨rfl, hg.1.2 n v x hv hx⟩
  · rintro (hv | ⟨rfl, rfl⟩)
    · exact ((hfg.2 i v).mp hv).2
    · exact hx

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
