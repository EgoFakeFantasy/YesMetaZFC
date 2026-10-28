import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NaturalPairCheck

/-! # 规范自然数配对证书的背景存在性与原图等价 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
universe u
variable {M : SetTheory.Structure.{u}}

theorem natural_pair_bound_l (hZF : M.Models ZF) {ω a b : M.Domain}
    (hω : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω) :
    ∃ n, M.mem n ω ∧ M.mem a n ∧ M.mem b n := by
  have upper {x y : M.Domain} (hy : M.mem y ω) (hxy : x = y ∨ M.mem x y) :
      ∃ n, M.mem n ω ∧ M.mem x n ∧ M.mem y n := by
    obtain ⟨n,hs,hn⟩ := hω.1.2 y hy
    exact ⟨n,hn,hxy.elim (fun eq => eq ▸ hs.predecessor_mem) (fun hx => (hs x).mpr (Or.inl hx)),hs.predecessor_mem⟩
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare a ha b hb with eq | hab | hba
  · exact upper hb (Or.inl (hZF.1.eq_of_same_members a b eq))
  · exact upper hb (Or.inr hab)
  · obtain ⟨n,hn,hbn,han⟩ := upper ha (Or.inr hba)
    exact ⟨n,hn,han,hbn⟩

theorem naturalPairCheck_exists_l (hZF : M.Models ZF) {ω a b c : M.Domain}
    (hω : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω)
    (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c) :
    ∃ n X R Y F p, NaturalPairCheck_d ω a b c n X R Y F p := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨t,p,hpair,old⟩ := pair
  obtain ⟨n,hn,han,hbn⟩ := natural_pair_bound_l hZF hω ha hb
  have hnO := hω.members_areOrdinals hZF n hn
  obtain ⟨X,hX⟩ := ZF.exists_cartesianProduct hZF I n n
  obtain ⟨R,hR,order⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I hnO hX
  have hpX := (hX p).mpr ⟨a,han,b,hbn,hpair⟩
  have fx : Finite_d I ω X := ZF.cartesianSquare_bounded_in_omega hZF I hω hn hX
  obtain ⟨Y,type,_⟩ := ZF.wellOrderType_existsUnique hZF I order
  have yo := type.isOrdinal hZF I order
  obtain ⟨K,hK⟩ := (type.equinumerous hZF I order).symm hZF I
  obtain ⟨m,hm,J,hJ⟩ := fx
  have fy : Finite_d I ω Y := ⟨m,hm,ZF.exists_compositionInjection hZF I hK.1 hJ⟩
  have hy := finite_ordinal_natural_l hZF hω yo fy
  obtain ⟨F,full,range⟩ := type
  have fn : M.IsSetFunctionFromTo I F X Y := by
    refine ⟨full.1,full.2.1,fun q hq => ?_⟩
    obtain ⟨y,hy⟩ := (full.2.1 q).mp hq
    exact ⟨y,(range y).mpr ⟨q,hy⟩,hy⟩
  have collapse : CollapseCheck_d X R Y F := by
    refine ⟨fn0_of_function_l hKP fn,yo.transitive,?_,?_⟩
    · intro y hy
      obtain ⟨q,hqy⟩ := (range y).mp hy
      exact ⟨q,(full.2.1 q).mpr ⟨y,hqy⟩,hqy⟩
    · intro q hq y _ hqy z _
      exact full.2.2.2 q hq y hqy z
  have entry := oc_at_function_l I hZF hnO hR full hpX old
  exact ⟨n,X,R,Y,F,p,hn,han,hbn,hy,hnO,(canonicalOrderCheck_correct_l hKP).mpr hR,hpair,hpX,collapse,entry⟩

/-- 对自然数输入，有界证书准确表达原规范序数配对图。 -/
theorem naturalPairCheck_iff_l (hZF : M.Models ZF) {ω a b c : M.Domain}
    (hω : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω) :
    (∃ n X R Y F p, NaturalPairCheck_d ω a b c n X R Y F p) ↔
      Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c :=
  ⟨fun ⟨_,_,_,_,_,_,cert⟩ => naturalPairCheck_sound_l hZF cert,naturalPairCheck_exists_l hZF hω ha hb⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
