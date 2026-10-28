import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthCertificate

/-! # 扩大传递求值域时的一步真值保持

旧赋值仍取值于小域。小域传递性保证有界量词的新值也在小域内；真实更新方程
保证大赋值空间中的候选更新仍是小赋值。全部字段和子行号均为内部对象。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}

theorem function_codomain_mono_l (I : 𝒞.Interpretation M) {n X Y f : M.Domain}
    (sub : M.MemberSubset X Y) (hf : M.IsSetFunctionFromTo I f n X) :
    M.IsSetFunctionFromTo I f n Y := by
  refine ⟨hf.1, hf.2.1, fun i hi => ?_⟩
  obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
  exact ⟨x, sub x hx, hix⟩

theorem functionSpace_inclusion_l (I : 𝒞.Interpretation M) {n X Y E G : M.Domain}
    (sub : M.MemberSubset X Y) (he : M.IsFunctionSpace I E n X) (hg : M.IsFunctionSpace I G n Y) :
    M.MemberSubset E G :=
  fun f hf => (hg f).mpr (function_codomain_mono_l I sub ((he f).mp hf))

/-- 同一合法指令只依赖较早行在旧赋值空间上的真值，故扩大传递域保值。 -/
theorem btruthNode_domain_l (hKP : M.Models KP) {T ω n X Y E G H J r c f : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l hKP) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l hKP) G n Y) (hf : M.mem f E)
    (previous : ∀ i, M.mem i r → ∀ g, M.mem g E → (Bhit_d H i g ↔ Bhit_d J i g))
    (valid : Bnode_d T ω n r c) :
    BtruthNode_d T n X E H c f ↔ BtruthNode_d T n Y G J c f := by
  have ff := (he f).mp hf
  have ffY := function_codomain_mono_l (kp_pair_l hKP) sub ff
  have eg := functionSpace_inclusion_l (kp_pair_l hKP) sub he hg
  rcases valid with valid | valid | valid | valid
  · obtain ⟨i, hi, j, hj, k, hk, hop, _⟩ := valid
    rw [btruthNode_decode_l hKP ⟨0, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨0, by decide⟩ hi hj hk hop]
    constructor
    · rintro ⟨a, ha, b, hb, hia, hjb, hab⟩
      exact ⟨a, sub a ha, b, sub b hb, hia, hjb, hab⟩
    · rintro ⟨a, _, b, _, hia, hjb, hab⟩
      exact ⟨a, ff.output_mem_of_pairMember hia, b, ff.output_mem_of_pairMember hjb, hia, hjb, hab⟩
  · obtain ⟨i, hi, j, hj, k, hk, hop, _⟩ := valid
    rw [btruthNode_decode_l hKP ⟨1, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨1, by decide⟩ hi hj hk hop]
    constructor
    · rintro ⟨a, ha, hia, hja⟩
      exact ⟨a, sub a ha, hia, hja⟩
    · rintro ⟨a, _, hia, hja⟩
      exact ⟨a, ff.output_mem_of_pairMember hia, hia, hja⟩
  · obtain ⟨i, hi, j, hj, k, hk, hop, hir, hjr, _⟩ := valid
    rw [btruthNode_decode_l hKP ⟨2, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨2, by decide⟩ hi hj hk hop]
    simp only [Barg_d, previous i hir f hf, previous j hjr f hf]
  · obtain ⟨i, hi, j, hj, k, hk, hop, hin, _, hkr⟩ := valid
    rw [btruthNode_decode_l hKP ⟨3, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨3, by decide⟩ hi hj hk hop]
    constructor
    · rintro ⟨a, ha, hja, x, hxx, hxa, g, hge, update, hit⟩
      have gf := (he g).mp hge
      have fullUpdate := (bupdate_correct_l hKP ff gf hin hxx).mp update
      have updateY := (bupdate_correct_l hKP ffY
        (function_codomain_mono_l (kp_pair_l hKP) sub gf) hin (sub x hxx)).mpr fullUpdate
      exact ⟨a, sub a ha, hja, x, sub x hxx, hxa, g, eg g hge, updateY,
        (previous k hkr g hge).mp hit⟩
    · rintro ⟨a, _, hja, x, hxY, hxa, g, hgg, update, hit⟩
      have haX := ff.output_mem_of_pairMember hja
      have hxX := hx a haX x hxa
      have fullUpdate := (bupdate_correct_l hKP ffY ((hg g).mp hgg) hin hxY).mp update
      have gf := SetTheory.Internal.Senv_update_d.function_l (kp_pair_l hKP) fullUpdate ff hin hxX
      have hge := (he g).mpr gf
      exact ⟨a, haX, hja, x, hxX, hxa, g, hge,
        (bupdate_correct_l hKP ff gf hin hxX).mpr fullUpdate, (previous k hkr g hge).mpr hit⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
