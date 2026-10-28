import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CanonicalOrderCheck
import YesMetaZFC.SetTheory.Card.Finite

/-! # 规范有限配对证书的内部有限界

全部有限性仍由模型内向 n∈ω 的实际单射给出，未用外部有限性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem finite_ordinal_natural_l (hZF : M.Models ZF) {ω a : M.Domain}
    (hω : M.IsOmega ω) (ha : M.IsOrdinal a)
    (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω a) : M.mem a ω := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨n,hn,inj⟩ := finite
  rcases ha.trichotomy hZF.1 (hω.isOrdinal hZF) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) a ω) with eq | h | h
  · exact (ZF.omega_not_le_finite_l I hZF hω n hn (hZF.1.eq_of_same_members a ω eq ▸ inj)).elim
  · exact h
  · obtain ⟨F,hF⟩ := ZF.exists_inclusionInjection hZF I (ha.transitive ω h)
    obtain ⟨G,hG⟩ := inj
    exact (ZF.omega_not_le_finite_l I hZF hω n hn (ZF.exists_compositionInjection hZF I hF hG)).elim

/-- 内部有限集合的实际笛卡尔方块仍内部有限。 -/
theorem finite_square_l (hZF : M.Models ZF) {ω X P : M.Domain}
    (hω : M.IsOmega ω) (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω X)
    (prod : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P X X) :
    Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω P := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨n,hn,F,hF⟩ := finite
  obtain ⟨Q,hQ⟩ := ZF.exists_cartesianProduct hZF I n n
  obtain ⟨G,hG⟩ := ZF.exists_cartesianProductInjection hZF I prod hQ hF hF
  obtain ⟨m,hm,H,hH⟩ := ZF.cartesianSquare_bounded_in_omega hZF I hω hn hQ
  exact ⟨m,hm,ZF.exists_compositionInjection hZF I hG hH⟩

theorem finite_relation_l (hZF : M.Models ZF) {ω X R : M.Domain}
    (hω : M.IsOmega ω) (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω X)
    (bound : RelationBound_d X R) : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨P,hP⟩ := ZF.exists_cartesianProduct hZF I X X
  exact ZF.finite_subset_l I hZF (finite_square_l hZF hω finite hP)
    (fun p hp => (hP p).mpr (bound p hp))

theorem finite_function_graph_l (hZF : M.Models ZF) {ω X Y F : M.Domain}
    (hω : M.IsOmega ω) (fx : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω X)
    (fy : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω Y)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F X Y) :
    Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨D,hD⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) X Y
  have fd := ZF.finite_union_l I hZF hω fx fy hD
  apply finite_relation_l hZF hω fd
  intro p hp
  obtain ⟨a,b,hpair⟩ := fn.1.1 p hp
  have hab : M.PairMember I a b F := ⟨p,hpair,hp⟩
  exact ⟨a,(hD a).mpr (Or.inl (fn.input_mem_of_pairMember hab)),
    b,(hD b).mpr (Or.inr (fn.output_mem_of_pairMember hab)),hpair⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
