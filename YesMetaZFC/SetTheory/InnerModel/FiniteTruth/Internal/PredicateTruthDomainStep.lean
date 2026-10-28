import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomainStep

/-! # 谓词程序在完整赋值空间上的单步传递域运输 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem predicateAtom_domain_l (hKP : M.Models KP) {A n X Y f i : M.Domain}
    (sub : M.MemberSubset X Y) (fn : M.IsSetFunctionFromTo (kp_pair_l hKP) f n X) :
    PredicateAtom_d A X f i ↔ PredicateAtom_d A Y f i := by
  constructor
  · rintro ⟨a,ha,read,hit⟩
    exact ⟨a,sub a ha,read,hit⟩
  · rintro ⟨a,_,read,hit⟩
    exact ⟨a,fn.output_mem_of_pairMember read,read,hit⟩

theorem ptruthNode_domain_l (hKP : M.Models KP) {T A ω n X Y E G H J r c f : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l hKP) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l hKP) G n Y) (hf : M.mem f E)
    (previous : ∀ i, M.mem i r → ∀ g, M.mem g E → (Bhit_d H i g ↔ Bhit_d J i g))
    (valid : Pnode_d T ω n r c) :
    PtruthNode_d T A n X E H c f ↔ PtruthNode_d T A n Y G J c f := by
  rcases valid with old | query
  · exact (ptruthNode_legacy_l hKP old).trans ((btruthNode_domain_l hKP hx sub he hg hf previous old).trans
      (ptruthNode_legacy_l hKP old).symm)
  · obtain ⟨i,hi,j,hj,k,hk,code,_⟩ := query
    exact (ptruthNode_predicate_l hKP hi hj hk code).trans
      ((predicateAtom_domain_l hKP sub ((he f).mp hf)).trans
        (ptruthNode_predicate_l hKP hi hj hk code).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
