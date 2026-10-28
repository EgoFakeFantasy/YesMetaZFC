import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicatePreservation
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateCertificate

/-! # 同一标准索引函数的原输出投影 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def indexedPredicateWitness_s : S1_binary 2 := nicePredicateSkolem_s.comp (S1_binary.of_delta0 (firstProjection 2))

theorem indexedPredicateWitness_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (input y : M.Domain) :
    indexedPredicateWitness_s.schema.denote ρ input y ↔
      ∃ z, nicePredicateSkolem_s.schema.denote ρ input z ∧ ∃ w, KPair_d M z y w := by
  simp only [indexedPredicateWitness_s,S1_binary.comp_sat_l (ZF.modelsKP hZF),S1_binary.of_delta0_sat_l,
    firstProjection_sat_l hZF.1]

theorem indexedPredicateWitness_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input y t : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (left : indexedPredicateWitness_s.schema.denote ρ input y)
    (right : indexedPredicateWitness_s.schema.denote ρ input t) : y = t := by
  obtain ⟨z,hz,w,pair⟩ := (indexedPredicateWitness_sat_l hZF ρ input y).mp left
  obtain ⟨v,hv,q,pair'⟩ := (indexedPredicateWitness_sat_l hZF ρ input t).mp right
  have eq := nicePredicateSkolem_unique_l hZF ρ hω hz hv
  subst v
  exact (kpair_injective_l M pair pair').1

theorem firstProjection_within_l (hZF : M.Models ZF) (ρ : Env M 2) {C z y w : M.Domain}
    (hzC : M.mem z C) (pair : KPair_d M z y w) :
    Within_d (S1_binary.of_delta0 (firstProjection 2)) ρ z y C :=
  ⟨z,hzC,(S1_binary.of_delta0_matrix_l (firstProjection 2) ρ z y z).mpr
    ((firstProjection_sat_l hZF.1 ρ z y).mpr ⟨w,pair⟩)⟩

theorem jh_indexedPredicateWitness_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (hωC : M.mem (ρ.bound 1) C) :
    Within_d indexedPredicateWitness_s ρ input y C ↔
      ∃ z, M.mem z C ∧ Within_d nicePredicateSkolem_s ρ input z C ∧ ∃ w, KPair_d M z y w := by
  have comp := within_comp_cover_l (ZF.modelsKP hZF) (jh_value_transitive_l (ZF.models_kpi_l hZF) h)
    (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC nicePredicateSkolem_s
    (S1_binary.of_delta0 (firstProjection 2)) ρ input y
  constructor
  · intro hit
    obtain ⟨z,hzC,nice,projection⟩ := comp.mp hit
    have pair := (firstProjection_sat_l hZF.1 ρ z y).mp
      ((S1_binary.of_delta0_sat_l (firstProjection 2) ρ z y).mp (within_toSchema_l _ _ projection))
    exact ⟨z,hzC,nice,pair⟩
  · rintro ⟨z,hzC,nice,w,pair⟩
    exact comp.mpr ⟨z,hzC,nice,firstProjection_within_l hZF ρ hzC pair⟩

theorem jh_indexedPredicateWitness_domain_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (hit : Within_d indexedPredicateWitness_s ρ input y C) :
    NiceInput_d (ρ.bound 1) C input ∧ M.mem input C ∧ M.mem y C := by
  obtain ⟨z,hzC,nice,w,pair⟩ := (jh_indexedPredicateWitness_within_l hZF hα h ρ hωC).mp hit
  obtain ⟨domain,hinC,_⟩ := jh_nicePredicateSkolem_domain_l hZF hα h ρ hω hωC nice
  exact ⟨domain,hinC,(po_pair_bound_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hzC pair).1⟩

theorem jh_indexedPredicateWitness_up_l (hZF : M.Models ZF) {α β C D : M.Domain}
    (hα : M.IsOrdinal α) (hβ : M.IsOrdinal β) (hC : Jh_value_d α C) (hD : Jh_value_d β D)
    (sub : M.MemberSubset C D) (ρ : Env M 2) {input y : M.Domain}
    (amenable : AmenableSet_d D (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (hit : Within_d indexedPredicateWitness_s ρ input y C) : Within_d indexedPredicateWitness_s ρ input y D := by
  obtain ⟨z,hzC,nice,w,pair⟩ := (jh_indexedPredicateWitness_within_l hZF hα hC ρ hωC).mp hit
  exact (jh_indexedPredicateWitness_within_l hZF hβ hD ρ (sub _ hωC)).mpr
    ⟨z,sub _ hzC,jh_nicePredicateSkolem_up_l hZF hα hβ hC hD sub ρ amenable hω hωC nice,w,pair⟩

theorem indexedPredicateWitness_predicate_l : PredicateDelta0 (3 : Fin 5) indexedPredicateWitness_s.matrix.body :=
  comp_predicate_l nicePredicateSkolem_s (S1_binary.of_delta0 (firstProjection 2)) nicePredicateSkolem_predicate_l
    (of_delta0_predicate_l (firstProjection 2) (firstProjection_predicate_l 1))

theorem indexedPredicateWitness_sigma1_l : indexedPredicateWitness_s.schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
