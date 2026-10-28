import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateDomain

/-! # 相同背景谓词和相同标准索引在嵌套原 J 层中的保值 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_nicePredicateSkolem_up_l (hZF : M.Models ZF) {α β C D : M.Domain}
    (hα : M.IsOrdinal α) (hβ : M.IsOrdinal β) (hC : Jh_value_d α C) (hD : Jh_value_d β D)
    (sub : M.MemberSubset C D) (ρ : Env M 2) {input y : M.Domain}
    (amenable : AmenableSet_d D (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (hit : Within_d nicePredicateSkolem_s ρ input y C) : Within_d nicePredicateSkolem_s ρ input y D := by
  obtain ⟨_,hinC,hyC⟩ := jh_nicePredicateSkolem_domain_l hZF hα hC ρ hω hωC hit
  have selected := within_toSchema_l nicePredicateSkolem_s ρ hit
  obtain ⟨packet,graph,choice⟩ := (nicePredicateSkolem_sat_l hZF ρ input y).mp selected
  have existsD : ∃ packet z, M.mem z D ∧ indexPacket_s.schema.denote ρ input packet ∧
      predicateParameterSkolem_s.schema.denote ρ packet z := ⟨packet,y,sub y hyC,graph,choice⟩
  exact (jh_nicePredicateSkolem_capture_l hZF hβ hD ρ amenable hω (sub _ hωC) (sub _ hinC) existsD selected).2

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
