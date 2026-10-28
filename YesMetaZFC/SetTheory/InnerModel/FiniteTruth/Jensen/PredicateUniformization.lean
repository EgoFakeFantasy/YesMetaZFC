import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LocalUniformizationSyntax

/-! # 同一原规范选择器的局部定义域、正确性与单值性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_canonicalPick_within_sound_l (hM : M.Models KPi) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) {n} (φ : S1_binary n)
    (ρ : Env M n) {x y : M.Domain} (selected : Within_d (canonicalPick_s φ) ρ x y C) :
    M.mem y C ∧ Within_d φ ρ x y C := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have rud := jh_value_closed_l hM hα hC
  have trans := jh_value_transitive_l hM hC
  have witness := selected
  obtain ⟨B,hBC,_⟩ := witness
  obtain ⟨q,hqC,leastHit,projectionHit⟩ := (within_comp_cover_l hKP trans rud hBC
    (leastWitness_s (pairedMatrix φ)) (S1_binary.of_delta0 (firstProjection n)) ρ x y).mp selected
  have least := (leastWitness_sat_l hM (pairedMatrix φ) ρ x q).mp (within_toSchema_l _ _ leastHit)
  obtain ⟨w,coords⟩ := (firstProjection_sat_l hKP.1 ρ q y).mp
    ((S1_binary.of_delta0_sat_l (firstProjection n) ρ q y).mp (within_toSchema_l _ _ projectionHit))
  obtain ⟨z,v,other,value⟩ := (pairedMatrix_sat_l hKP.1 φ ρ x q).mp least.2.1
  obtain ⟨rfl,rfl⟩ := kpair_injective_l M other coords
  have bounds := po_pair_bound_l trans hqC coords
  exact ⟨bounds.1,v,bounds.2,value⟩

theorem canonicalPick_within_unique_l (hM : M.Models KPi) {n} (φ : S1_binary n)
    (ρ : Env M n) {C x y z : M.Domain}
    (first : Within_d (canonicalPick_s φ) ρ x y C) (second : Within_d (canonicalPick_s φ) ρ x z C) : y = z :=
  canonicalPick_unique_l hM φ ρ ((canonicalPick_sat_l hM φ ρ x y).mp (within_toSchema_l _ _ first))
    ((canonicalPick_sat_l hM φ ρ x z).mp (within_toSchema_l _ _ second))

theorem jh_canonicalPick_uniformizes_l (hM : M.Models KPi) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) {n} (φ : S1_binary n) (ρ : Env M n) :
    LocalUniformizes_d φ (canonicalPick_s φ) ρ C := by
  intro x _
  constructor
  · constructor
    · intro existsWitness
      obtain ⟨z,hzC,selected,_,_⟩ := jh_canonicalPick_within_function_l hM hα hC φ ρ x existsWitness
      exact ⟨z,hzC,selected⟩
    · rintro ⟨y,hyC,selected⟩
      exact ⟨y,hyC,(jh_canonicalPick_within_sound_l hM hα hC φ ρ selected).2⟩
  · intro y _ selected
    exact ⟨(jh_canonicalPick_within_sound_l hM hα hC φ ρ selected).2,
      fun z _ other => canonicalPick_within_unique_l hM φ ρ other selected⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
