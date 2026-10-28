import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixInput
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedPredicateExtension

/-! # 固定普通参数前缀上的同一原索引查询函数 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def prefixIndexedWitness_s : S1_binary 3 := prefixInput_s.comp extendedIndexedWitness_s

theorem prefixIndexedWitness_sat_l (hZF : M.Models ZF) (ρ : Env M 3) (input y : M.Domain) :
    prefixIndexedWitness_s.schema.denote ρ input y ↔
      ∃ packet, PrefixInput_d (ρ.bound 1) (ρ.bound 2) input packet ∧
        indexedPredicateWitness_s.schema.denote (extendedIndexedWitness_env_l ρ) packet y := by
  simp only [prefixIndexedWitness_s,S1_binary.comp_sat_l (ZF.modelsKP hZF),
    prefixInput_sat_l (ZF.modelsKP hZF),extendedIndexedWitness_sat_l]

theorem prefixIndexedWitness_unique_l (hZF : M.Models ZF) (ρ : Env M 3) {input y t : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (left : prefixIndexedWitness_s.schema.denote ρ input y)
    (right : prefixIndexedWitness_s.schema.denote ρ input t) : y = t := by
  obtain ⟨packet,normal,chosen⟩ := (prefixIndexedWitness_sat_l hZF ρ input y).mp left
  obtain ⟨other,normal',chosen'⟩ := (prefixIndexedWitness_sat_l hZF ρ input t).mp right
  have eq := prefixInput_unique_l hZF ρ hω
    ((prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mpr normal)
    ((prefixInput_sat_l (ZF.modelsKP hZF) ρ input other).mpr normal')
  subst other
  exact indexedPredicateWitness_unique_l hZF (extendedIndexedWitness_env_l ρ) hω chosen chosen'

theorem jh_prefixIndexedWitness_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 3) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hPC : M.mem (ρ.bound 2) C)
    (hinC : M.mem input C) :
    Within_d prefixIndexedWitness_s ρ input y C ↔
      ∃ packet, M.mem packet C ∧ PrefixInput_d (ρ.bound 1) (ρ.bound 2) input packet ∧
        Within_d indexedPredicateWitness_s (extendedIndexedWitness_env_l ρ) packet y C := by
  have comp := within_comp_cover_l (ZF.modelsKP hZF) (jh_value_transitive_l (ZF.models_kpi_l hZF) h)
    (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC prefixInput_s extendedIndexedWitness_s ρ input y
  constructor
  · intro hit
    obtain ⟨packet,hpC,normal,chosen⟩ := comp.mp hit
    exact ⟨packet,hpC,(prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mp (within_toSchema_l _ _ normal),
      (extendedIndexedWitness_within_l ρ packet y C).mp chosen⟩
  · rintro ⟨packet,hpC,normal,chosen⟩
    exact comp.mpr ⟨packet,hpC,(jh_prefixInput_within_l hZF hα h ρ input packet hω hωC hPC hinC).mpr normal,
      (extendedIndexedWitness_within_l ρ packet y C).mpr chosen⟩

theorem prefixInput_predicate_l : PredicateDelta0 (3 : Fin 6) prefixInput_s.matrix.body := by
  apply predicateUseCheck_sound_l prefixInput_s.matrix.delta0 (3 : Fin 6)
  rfl

theorem prefixIndexedWitness_predicate_l : PredicateDelta0 (3 : Fin 6) prefixIndexedWitness_s.matrix.body :=
  comp_predicate_l prefixInput_s extendedIndexedWitness_s prefixInput_predicate_l extendedIndexedWitness_predicate_l

theorem prefixIndexedWitness_sigma1_l : prefixIndexedWitness_s.schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
