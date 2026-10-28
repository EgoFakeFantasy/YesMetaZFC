import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AmenableObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterSkolem

/-! # 同一规范选择器的直接 Within 证书

原初段证书和有限装配不要求源参数属于当前层。
使用同一个 leastWitness_s / canonicalPick_s，不增设选择图。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem leastWitness_matrix_unrestricted_l {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) (x y B : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push B) (leastWitness_s φ).matrix.body ↔
      ∃ I, M.mem I B ∧ ∃ T, M.mem T B ∧
        Formula.satisfies ((((⟨Fin.elim0,ρ.free⟩ : Env M 0).push y).push I).push T)
          js_initial_s.matrix.body ∧ φ.toBinarySchema.denote ρ x y ∧
            ∀ z, M.mem z I → ¬ φ.toBinarySchema.denote ρ x z := by
  simp only [leastWitness_s,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    S1_binary.matrix_sat_l,binary_pred_sat_l,Formula.satisfies_forallMem_iff,Formula.satisfies_neg_iff]
  apply exists_congr
  intro I
  apply and_congr_right
  intro _
  apply exists_congr
  intro T
  apply and_congr_right
  intro _
  apply and_congr
  · exact Formula.closed_env_l _ js_initial_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  · rfl

theorem jh_leastWitness_within_l (hM : M.Models KPi) {α C y : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hyC : M.mem y C)
    {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (x : M.Domain) :
    Within_d (leastWitness_s φ) ρ x y C ↔ LeastWitness_d φ ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have rud := jh_value_closed_l hM hα hC
  have trans := jh_value_transitive_l hM hC
  constructor
  · intro hit
    exact (leastWitness_sat_l hM φ ρ x y).mp (within_toSchema_l _ _ hit)
  · intro least
    obtain ⟨I,hIC,initial⟩ := jh_initial_in_l hM hα hC hyC
    let ζ : Env M 0 := ⟨Fin.elim0,ρ.free⟩
    obtain ⟨T,hTC,cert⟩ := js_initial_cert_in_l hM rud trans
      (js_rep_access_l hM rud (jh_order_rep_l hM hα hC) y hyC) initial ζ
    obtain ⟨B,pair⟩ := KP.exists_pair hKP I T
    have hBC : M.mem B C := rud .pair I T T hIC hTC hTC B pair
    refine ⟨B,hBC,(leastWitness_matrix_unrestricted_l φ ρ x y B).mpr ?_⟩
    exact ⟨I,(pair I).mpr (Or.inl rfl),T,(pair T).mpr (Or.inr rfl),
      (js_initial_matrix_l hKP ζ y I T).mpr cert,least.2.1,
      fun z hz => least.2.2 z ((initial.2 z).mp hz)⟩

theorem jh_leastWitness_within_function_l (hM : M.Models KPi) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) (x : M.Domain)
    (existsWitness : ∃ y, M.mem y C ∧ φ.toBinarySchema.denote ρ x y) :
    ∃ z, M.mem z C ∧ Within_d (leastWitness_s φ) ρ x z C ∧
      ∀ v, (leastWitness_s φ).schema.denote ρ x v → v = z := by
  obtain ⟨y,hyC,good⟩ := existsWitness
  have hyL : L_d y := ⟨α,C,⟨hα,hC⟩,hyC⟩
  obtain ⟨z,least⟩ := leastWitness_exists_l hM φ ρ hyL good
  have hzC : M.mem z C := by
    rcases leastWitness_le_l hM φ ρ least hyL good with eq | lt
    · exact eq ▸ hyC
    · obtain ⟨I,hIC,initial⟩ := jh_initial_in_l hM hα hC hyC
      exact jh_value_transitive_l hM hC I hIC z ((initial.2 z).mpr lt)
  exact ⟨z,hzC,(jh_leastWitness_within_l hM hα hC hzC φ ρ x).mpr least,
    fun v hv => leastWitness_unique_l hM φ ρ ((leastWitness_sat_l hM φ ρ x v).mp hv) least⟩

theorem jh_canonicalPick_within_function_l (hM : M.Models KPi) {α C : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) {n} (φ : S1_binary n)
    (ρ : Env M n) (x : M.Domain)
    (existsWitness : ∃ y, M.mem y C ∧ Within_d φ ρ x y C) :
    ∃ z, M.mem z C ∧ Within_d (canonicalPick_s φ) ρ x z C ∧ Within_d φ ρ x z C ∧
      ∀ v, (canonicalPick_s φ).schema.denote ρ x v → v = z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have rud := jh_value_closed_l hM hα hC
  have trans := jh_value_transitive_l hM hC
  obtain ⟨y,hyC,w,hwC,good⟩ := existsWitness
  obtain ⟨p,pair⟩ := (kp_pair_l hKP).total y w
  have hpC := rud .opair y w w hyC hwC hwC p (rd_opair_value_l hKP.1 pair)
  have paired := (pairedMatrix_sat_l hKP.1 φ ρ x p).mpr ⟨y,w,pair,good⟩
  obtain ⟨q,hqC,hit,_⟩ := jh_leastWitness_within_function_l hM hα hC (pairedMatrix φ) ρ x ⟨p,hpC,paired⟩
  have least := (jh_leastWitness_within_l hM hα hC hqC (pairedMatrix φ) ρ x).mp hit
  obtain ⟨z,v,coords,value⟩ := (pairedMatrix_sat_l hKP.1 φ ρ x q).mp least.2.1
  have bounds := po_pair_bound_l trans hqC coords
  have projection : Within_d (S1_binary.of_delta0 (firstProjection n)) ρ q z C :=
    ⟨q,hqC,(S1_binary.of_delta0_matrix_l (firstProjection n) ρ q z q).mpr
      ((firstProjection_sat_l hKP.1 ρ q z).mpr ⟨v,coords⟩)⟩
  have selected : Within_d (canonicalPick_s φ) ρ x z C :=
    (within_comp_cover_l hKP trans rud hqC (leastWitness_s (pairedMatrix φ))
      (S1_binary.of_delta0 (firstProjection n)) ρ x z).mpr ⟨q,hqC,hit,projection⟩
  refine ⟨z,bounds.1,selected,⟨v,bounds.2,value⟩,?_⟩
  intro t ht
  exact canonicalPick_unique_l hM φ ρ ((canonicalPick_sat_l hM φ ρ x t).mp ht)
    ((canonicalPick_sat_l hM φ ρ x z).mp (within_toSchema_l _ _ selected))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
