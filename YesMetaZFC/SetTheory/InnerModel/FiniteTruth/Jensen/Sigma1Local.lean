import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LeastWitness
import YesMetaZFC.SetTheory.KP.Sigma1Matrix
import YesMetaZFC.SetTheory.InnerModel.Separation.Enclosure

/-! # 非可容许层中的 Σ₁ 复合

复合只需把三个已给见证装入一个有限容器；不假设所在结构满足 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

/-- 三个给定对象能被一个集合包含时，原 Σ₁ 复合正规形准确。 -/
theorem s1_comp_sat_of_cover_l
    (cover : ∀ a b c : M.Domain, ∃ T, M.mem a T ∧ M.mem b T ∧ M.mem c T)
    {n} (φ ψ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    (φ.comp ψ).schema.denote ρ x y ↔
      ∃ z, φ.schema.denote ρ x z ∧ ψ.schema.denote ρ z y := by
  rw [S1_binary.sat_l]
  simp only [S1_binary.comp_matrix_l]
  constructor
  · rintro ⟨_, z, _, w, _, v, _, hw, hv⟩
    exact ⟨z, (φ.sat_l ρ x z).mpr ⟨w, hw⟩, (ψ.sat_l ρ z y).mpr ⟨v, hv⟩⟩
  · rintro ⟨z, hz, hy⟩
    obtain ⟨w, hw⟩ := (φ.sat_l ρ x z).mp hz
    obtain ⟨v, hv⟩ := (ψ.sat_l ρ z y).mp hy
    obtain ⟨T, hzT, hwT, hvT⟩ := cover z w v
    exact ⟨T, z, hzT, w, hwT, v, hvT, hw, hv⟩

/-- rud 闭包中的三个对象有同层的有限容器。 -/
theorem rt_triple_cover_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C)
    (hn : Nonempty {x : M.Domain // M.mem x C})
    (a b c : (rt_model_l C hn).Domain) :
    ∃ T : (rt_model_l C hn).Domain,
      (rt_model_l C hn).mem a T ∧ (rt_model_l C hn).mem b T ∧ (rt_model_l C hn).mem c T := by
  obtain ⟨P, hPC, hP⟩ := hC.exists_l hKP .pair a.property b.property b.property
  obtain ⟨T, hTC, hT⟩ := rd_insert_closed_l hKP hC hPC c.property
  exact ⟨⟨T, hTC⟩, (hT a.val).mpr (Or.inl ((hP a.val).mpr (Or.inl rfl))),
    (hT b.val).mpr (Or.inl ((hP b.val).mpr (Or.inr rfl))), (hT c.val).mpr (Or.inr rfl)⟩

/-- 在实际 rud 闭包内部解释复合，无需该层本身满足 KP。 -/
theorem rt_s1_comp_sat_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ ψ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) (x y : (rt_model_l C hn).Domain) :
    (φ.comp ψ).schema.denote ρ x y ↔
      ∃ z, φ.schema.denote ρ x z ∧ ψ.schema.denote ρ z y :=
  s1_comp_sat_of_cover_l (rt_triple_cover_l hKP hC hn) φ ψ ρ x y

/-- 实际 Σ₁ 矩阵的有界性给出传递层与背景间的准确解释。 -/
theorem s1_matrix_local_l {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) (x y w : (rt_model_l C hn).Domain) :
    Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body ↔
      Formula.satisfies ((((image_env_l Subtype.val ρ).push x.val).push y.val).push w.val)
        φ.matrix.body := by
  apply (rt_model_delta_l hc hn φ.matrix.delta0 _).trans
  exact Formula.closed_env_l _ φ.matrix.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
