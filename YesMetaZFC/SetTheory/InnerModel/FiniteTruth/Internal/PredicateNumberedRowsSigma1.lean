import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNumberedRowsCertificate

/-! # 原逐行编号的实际 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 参数槽依次为 L、n、ω、T；输入原程序 F，输出原编号列 G。 -/
def prowsCode_s : S1_binary 4 where
  matrix := {
    body := Formula.existsMem .newest (prowsNumberCheck_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
    delta0 := .existsMem _ (prowsNumberCheck_delta_l ..) }

theorem prowsCode_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 4) (F G w : M.Domain) :
    Formula.satisfies (((ρ.push F).push G).push w) prowsCode_s.matrix.body ↔
      ∃ V, M.mem V w ∧ PRowsNumberCheck_d (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) F G V := by
  simp only [prowsCode_s,Formula.satisfies_existsMem_iff,prowsNumberCheck_sat_l hKP]
  rfl

theorem prowsCode_sat_l (hZF : M.Models ZF) (ρ : Env M 4) (F G : M.Domain) (hω : M.IsOmega (ρ.bound 2)) :
    prowsCode_s.schema.denote ρ F G ↔ PBoundedFormula_d (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) F ∧
      NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 2) (ρ.bound 0) F G := by
  rw [S1_binary.sat_l]
  simp only [prowsCode_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,V,_,cert⟩
    exact prowsNumberCheck_sound_l hZF cert
  · rintro ⟨valid,rows⟩
    obtain ⟨V,cert⟩ := prowsNumberCheck_exists_l hZF hω valid rows
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [V]
    exact ⟨w,V,hw V (by simp),cert⟩

theorem prowsCode_unique_l (hZF : M.Models ZF) (ρ : Env M 4) {F G H : M.Domain}
    (hω : M.IsOmega (ρ.bound 2)) (hg : prowsCode_s.schema.denote ρ F G) (hh : prowsCode_s.schema.denote ρ F H) : G = H :=
  ((prowsCode_sat_l hZF ρ F G hω).mp hg).2.unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1
    ((prowsCode_sat_l hZF ρ F H hω).mp hh).2

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
