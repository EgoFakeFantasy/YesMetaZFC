import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceCertificateExistence
import YesMetaZFC.SetTheory.KP.Sigma1

/-! # 完整内部有限赋值空间的实际 Σ₁ 正规形

输入是内部有限变量域 n，输出是完整赋值空间 E。见证集合只需包含四个证书对象；
其矩阵为实际 Δ₀。在给定真实内部 ω 且 n∈ω 时，与原完整函数空间规格等价。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem assignmentSpaceCert_for_space_l (hZF : M.Models ZF) {ω n X E : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω)
    (full : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X) :
    ∃ e s Z S, AssignmentSpaceCert_d ω n X e s Z S E := by
  obtain ⟨e, s, Z, S, A, cert⟩ := assignmentSpaceCert_exists_l hZF hω hn X
  have ha := assignmentSpaceCert_sound_l hZF hω cert
  have eq := hZF.1.eq_of_same_members A E (fun f => (ha f).trans (full f).symm)
  exact ⟨e, s, Z, S, eq ▸ cert⟩

/-- 参数槽为 X、ω，输入为 n，输出为 E。 -/
def assignmentSpace_s : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <|
        assignmentSpaceCert_m (.bound 8) (.bound 6) (.bound 7) (.bound 3) (.bound 2) (.bound 1) .newest (.bound 5)
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (assignmentSpaceCert_delta_l ..)))) }

theorem assignmentSpace_matrix_sat_l (hE : Extensional M) (ρ : Env M 2) (n E w : M.Domain) :
    Formula.satisfies (((ρ.push n).push E).push w) assignmentSpace_s.matrix.body ↔
      ∃ e, M.mem e w ∧ ∃ s, M.mem s w ∧ ∃ Z, M.mem Z w ∧ ∃ S, M.mem S w ∧
        AssignmentSpaceCert_d (ρ.bound 1) n (ρ.bound 0) e s Z S E := by
  simp only [assignmentSpace_s, Formula.satisfies_existsMem_iff, assignmentSpaceCert_sat_l hE]
  rfl

theorem assignmentSpace_sat_l (hKP : M.Models KP) (ρ : Env M 2) (n E : M.Domain) :
    assignmentSpace_s.schema.denote ρ n E ↔ ∃ e s Z S, AssignmentSpaceCert_d (ρ.bound 1) n (ρ.bound 0) e s Z S E := by
  rw [S1_binary.sat_l]
  simp only [assignmentSpace_matrix_sat_l hKP.1]
  constructor
  · rintro ⟨w, e, _, s, _, Z, _, S, _, cert⟩
    exact ⟨e,s,Z,S,cert⟩
  · rintro ⟨e,s,Z,S,cert⟩
    obtain ⟨P,hP⟩ := KP.exists_pair hKP e s
    obtain ⟨Q,hQ⟩ := KP.exists_pair hKP Z S
    obtain ⟨w,hw⟩ := KP.exists_unionOfTwo hKP P Q
    exact ⟨w,e,(hw e).mpr (Or.inl ((hP e).mpr (Or.inl rfl))),
      s,(hw s).mpr (Or.inl ((hP s).mpr (Or.inr rfl))),
      Z,(hw Z).mpr (Or.inr ((hQ Z).mpr (Or.inl rfl))),
      S,(hw S).mpr (Or.inr ((hQ S).mpr (Or.inr rfl))),cert⟩

/-- 原完整函数空间的规格在内部有限输入上具有已核验的 Σ₁ 正规形。 -/
theorem assignmentSpace_sigma1_l (hZF : M.Models ZF) (ρ : Env M 2) {n E : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hn : M.mem n (ρ.bound 1)) :
    assignmentSpace_s.schema.denote ρ n E ↔
      M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n (ρ.bound 0) :=
  (assignmentSpace_sat_l (ZF.modelsKP hZF) ρ n E).trans
    ⟨fun ⟨_,_,_,_,cert⟩ => assignmentSpaceCert_sound_l hZF hω cert,
      assignmentSpaceCert_for_space_l hZF hω hn⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
