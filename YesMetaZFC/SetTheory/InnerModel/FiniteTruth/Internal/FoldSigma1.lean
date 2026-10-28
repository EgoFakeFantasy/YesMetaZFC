import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldCertificateExistence

/-! # 原规范有限折叠的实际 Σ₁ 图

参数为 n、ω；输入原自然数列 F，输出原 Oc_fold 的数值。
完整历史及全部逐步配对证书同时存在量化，涵盖全部内部有限长度。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def naturalFold_s : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <|
        foldCheck_m (.bound 8) (.bound 6) (.bound 7) (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (foldCheck_delta_l ..)))) }

theorem naturalFold_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 2) (F c w : M.Domain) :
    Formula.satisfies (((ρ.push F).push c).push w) naturalFold_s.matrix.body ↔
      ∃ e, M.mem e w ∧ ∃ s, M.mem s w ∧ ∃ H, M.mem H w ∧ ∃ V, M.mem V w ∧
        FoldCheck_d (ρ.bound 1) F (ρ.bound 0) c e s H V := by
  simp only [naturalFold_s,Formula.satisfies_existsMem_iff,foldCheck_sat_l hKP]
  rfl

theorem naturalFold_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (F c : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) :
    naturalFold_s.schema.denote ρ F c ↔ M.mem (ρ.bound 0) (ρ.bound 1) ∧
      Fn0_d (ρ.bound 0) (ρ.bound 1) F ∧ Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F (ρ.bound 0) c := by
  rw [S1_binary.sat_l]
  simp only [naturalFold_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,e,_,s,_,H,_,V,_,cert⟩
    exact ⟨cert.1,cert.2.2.2.1,foldCheck_sound_l hZF hω cert⟩
  · rintro ⟨hn,input,fold⟩
    obtain ⟨e,s,H,V,cert⟩ := foldCheck_exists_l hZF hω hn input fold
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [e,s,H,V]
    exact ⟨w,e,hw e (by simp),s,hw s (by simp),H,hw H (by simp),V,hw V (by simp),cert⟩

theorem naturalFold_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {F c d : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hc : naturalFold_s.schema.denote ρ F c)
    (hd : naturalFold_s.schema.denote ρ F d) : c = d := by
  have cval := (naturalFold_sat_l hZF ρ F c hω).mp hc
  have dval := (naturalFold_sat_l hZF ρ F d hω).mp hd
  exact oc_fold_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (fn0_function_l (ZF.modelsKP hZF) cval.2.1).1 cval.2.2 dval.2.2

/-- 实际完整历史保证输出仍是内部自然数。 -/
theorem naturalFold_output_l (hZF : M.Models ZF) (ρ : Env M 2) {F c : M.Domain}
    (graph : naturalFold_s.schema.denote ρ F c) : M.mem c (ρ.bound 1) := by
  rw [S1_binary.sat_l] at graph
  obtain ⟨w,hw⟩ := graph
  obtain ⟨e,_,s,_,H,_,V,_,cert⟩ := (naturalFold_matrix_sat_l (ZF.modelsKP hZF) ρ F c w).mp hw
  exact (cert.2.2.2.2.1.bound_l cert.2.2.2.2.2.2.2.1).2

theorem naturalFold_total_l (hZF : M.Models ZF) (ρ : Env M 2) (F : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (hn : M.mem (ρ.bound 0) (ρ.bound 1))
    (input : Fn0_d (ρ.bound 0) (ρ.bound 1) F) :
    ∃ c, M.mem c (ρ.bound 1) ∧ naturalFold_s.schema.denote ρ F c := by
  obtain ⟨c,fold⟩ := oc_fold_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (fn0_function_l (ZF.modelsKP hZF) input).1 (hω.members_areOrdinals hZF (ρ.bound 0) hn)
  have graph := (naturalFold_sat_l hZF ρ F c hω).mpr ⟨hn,input,fold⟩
  exact ⟨c,naturalFold_output_l hZF ρ graph,graph⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
