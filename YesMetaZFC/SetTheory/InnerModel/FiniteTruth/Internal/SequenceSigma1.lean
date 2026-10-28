import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SequenceCertificate

/-! # 原内部有限自然数列编号的实际 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def sequenceCode_s : S1_binary 1 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        Formula.existsMem (.bound 6) <|
          sequenceCheck_m (.bound 10) (.bound 9) (.bound 8) (.bound 6) (.bound 5)
            (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (sequenceCheck_delta_l ..))))))) }

theorem sequenceCode_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 1) (F c w : M.Domain) :
    Formula.satisfies (((ρ.push F).push c).push w) sequenceCode_s.matrix.body ↔
      ∃ n, M.mem n w ∧ ∃ b, M.mem b w ∧ ∃ e, M.mem e w ∧ ∃ s, M.mem s w ∧
        ∃ H, M.mem H w ∧ ∃ V, M.mem V w ∧ ∃ p, M.mem p w ∧ SequenceCheck_d (ρ.bound 0) F c n b e s H V p := by
  simp only [sequenceCode_s,Formula.satisfies_existsMem_iff,sequenceCheck_sat_l hKP]
  rfl

theorem sequenceCode_sat_l (hZF : M.Models ZF) (ρ : Env M 1) (F c : M.Domain)
    (hω : M.IsOmega (ρ.bound 0)) :
    sequenceCode_s.schema.denote ρ F c ↔ NaturalSequence_d (ρ.bound 0) F ∧
      Oc_seq_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) F c := by
  rw [S1_binary.sat_l]
  simp only [sequenceCode_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,n,_,b,_,e,_,s,_,H,_,V,_,p,_,cert⟩
    exact sequenceCheck_sound_l hZF hω cert
  · rintro ⟨input,code⟩
    obtain ⟨n,b,e,s,H,V,p,cert⟩ := sequenceCheck_exists_l hZF hω input code
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [n,b,e,s,H,V,p]
    exact ⟨w,n,hw n (by simp),b,hw b (by simp),e,hw e (by simp),s,hw s (by simp),
      H,hw H (by simp),V,hw V (by simp),p,hw p (by simp),cert⟩

theorem sequenceCode_output_l (hZF : M.Models ZF) (ρ : Env M 1) {F c : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (graph : sequenceCode_s.schema.denote ρ F c) : M.mem c (ρ.bound 0) := by
  obtain ⟨⟨_,_,input⟩,code⟩ := (sequenceCode_sat_l hZF ρ F c hω).mp graph
  exact oc_seq_natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω (fn0_function_l (ZF.modelsKP hZF) input) code

theorem sequenceCode_unique_l (hZF : M.Models ZF) (ρ : Env M 1) {F c d : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hc : sequenceCode_s.schema.denote ρ F c)
    (hd : sequenceCode_s.schema.denote ρ F d) : c = d :=
  oc_seq_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    ((sequenceCode_sat_l hZF ρ F c hω).mp hc).2 ((sequenceCode_sat_l hZF ρ F d hω).mp hd).2

theorem sequenceCode_injective_l (hZF : M.Models ZF) (ρ : Env M 1) {F G c : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hf : sequenceCode_s.schema.denote ρ F c)
    (hg : sequenceCode_s.schema.denote ρ G c) : F = G :=
  oc_seq_injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω
    ((sequenceCode_sat_l hZF ρ F c hω).mp hf).2 ((sequenceCode_sat_l hZF ρ G c hω).mp hg).2

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
