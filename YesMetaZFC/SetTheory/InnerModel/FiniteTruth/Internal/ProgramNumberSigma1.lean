import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumberCertificate

/-! # 原合法程序编号的实际局部 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 参数槽为 r、L、n、ω、T；输入原程序图 F，输出原自然数编号 e。 -/
def programCode_s : S1_binary 5 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        Formula.existsMem (.bound 6) <|
          programCheck_m (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 9) (.bound 10) (.bound 8)
            (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (programCheck_delta_l ..))))))) }

theorem programCode_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 5) (F e w : M.Domain) :
    Formula.satisfies (((ρ.push F).push e).push w) programCode_s.matrix.body ↔
      ∃ G, M.mem G w ∧ ∃ c, M.mem c w ∧ ∃ d, M.mem d w ∧ ∃ R, M.mem R w ∧
        ∃ Q, M.mem Q w ∧ ∃ p, M.mem p w ∧ ∃ q, M.mem q w ∧
          ProgramCheck_d (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) F (ρ.bound 0) e G c d R Q p q := by
  simp only [programCode_s,Formula.satisfies_existsMem_iff,programCheck_sat_l hKP]
  rfl

theorem programCode_sat_l (hZF : M.Models ZF) (ρ : Env M 5) (F e : M.Domain) (hω : M.IsOmega (ρ.bound 3)) :
    programCode_s.schema.denote ρ F e ↔ BoundedFormula_d (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) F ∧
      ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) F (ρ.bound 0) e := by
  rw [S1_binary.sat_l]
  simp only [programCode_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,G,_,c,_,d,_,R,_,Q,_,p,_,q,_,cert⟩
    exact programCheck_sound_l hZF hω cert
  · rintro ⟨valid,code⟩
    obtain ⟨G,c,d,R,Q,p,q,cert⟩ := programCheck_exists_l hZF hω valid code
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q,p,q]
    exact ⟨w,G,hw G (by simp),c,hw c (by simp),d,hw d (by simp),R,hw R (by simp),
      Q,hw Q (by simp),p,hw p (by simp),q,hw q (by simp),cert⟩

theorem programCode_output_l (hZF : M.Models ZF) (ρ : Env M 5) {F e : M.Domain}
    (hω : M.IsOmega (ρ.bound 3)) (graph : programCode_s.schema.denote ρ F e) : M.mem e (ρ.bound 3) :=
  ((programCode_sat_l hZF ρ F e hω).mp graph).2.natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω

theorem programCode_unique_l (hZF : M.Models ZF) (ρ : Env M 5) {F e f : M.Domain}
    (hω : M.IsOmega (ρ.bound 3)) (he : programCode_s.schema.denote ρ F e)
    (hf : programCode_s.schema.denote ρ F f) : e = f :=
  ((programCode_sat_l hZF ρ F e hω).mp he).2.unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    ((programCode_sat_l hZF ρ F f hω).mp hf).2

theorem programCode_injective_l (hZF : M.Models ZF) (ρ : Env M 5) {F G e : M.Domain}
    (hω : M.IsOmega (ρ.bound 3)) (hf : programCode_s.schema.denote ρ F e)
    (hg : programCode_s.schema.denote ρ G e) : F = G :=
  (((programCode_sat_l hZF ρ F e hω).mp hf).2.injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω
    ((programCode_sat_l hZF ρ G e hω).mp hg).2).2.2.1

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
