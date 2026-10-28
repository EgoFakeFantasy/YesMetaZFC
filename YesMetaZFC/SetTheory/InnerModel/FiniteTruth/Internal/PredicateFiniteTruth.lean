import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateCertifiedTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruth

/-! # 赋值空间作为实际有界见证的谓词操作真值

A 是只读背景集合谓词，不进入普通赋值或见证束。E 在原 Δ₀ 矩阵中由完整
空间证书恢复；正负模板只在真实函数赋值上互补。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PFiniteTruthCert_d (positive : Bool) (T A ω n X F L r f e s Z S E V H : M.Domain) : Prop :=
  AssignmentSpaceCert_d ω n X e s Z S E ∧ M.mem f E ∧
    PtruthCheck_d T A n X E F L V H ∧ BtruthAnswer_d positive H r f

def PFiniteTruth_d (positive : Bool) (T A ω n X F L r f : M.Domain) : Prop :=
  ∃ e s Z S E V H, PFiniteTruthCert_d positive T A ω n X F L r f e s Z S E V H

/-- 参数依次为 A、L、F、X、n、ω、T；输入为行号，输出为真实函数赋值。 -/
def pfiniteTruth_s (positive : Bool) : S1_binary 7 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <|
        Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
          Formula.existsMem (.bound 6) <|
            .conj (assignmentSpaceCert_m (.bound 15) (.bound 14) (.bound 13) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)) <|
              .conj (.mem (.bound 8) (.bound 2)) <|
                .conj (ptruthCheck_m (.bound 16) (.bound 10) (.bound 14) (.bound 13) (.bound 2) (.bound 12) (.bound 11) (.bound 1) .newest)
                  (btruthAnswer_m positive .newest (.bound 9) (.bound 8))
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (assignmentSpaceCert_delta_l ..) (.conj (.mem _ _) (.conj (ptruthCheck_delta_l ..) (btruthAnswer_delta_l ..)))))))))) }

def pfiniteTruth_env_l (T A ω n X F L : M.Domain) : Env M 7 :=
  ⟨Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T)))))),fun _ => T⟩

theorem pfiniteTruth_matrix_sat_l (hE : Extensional M) (positive : Bool) (ρ : Env M 7) (r f w : M.Domain) :
    Formula.satisfies (((ρ.push r).push f).push w) (pfiniteTruth_s positive).matrix.body ↔
      ∃ e, M.mem e w ∧ ∃ s, M.mem s w ∧ ∃ Z, M.mem Z w ∧ ∃ S, M.mem S w ∧
        ∃ E, M.mem E w ∧ ∃ V, M.mem V w ∧ ∃ H, M.mem H w ∧
          PFiniteTruthCert_d positive (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4)
            (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) r f e s Z S E V H := by
  simp only [pfiniteTruth_s,PFiniteTruthCert_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    assignmentSpaceCert_sat_l hE,Formula.satisfies_mem_iff,ptruthCheck_sat_l hE,btruthAnswer_sat_l hE]
  rfl

theorem pfiniteTruth_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 7) (r f : M.Domain) :
    (pfiniteTruth_s positive).schema.denote ρ r f ↔
      PFiniteTruth_d positive (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4)
        (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) r f := by
  rw [S1_binary.sat_l]
  simp only [pfiniteTruth_matrix_sat_l hKP.1]
  constructor
  · rintro ⟨w,e,_,s,_,Z,_,S,_,E,_,V,_,H,_,cert⟩
    exact ⟨e,s,Z,S,E,V,H,cert⟩
  · rintro ⟨e,s,Z,S,E,V,H,cert⟩
    obtain ⟨w,hw⟩ := finiteTruth_cover_l hKP [e,s,Z,S,E,V,H]
    exact ⟨w,e,hw e (by simp),s,hw s (by simp),Z,hw Z (by simp),S,hw S (by simp),
      E,hw E (by simp),V,hw V (by simp),H,hw H (by simp),cert⟩

theorem pfiniteTruth_sigma1_l (positive : Bool) : (pfiniteTruth_s positive).schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

theorem pfiniteTruth_space_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X E F L r f : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω)
    (full : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ M.mem f E ∧ PCertifiedTruth_d positive T A n X E F L r f := by
  constructor
  · rintro ⟨e,s,Z,S,Q,V,H,space,hf,truth,answer⟩
    have fq := assignmentSpaceCert_sound_l hZF hω space
    have eq := hZF.1.eq_of_same_members Q E (fun g => (fq g).trans (full g).symm)
    subst Q
    exact ⟨hf,V,H,truth,answer⟩
  · rintro ⟨hf,V,H,truth,answer⟩
    obtain ⟨e,s,Z,S,space⟩ := assignmentSpaceCert_for_space_l hZF hω hn full
    exact ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩

theorem pfiniteTruth_function_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (truth : PFiniteTruth_d positive T A ω n X F L r f) :
    M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X := by
  obtain ⟨_,_,_,_,E,_,_,space,hf,_⟩ := truth
  exact (assignmentSpaceCert_sound_l hZF hω space f).mp hf

theorem pfiniteTruth_complement_l (hZF : M.Models ZF) {T A ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    PFiniteTruth_d false T A ω n X F L r f ↔ ¬ PFiniteTruth_d true T A ω n X F L r f := by
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  have hfE := (full f).mpr hf
  rw [pfiniteTruth_space_l hZF false hω valid.variables full,pfiniteTruth_space_l hZF true hω valid.variables full]
  simpa only [hfE,true_and] using (pcertifiedTruth_complement_l hZF (r := r) (f := f) valid)

theorem pfiniteTruth_trace_l (positive : Bool) {T A B ω n X F L r f : M.Domain}
    (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ PFiniteTruth_d positive T B ω n X F L r f := by
  simp only [PFiniteTruth_d,PFiniteTruthCert_d,ptruthCheck_trace_l trace]

theorem pfiniteTruth_legacy_l (hKP : M.Models KP) (positive : Bool) {T A ω n X F L r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) :
    PFiniteTruth_d positive T A ω n X F L r f ↔ FiniteTruth_d positive T ω n X F L r f := by
  simp only [PFiniteTruth_d,PFiniteTruthCert_d,FiniteTruth_d,FiniteTruthCert_d,ptruthCheck_legacy_l hKP valid]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
