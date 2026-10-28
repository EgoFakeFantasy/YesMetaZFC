import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CertifiedTruth

/-! # 内部谓词程序的正负实际 Σ₁ 证书源

参数槽为 A、L、F、E、X、n、T。A 不装入赋值图或证书容器。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PCertifiedTruth_d (positive : Bool) (T A n X E F L r f : M.Domain) : Prop :=
  ∃ Z H, PtruthCheck_d T A n X E F L Z H ∧ BtruthAnswer_d positive H r f

def pcertifiedTruth_s (positive : Bool) : S1_binary 7 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      .conj (ptruthCheck_m (.bound 11) (.bound 5) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 1) .newest)
        (btruthAnswer_m positive .newest (.bound 4) (.bound 3))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (ptruthCheck_delta_l ..) (btruthAnswer_delta_l ..))) }

def pcertifiedTruth_env_l (T A n X E F L : M.Domain) : Env M 7 :=
  ⟨Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (fun _ => T)))))),fun _ => T⟩

theorem pcertifiedTruth_matrix_l (hE : Extensional M) (positive : Bool) (ρ : Env M 7) (r f w : M.Domain) :
    Formula.satisfies (((ρ.push r).push f).push w) (pcertifiedTruth_s positive).matrix.body ↔
      ∃ Z, M.mem Z w ∧ ∃ H, M.mem H w ∧
        PtruthCheck_d (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) Z H ∧
          BtruthAnswer_d positive H r f := by
  simp only [pcertifiedTruth_s,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    ptruthCheck_sat_l hE,btruthAnswer_sat_l hE]
  rfl

theorem pcertifiedTruth_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 7) (r f : M.Domain) :
    (pcertifiedTruth_s positive).schema.denote ρ r f ↔
      PCertifiedTruth_d positive (ρ.bound 6) (ρ.bound 0) (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) r f := by
  rw [S1_binary.sat_l]
  simp only [pcertifiedTruth_matrix_l hKP.1]
  constructor
  · rintro ⟨w,Z,_,H,_,check,answer⟩
    exact ⟨Z,H,check,answer⟩
  · rintro ⟨Z,H,check,answer⟩
    obtain ⟨w,pair⟩ := KP.exists_pair hKP Z H
    exact ⟨w,Z,(pair Z).mpr (Or.inl rfl),H,(pair H).mpr (Or.inr rfl),check,answer⟩

theorem pcertifiedTruth_sigma1_l (positive : Bool) : (pcertifiedTruth_s positive).schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

theorem pcertifiedTruth_value_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X E F L Z H r f : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) (check : PtruthCheck_d T A n X E F L Z H) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ BtruthAnswer_d positive H r f := by
  constructor
  · rintro ⟨W,J,other,answer⟩
    exact ptruthCertificate_unique_l hZF valid other check ▸ answer
  · exact fun answer => ⟨Z,H,check,answer⟩

theorem pcertifiedTruth_complement_l (hZF : M.Models ZF) {T A ω n X E F L r f : M.Domain}
    (valid : PBoundedFormula_d T ω n L F) :
    PCertifiedTruth_d false T A n X E F L r f ↔ ¬ PCertifiedTruth_d true T A n X E F L r f := by
  obtain ⟨Z,H,check⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) valid
  rw [pcertifiedTruth_value_l hZF false valid check,pcertifiedTruth_value_l hZF true valid check]
  rfl

theorem pcertifiedTruth_trace_l (positive : Bool) {T A B n X E F L r f : M.Domain}
    (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ PCertifiedTruth_d positive T B n X E F L r f := by
  simp only [PCertifiedTruth_d,ptruthCheck_trace_l trace]

theorem pcertifiedTruth_legacy_l (hKP : M.Models KP) (positive : Bool) {T A ω n X E F L r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ CertifiedTruth_d positive T n X E F L r f := by
  simp only [PCertifiedTruth_d,CertifiedTruth_d,ptruthCheck_legacy_l hKP valid]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
