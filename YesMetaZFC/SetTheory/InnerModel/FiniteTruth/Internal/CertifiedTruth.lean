import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthCertificate
import YesMetaZFC.SetTheory.KP.Sigma1

/-! # 统一内部有界程序的正负 Σ₁ 真值模板

正负模板使用同一完整历史证书。见证仅为包含历史图和行容器的一个集合；矩阵
实际为 Δ₀。此处解释内部指令，原 Project 公式的编译与语义保持仍须另证。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def BtruthAnswer_d (positive : Bool) (H r f : M.Domain) : Prop :=
  if positive then Bhit_d H r f else ¬ Bhit_d H r f

def btruthAnswer_m (positive : Bool) {d} (H r f : Term d) : Formula 1 d :=
  if positive then bhit_m H r f else .neg (bhit_m H r f)

@[simp] theorem btruthAnswer_closed_l (positive : Bool) {d} (H r f : Term d)
    (hH : H.freeSupport = []) (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (btruthAnswer_m positive H r f).FreeClosed := by
  cases positive <;> simp [btruthAnswer_m, Definitional.Formula.FreeClosed, hH, hr, hf]

theorem btruthAnswer_delta_l (positive : Bool) {d} (H r f : Term d) :
    (btruthAnswer_m positive H r f).IsDelta0 := by
  cases positive
  · exact .neg (bhit_delta_l ..)
  · exact bhit_delta_l ..

theorem btruthAnswer_sat_l (hE : Extensional M) (positive : Bool) {d} (ρ : Env M d) (H r f : Term d) :
    Formula.satisfies ρ (btruthAnswer_m positive H r f) ↔
      BtruthAnswer_d positive (H.eval ρ) (r.eval ρ) (f.eval ρ) := by
  cases positive <;> simp only [btruthAnswer_m, BtruthAnswer_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_neg_iff, bhit_sat_l hE]

/-- 参数槽依次为 L、F、E、X、n、T；输入是行号，输出是赋值。 -/
def certifiedTruth_s (positive : Bool) : S1_binary 6 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      .conj (btruthCheck_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)
        (btruthAnswer_m positive .newest (.bound 4) (.bound 3))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (btruthCheck_delta_l ..) (btruthAnswer_delta_l ..))) }

def certifiedTruth_env_l (T n X E F L : M.Domain) : Env M 6 :=
  (btruth_env_l T n X E F).push L

def CertifiedTruth_d (positive : Bool) (T n X E F L r f : M.Domain) : Prop :=
  ∃ Z H, BtruthCheck_d T n X E F L Z H ∧ BtruthAnswer_d positive H r f

theorem certifiedTruth_matrix_sat_l (hE : Extensional M) (positive : Bool) (ρ : Env M 6) (r f w : M.Domain) :
    Formula.satisfies (((ρ.push r).push f).push w) (certifiedTruth_s positive).matrix.body ↔
      ∃ Z, M.mem Z w ∧ ∃ H, M.mem H w ∧
        BtruthCheck_d (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) Z H ∧
          BtruthAnswer_d positive H r f := by
  simp only [certifiedTruth_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    btruthCheck_sat_l hE, btruthAnswer_sat_l hE]
  rfl

theorem certifiedTruth_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 6) (r f : M.Domain) :
    (certifiedTruth_s positive).schema.denote ρ r f ↔
      CertifiedTruth_d positive (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) r f := by
  rw [S1_binary.sat_l]
  simp only [certifiedTruth_matrix_sat_l hKP.1]
  constructor
  · rintro ⟨w, Z, _, H, _, check, answer⟩
    exact ⟨Z, H, check, answer⟩
  · rintro ⟨Z, H, check, answer⟩
    obtain ⟨w, hw⟩ := KP.exists_pair hKP Z H
    exact ⟨w, Z, (hw Z).mpr (Or.inl rfl), H, (hw H).mpr (Or.inr rfl), check, answer⟩

/-- 任意完整证书确定正负真值，不依赖外部选择的历史。 -/
theorem certifiedTruth_value_l (hZF : M.Models ZF) (positive : Bool) {T ω n X E F L Z H r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (check : BtruthCheck_d T n X E F L Z H) :
    CertifiedTruth_d positive T n X E F L r f ↔ BtruthAnswer_d positive H r f := by
  constructor
  · rintro ⟨W, J, hc, answer⟩
    have eq := btruthCertificate_unique_l hZF valid hc check
    exact eq ▸ answer
  · exact fun answer => ⟨Z, H, check, answer⟩

/-- 正负 Σ₁ 模板在全部合法内部程序上互补。 -/
theorem certifiedTruth_complement_l (hZF : M.Models ZF) {T ω n X E F L r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) :
    CertifiedTruth_d false T n X E F L r f ↔ ¬ CertifiedTruth_d true T n X E F L r f := by
  obtain ⟨Z, H, check⟩ := btruthCertificate_exists_l hZF valid
  rw [certifiedTruth_value_l hZF false valid check, certifiedTruth_value_l hZF true valid check]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
