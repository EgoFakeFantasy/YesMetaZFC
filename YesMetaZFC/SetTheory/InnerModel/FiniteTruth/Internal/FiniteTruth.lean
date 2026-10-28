import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CertifiedTruth
import YesMetaZFC.SetTheory.InnerModel.Separation.Enclosure

/-! # 无自由赋值空间参数的统一 Σ₁ 操作真值

同一个见证集合容纳完整空间证书与整张真值历史。E 在实际有界矩阵内部存在量化，
合法赋值也有界核验；参数只保留 T、ω、n、X、F、L。原公式编译仍须另证。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def FiniteTruthCert_d (positive : Bool) (T ω n X F L r f e s Z S E V H : M.Domain) : Prop :=
  AssignmentSpaceCert_d ω n X e s Z S E ∧ M.mem f E ∧
    BtruthCheck_d T n X E F L V H ∧ BtruthAnswer_d positive H r f

def FiniteTruth_d (positive : Bool) (T ω n X F L r f : M.Domain) : Prop :=
  ∃ e s Z S E V H, FiniteTruthCert_d positive T ω n X F L r f e s Z S E V H

/-- 参数槽依次为 L、F、X、n、ω、T；输入为行号，输出为合法赋值。 -/
def finiteTruth_s (positive : Bool) : S1_binary 6 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <|
        Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
          Formula.existsMem (.bound 6) <|
            .conj (assignmentSpaceCert_m (.bound 14) (.bound 13) (.bound 12) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2)) <|
              .conj (.mem (.bound 8) (.bound 2)) <|
                .conj (btruthCheck_m (.bound 15) (.bound 13) (.bound 12) (.bound 2) (.bound 11) (.bound 10) (.bound 1) .newest)
                  (btruthAnswer_m positive .newest (.bound 9) (.bound 8))
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (assignmentSpaceCert_delta_l ..) (.conj (.mem _ _) (.conj (btruthCheck_delta_l ..) (btruthAnswer_delta_l ..)))))))))) }

/-- 固定外部有限见证束的实际集合覆盖；不用于替代内部长度归纳。 -/
theorem finiteTruth_cover_l (hKP : M.Models KP) (L : List M.Domain) :
    ∃ w, ∀ x ∈ L, M.mem x w := by
  induction L with
  | nil =>
    obtain ⟨w,_⟩ := KP.exists_empty hKP
    exact ⟨w,fun _ h => (List.not_mem_nil h).elim⟩
  | cons a L ih =>
    obtain ⟨w,hw⟩ := ih
    obtain ⟨v,hv⟩ := KP.exists_insert hKP w a
    exact ⟨v,fun x hx => (hv x).mpr ((List.mem_cons.mp hx).elim
      (fun eq => Or.inr eq) (fun hx => Or.inl (hw x hx)))⟩

/-- 同层覆盖固定见证束只使用有限次 rud 插入。 -/
theorem rd_finiteTruth_cover_l (hKP : M.Models KP) {C A : M.Domain} (hC : Rd_closed_d C)
    (hAC : M.mem A C) (L : List M.Domain) (hL : ∀ x ∈ L, M.mem x C) :
    ∃ w, M.mem w C ∧ ∀ x ∈ L, M.mem x w := by
  induction L with
  | nil => exact ⟨A,hAC,fun _ h => (List.not_mem_nil h).elim⟩
  | cons a L ih =>
    obtain ⟨w,hwC,hw⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    obtain ⟨v,hvC,hv⟩ := rd_insert_closed_l hKP hC hwC (hL a (List.mem_cons_self ..))
    exact ⟨v,hvC,fun x hx => (hv x).mpr ((List.mem_cons.mp hx).elim
      (fun eq => Or.inr eq) (fun hx => Or.inl (hw x hx)))⟩

theorem finiteTruth_matrix_sat_l (hE : Extensional M) (positive : Bool) (ρ : Env M 6) (r f w : M.Domain) :
    Formula.satisfies (((ρ.push r).push f).push w) (finiteTruth_s positive).matrix.body ↔
      ∃ e, M.mem e w ∧ ∃ s, M.mem s w ∧ ∃ Z, M.mem Z w ∧ ∃ S, M.mem S w ∧
        ∃ E, M.mem E w ∧ ∃ V, M.mem V w ∧ ∃ H, M.mem H w ∧
          FiniteTruthCert_d positive (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2)
            (ρ.bound 1) (ρ.bound 0) r f e s Z S E V H := by
  simp only [finiteTruth_s,FiniteTruthCert_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    assignmentSpaceCert_sat_l hE,Formula.satisfies_mem_iff,btruthCheck_sat_l hE,btruthAnswer_sat_l hE]
  rfl

theorem finiteTruth_sat_l (hKP : M.Models KP) (positive : Bool) (ρ : Env M 6) (r f : M.Domain) :
    (finiteTruth_s positive).schema.denote ρ r f ↔
      FiniteTruth_d positive (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) r f := by
  rw [S1_binary.sat_l]
  simp only [finiteTruth_matrix_sat_l hKP.1]
  constructor
  · rintro ⟨w,e,_,s,_,Z,_,S,_,E,_,V,_,H,_,cert⟩
    exact ⟨e,s,Z,S,E,V,H,cert⟩
  · rintro ⟨e,s,Z,S,E,V,H,cert⟩
    obtain ⟨w,hw⟩ := finiteTruth_cover_l hKP [e,s,Z,S,E,V,H]
    exact ⟨w,e,hw e (by simp),s,hw s (by simp),Z,hw Z (by simp),S,hw S (by simp),
      E,hw E (by simp),V,hw V (by simp),H,hw H (by simp),cert⟩

/-- 空间参数已在有界见证中恢复；与任意给定的真实完整空间准确对应。 -/
theorem finiteTruth_space_l (hZF : M.Models ZF) (positive : Bool) {T ω n X E F L r f : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω)
    (full : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X) :
    FiniteTruth_d positive T ω n X F L r f ↔ M.mem f E ∧ CertifiedTruth_d positive T n X E F L r f := by
  constructor
  · rintro ⟨e,s,Z,S,A,V,H,space,hf,truth,answer⟩
    have fa := assignmentSpaceCert_sound_l hZF hω space
    have eq := hZF.1.eq_of_same_members A E (fun g => (fa g).trans (full g).symm)
    subst A
    exact ⟨hf,V,H,truth,answer⟩
  · rintro ⟨hf,V,H,truth,answer⟩
    obtain ⟨e,s,Z,S,space⟩ := assignmentSpaceCert_for_space_l hZF hω hn full
    exact ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩

/-- 合法赋值上的正负模板仍互补；域外对象不被误当作赋值。 -/
theorem finiteTruth_complement_l (hZF : M.Models ZF) {T ω n X F L r f : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    FiniteTruth_d false T ω n X F L r f ↔ ¬ FiniteTruth_d true T ω n X F L r f := by
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n X
  have hfE := (full f).mpr hf
  rw [finiteTruth_space_l hZF false hω valid.variables full,finiteTruth_space_l hZF true hω valid.variables full]
  simpa only [hfE,true_and] using (certifiedTruth_complement_l hZF (r := r) (f := f) valid)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
