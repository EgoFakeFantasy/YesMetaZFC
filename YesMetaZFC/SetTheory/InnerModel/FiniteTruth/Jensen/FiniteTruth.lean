import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AssignmentSpaceCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CertifiedTruthLocal

/-! # 组合空间与真值证书的同层准确性

解释器不再把 E 作为参数。完整空间、空间表、真值图及全部证书对象在原同一 J
层中构造，再作固定有限见证束的 rud 装配；小层不假设 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 全部七个组合证书对象有同层见证，故正负模板的层内解释准确。 -/
theorem jh_finiteTruth_within_l (hZF : M.Models ZF) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (positive : Bool) (ρ : Env M 6)
    (hp : ∀ i, M.mem (ρ.bound i) C) (hω : M.IsOmega (ρ.bound 4))
    (valid : BoundedFormula_d (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 0) (ρ.bound 1)) (r f : M.Domain) :
    Within_d (finiteTruth_s positive) ρ r f C ↔
      FiniteTruth_d positive (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) r f := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨e,_,s,_,Z,_,S,_,E,_,V,_,H,_,cert⟩ := (finiteTruth_matrix_sat_l hZF.1 positive ρ r f w).mp hw
    exact ⟨e,s,Z,S,E,V,H,cert⟩
  · rintro ⟨e0,s0,Z0,S0,A,V0,H0,space0,hf0,truth0,answer0⟩
    obtain ⟨e,s,Z,S,E,heC,hsC,hZC,hSC,hEC,space⟩ :=
      jh_assignmentSpaceCertificate_l hZF ha h hω (hp 4) (hp 2) valid.variables
    have fullA := assignmentSpaceCert_sound_l hZF hω space0
    have fullE := assignmentSpaceCert_sound_l hZF hω space
    have eq := hZF.1.eq_of_same_members A E (fun g => (fullA g).trans (fullE g).symm)
    subst A
    obtain ⟨V,H,hVC,hHC,truth⟩ := jh_btruthCertificate_l hZF ha h hω
      (hp 4) (hp 5) (hp 3) (hp 2) hEC (hp 1) valid
    have answer := (certifiedTruth_value_l hZF positive valid truth).mp ⟨V0,H0,truth0,answer0⟩
    have inC : ∀ v, v ∈ [e,s,Z,S,E,V,H] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) ha h) (hp 4) [e,s,Z,S,E,V,H] inC
    exact ⟨w,hwC,(finiteTruth_matrix_sat_l hZF.1 positive ρ r f w).mpr
      ⟨e,hw e (by simp),s,hw s (by simp),Z,hw Z (by simp),S,hw S (by simp),
        E,hw E (by simp),V,hw V (by simp),H,hw H (by simp),space,hf0,truth,answer⟩⟩

/-- 原 J 层中的实际 Σ₁ 图与背景图准确一致，不需要层内 KP。 -/
theorem jh_finiteTruth_local_l (hZF : M.Models ZF) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hnC : Nonempty {x : M.Domain // M.mem x C}) (positive : Bool)
    (ρ : Env (rt_model_l C hnC) 6) (r f : (rt_model_l C hnC).Domain)
    (hω : M.IsOmega (ρ.bound 4).val)
    (valid : BoundedFormula_d (ρ.bound 5).val (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 0).val (ρ.bound 1).val) :
    (finiteTruth_s positive).schema.denote ρ r f ↔ (finiteTruth_s positive).schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) r.val f.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC (finiteTruth_s positive) ρ r f).trans
    ((jh_finiteTruth_within_l (M := M) hZF ha h positive
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
      (fun i => (ρ.bound i).property) hω valid r.val f.val).trans
        (finiteTruth_sat_l (ZF.modelsKP hZF) positive
          (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) r.val f.val).symm)

private def finiteTruthLocalParams : Fin 6 → Term 10 := fun i => .bound ⟨i.val + 2, by omega⟩

private def jensenFiniteTruthLocalBody (positive : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 9)) <| .imp (jh_value_m (.bound 9) (.bound 8)) <|
      .imp (Formula.isOmega (.bound 6)) <| .imp (.mem (.bound 6) (.bound 8)) <|
        .imp (.mem (.bound 7) (.bound 8)) <| .imp (.mem (.bound 5) (.bound 8)) <|
          .imp (.mem (.bound 4) (.bound 8)) <| .imp (.mem (.bound 3) (.bound 8)) <|
            .imp (.mem (.bound 2) (.bound 8)) <| .imp (.mem (.bound 1) (.bound 8)) <|
              .imp (.mem .newest (.bound 8)) <|
                .imp (boundedFormula_m (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 3)) <|
                  .iff (within_m (finiteTruth_s positive) finiteTruthLocalParams (.bound 1) .newest (.bound 8))
                    (binary_pred_m (finiteTruth_s positive).schema finiteTruthLocalParams (.bound 1) .newest)

def jensenFiniteTruthLocal (positive : Bool) : Sentence := .ofFormula (jensenFiniteTruthLocalBody positive)
  (by simp -implicitDefEqProofs [jensenFiniteTruthLocalBody,finiteTruthLocalParams,Definitional.Formula.FreeClosed])

theorem jensenFiniteTruthLocal_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenFiniteTruthLocal positive) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (jensenFiniteTruthLocalBody positive)
  simp only [jensenFiniteTruthLocalBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    boundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_iff_iff,within_sat_l,binary_pred_sat_l]
  intro a C T ω n X F L r f ha h hω hωC hTC hnC hXC hFC hLC _ _ valid
  let ρ : Env M 6 := ⟨Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T))))),envFree⟩
  let ξ := ((((((((((⟨Fin.elim0,envFree⟩ : Env M 0).push a).push C).push T).push ω).push n).push X).push F).push L).push r).push f
  let η : Env M 6 := ⟨fun i => (finiteTruthLocalParams i).eval ξ,envFree⟩
  have envEq : η = ρ := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))),rfl⟩
  change Within_d (finiteTruth_s positive) η r f C ↔ (finiteTruth_s positive).schema.denote η r f
  rw [envEq]
  exact (jh_finiteTruth_within_l hZF ha h positive ρ
    (Fin.cases hLC (Fin.cases hFC (Fin.cases hXC (Fin.cases hnC (Fin.cases hωC (fun _ => hTC)))))) hω valid r f).trans
      (finiteTruth_sat_l (ZF.modelsKP hZF) positive ρ r f).symm

theorem jensenFiniteTruthLocal_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenFiniteTruthLocal positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenFiniteTruthLocal_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
