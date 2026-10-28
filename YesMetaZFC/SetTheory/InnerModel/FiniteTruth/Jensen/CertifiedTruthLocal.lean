import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CertifiedTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LocalObjectTheorem

/-! # 统一内部真值模板在同一 Jensen 层中的准确解释

正负两个模板共享同层的实际完整历史。在嵌套结构中的解释以有界证书为依据，
不要求小层满足 KP。源 Project 公式到内部指令的编译仍是独立义务。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 两个 Σ₁ 模板均具有同层见证，故其层内有界解释与背景真值准确等价。 -/
theorem jh_certifiedTruth_within_l (hZF : M.Models ZF) {a C ω : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (positive : Bool) (ρ : Env M 6) (hp : ∀ i, M.mem (ρ.bound i) C)
    (valid : BoundedFormula_d (ρ.bound 5) ω (ρ.bound 4) (ρ.bound 0) (ρ.bound 1)) (r f : M.Domain) :
    Within_d (certifiedTruth_s positive) ρ r f C ↔
      CertifiedTruth_d positive (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) r f := by
  constructor
  · rintro ⟨w, _, hw⟩
    obtain ⟨Z, _, H, _, check, answer⟩ := (certifiedTruth_matrix_sat_l hZF.1 positive ρ r f w).mp hw
    exact ⟨Z, H, check, answer⟩
  · intro truth
    obtain ⟨Z, H, hZC, hHC, check⟩ := jh_btruthCertificate_l hZF ha h hω hωC
      (hp 5) (hp 4) (hp 3) (hp 2) (hp 1) valid
    have answer := (certifiedTruth_value_l hZF positive valid check).mp truth
    obtain ⟨w, hwC, hw⟩ := (jh_value_closed_l (ZF.models_kpi_l hZF) ha h).exists_l
      (ZF.modelsKP hZF) .pair hZC hHC hZC
    exact ⟨w, hwC, (certifiedTruth_matrix_sat_l hZF.1 positive ρ r f w).mpr
      ⟨Z, (hw Z).mpr (Or.inl rfl), H, (hw H).mpr (Or.inr rfl), check, answer⟩⟩

theorem jh_certifiedTruth_equiv_l (hZF : M.Models ZF) {a C ω : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (positive : Bool) (ρ : Env M 6) (hp : ∀ i, M.mem (ρ.bound i) C)
    (valid : BoundedFormula_d (ρ.bound 5) ω (ρ.bound 4) (ρ.bound 0) (ρ.bound 1)) (r f : M.Domain) :
    Within_d (certifiedTruth_s positive) ρ r f C ↔ (certifiedTruth_s positive).schema.denote ρ r f :=
  (jh_certifiedTruth_within_l hZF ha h hω hωC positive ρ hp valid r f).trans
    (certifiedTruth_sat_l (ZF.modelsKP hZF) positive ρ r f).symm

/-- 原 J 层内的实际 Σ₁ 解释保留正负真值，不调用小层可靠性或 KP。 -/
theorem jh_certifiedTruth_local_l (hZF : M.Models ZF) {a C ω : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) (positive : Bool)
    (ρ : Env (rt_model_l C hn) 6) (r f : (rt_model_l C hn).Domain)
    (valid : BoundedFormula_d (ρ.bound 5).val ω (ρ.bound 4).val (ρ.bound 0).val (ρ.bound 1).val) :
    (certifiedTruth_s positive).schema.denote ρ r f ↔
      (certifiedTruth_s positive).schema.denote (image_env_l (fun x : (rt_model_l C hn).Domain => (x.val : M.Domain)) ρ) r.val f.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hn
    (certifiedTruth_s positive) ρ r f).trans
      (jh_certifiedTruth_equiv_l (M := M) hZF ha h hω hωC positive (image_env_l (fun x : (rt_model_l C hn).Domain => (x.val : M.Domain)) ρ)
        (fun i => (ρ.bound i).property) valid r.val f.val)

private def truthLocalParams : Fin 6 → Term 11 := fun i => .bound ⟨i.val + 2, by omega⟩

private def jensenCertifiedTruthBody (positive : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
      .imp (KP.ord0_m (.bound 10)) <| .imp (jh_value_m (.bound 10) (.bound 9)) <|
        .imp (Formula.isOmega (.bound 8)) <| .imp (.mem (.bound 8) (.bound 9)) <|
          .imp (.mem (.bound 7) (.bound 9)) <| .imp (.mem (.bound 6) (.bound 9)) <|
            .imp (.mem (.bound 5) (.bound 9)) <| .imp (.mem (.bound 4) (.bound 9)) <|
              .imp (.mem (.bound 3) (.bound 9)) <| .imp (.mem (.bound 2) (.bound 9)) <|
                .imp (.mem (.bound 1) (.bound 9)) <| .imp (.mem .newest (.bound 9)) <|
                  .imp (boundedFormula_m (.bound 7) (.bound 8) (.bound 6) (.bound 2) (.bound 3)) <|
                    .iff (within_m (certifiedTruth_s positive) truthLocalParams (.bound 1) .newest (.bound 9))
                      (binary_pred_m (certifiedTruth_s positive).schema truthLocalParams (.bound 1) .newest)

/-- 两个模板各有一个统一量化全部内部程序码的原对象闭句。 -/
def jensenCertifiedTruthLocal (positive : Bool) : Sentence := .ofFormula (jensenCertifiedTruthBody positive)
  (by simp -implicitDefEqProofs [jensenCertifiedTruthBody, truthLocalParams, Definitional.Formula.FreeClosed])

theorem jensenCertifiedTruthLocal_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenCertifiedTruthLocal positive) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0, envFree⟩ : Env M 0) (jensenCertifiedTruthBody positive)
  simp only [jensenCertifiedTruthBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l, Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff, boundedFormula_sat_l (ZF.modelsKP hZF), Formula.satisfies_iff_iff,
    within_sat_l, binary_pred_sat_l]
  intro a C ω T n X E F L r v ha h hω hωC hTC hnC hXC hEC hFC hLC _ _ valid
  let ρ : Env M 6 := ⟨Fin.cases L (Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (fun _ => T))))), envFree⟩
  let ξ := (((((((((((⟨Fin.elim0, envFree⟩ : Env M 0).push a).push C).push ω).push T).push n).push X).push E).push F).push L).push r).push v
  let η : Env M 6 := ⟨fun i => (truthLocalParams i).eval ξ, envFree⟩
  have envEq : η = ρ := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))), rfl⟩
  change Within_d (certifiedTruth_s positive) η r v C ↔ (certifiedTruth_s positive).schema.denote η r v
  rw [envEq]
  exact jh_certifiedTruth_equiv_l hZF ha h hω hωC positive ρ
    (Fin.cases hLC (Fin.cases hFC (Fin.cases hEC (Fin.cases hXC (Fin.cases hnC (fun _ => hTC)))))) valid r v

/-- 原 ZF 中分别证明正、负统一真值模板的同层准确性。 -/
theorem jensenCertifiedTruthLocal_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenCertifiedTruthLocal positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenCertifiedTruthLocal_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
