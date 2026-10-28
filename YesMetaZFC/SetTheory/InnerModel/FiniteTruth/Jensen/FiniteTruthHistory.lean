import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteAssignmentSpace

/-! # 原 Jensen 层中的完整有限真值证书

原微层访问给出逐参数的同层传递包络。由原公式的内部 ω 归纳，所有有限历史
及其实际行容器留在同一宏观 J 层；不假设该层满足 KP、Collection 或 Power Set。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 原宏观 J 层中的每个参数都有实际同层传递包络。 -/
theorem jh_local_enclosure_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) :
    ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U := by
  have hC := jh_value_closed_l hM ha h
  have access := js_rep_access_l hM hC (jh_order_rep_l hM ha h)
  intro x hx
  obtain ⟨b, U, R, hb, hUR, hUC, hxU⟩ := access x hx
  exact ⟨U, hUC, (js_coherence_l hM hb hUR).1, hxU⟩

/-- 程序及全部参数在同一 J 层时，任意内部有限长度的操作历史仍在该层。 -/
theorem jh_finite_btruthHistory_l (hZF : M.Models ZF) {a C T n X E F L ω : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C) (hXC : M.mem X C)
    (hEC : M.mem E C) (hFC : M.mem F C) (hF : Fn0_d L T F) :
    ∀ r, M.mem r ω → ∃ H, M.mem H C ∧
      BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F r H := by
  let hM := ZF.models_kpi_l hZF
  exact rd_finite_btruthHistory_l hZF (jh_value_closed_l hM ha h) (jh_value_transitive_l hM h)
    (jh_local_enclosure_l hM ha h) hω hωC hTC hnC hXC hEC hFC hF

/-- 合法程序的整张真值图及实际行容器都留在原同一个 J 层中。 -/
theorem jh_btruthCertificate_l (hZF : M.Models ZF) {a C ω T n X E F L : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C) (hXC : M.mem X C)
    (hEC : M.mem E C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F) :
    ∃ Z H, M.mem Z C ∧ M.mem H C ∧ BtruthCheck_d T n X E F L Z H := by
  let hKP := ZF.modelsKP hZF
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  obtain ⟨H, hHC, hH⟩ := jh_finite_btruthHistory_l hZF ha h hω hωC hTC hnC hXC hEC hFC valid.graph L valid.finite
  obtain ⟨Z, hZC, hZ⟩ := hC.exists_l hKP .range hHC hHC hHC
  have fn : Fn0_d L Z H := fn0_of_function_l hKP ⟨hH.1.2.1, hH.1.2.2, fun r hr => by
    obtain ⟨Y, hY⟩ := (hH.1.2.2 r).mp hr
    exact ⟨Y, (hZ Y).mpr ⟨r, hY⟩, hY⟩⟩
  exact ⟨Z, H, hZC, hHC, btruthCheck_of_eval_l hKP valid hH fn⟩

private def jensenBoundedTruthBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 8)) <| .imp (jh_value_m (.bound 8) (.bound 7)) <|
      .imp (Formula.isOmega (.bound 6)) <| .imp (.mem (.bound 6) (.bound 7)) <|
        .imp (.mem (.bound 5) (.bound 7)) <| .imp (.mem (.bound 4) (.bound 7)) <|
          .imp (.mem (.bound 3) (.bound 7)) <| .imp (.mem (.bound 2) (.bound 7)) <|
            .imp (.mem (.bound 1) (.bound 7)) <|
              .imp (boundedFormula_m (.bound 5) (.bound 6) (.bound 4) .newest (.bound 1)) <|
                .existsE <| .existsE <| .conj (.mem (.bound 1) (.bound 9)) <|
                  .conj (.mem .newest (.bound 9))
                    (btruthCheck_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)

/-- 对全部内部程序码和有限长度统一的同层完整真值证书句子。 -/
def jensenBoundedTruth : Sentence := .ofFormula jensenBoundedTruthBody
  (by simp -implicitDefEqProofs [jensenBoundedTruthBody, Definitional.Formula.FreeClosed])

theorem jensenBoundedTruth_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenBoundedTruth := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0) jensenBoundedTruthBody
  simp only [jensenBoundedTruthBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l, Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff, boundedFormula_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, btruthCheck_sat_l hZF.1]
  intro a C ω T n X E F L ha h hω hωC hTC hnC hXC hEC hFC valid
  exact jh_btruthCertificate_l hZF ha h hω hωC hTC hnC hXC hEC hFC valid

theorem jensenBoundedTruth_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenBoundedTruth :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenBoundedTruth_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
