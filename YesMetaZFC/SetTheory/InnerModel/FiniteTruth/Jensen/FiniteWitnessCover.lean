import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteSubset

/-! # 原 J 层中的内部有限见证覆盖

固定原二元模板的逐点层内见证可对任意内部有限索引集装配成同层覆盖集合。
归纳谓词是实际原对象公式；只使用背景 ZF 的有限集合归纳和同层 rud 插入。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

private def coverParams4 {k} : Fin k → Term (k+4) := fun i =>
  (.bound i : Term k).weaken.weaken.weaken.weaken
private def coverParams5 {k} : Fin k → Term (k+5) := fun i =>
  (.bound i : Term k).weaken.weaken.weaken.weaken.weaken

theorem jh_finite_witnessCover_l (hZF : M.Models ZF) {k} (φ : BinarySchema k) (ρ : Env M k)
    {α C ω A : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω A)
    (total : ∀ i, M.mem i A → ∃ w, M.mem w C ∧ φ.denote ρ i w) :
    ∃ V, M.mem V C ∧ ∀ i, M.mem i A → ∃ w, M.mem w V ∧ φ.denote ρ i w := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  let η := ρ.push C
  let ψ : UnarySchema (k+1) := {
    body := .imp
      (Formula.forallMem .newest <| Formula.existsMem (.bound 2) <|
        binary_pred_m φ coverParams4 (.bound 1) .newest)
      (Formula.existsMem (.bound 1) <| Formula.forallMem (.bound 1) <| Formula.existsMem (.bound 1) <|
        binary_pred_m φ coverParams5 (.bound 1) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,coverParams4,coverParams5] }
  have sat X : ψ.denote η X ↔
      (∀ i, M.mem i X → ∃ w, M.mem w C ∧ φ.denote ρ i w) →
        ∃ V, M.mem V C ∧ ∀ i, M.mem i X → ∃ w, M.mem w V ∧ φ.denote ρ i w := by
    simp only [UnarySchema.denote,ψ,Formula.satisfies_imp_iff,Formula.satisfies_forallMem_iff,
      Formula.satisfies_existsMem_iff,binary_pred_sat_l,coverParams4,coverParams5,Definitional.Term.eval_weaken]
    rfl
  have all := ZF.finite_ind_l I hZF hω ψ η (by
    intro E empty
    apply (sat E).mpr
    intro _
    obtain ⟨D,hDC,_⟩ := closed.exists_l hKP .diff hωC hωC hωC
    exact ⟨D,hDC,fun i hi => (empty i hi).elim⟩) (by
      intro X x Y _ ih inserted
      apply (sat Y).mpr
      intro witnesses
      obtain ⟨V,hVC,cover⟩ := (sat X).mp ih (fun i hi => witnesses i ((inserted i).mpr (Or.inl hi)))
      obtain ⟨w,hwC,hit⟩ := witnesses x ((inserted x).mpr (Or.inr rfl))
      obtain ⟨W,hWC,hW⟩ := rd_insert_closed_l hKP closed hVC hwC
      refine ⟨W,hWC,fun i hi => ?_⟩
      rcases (inserted i).mp hi with old | eq
      · obtain ⟨z,hz,sat⟩ := cover i old
        exact ⟨z,(hW z).mpr (Or.inl hz),sat⟩
      · subst i
        exact ⟨w,(hW w).mpr (Or.inr rfl),hit⟩)
  exact (sat A).mp (all A finite) total

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
