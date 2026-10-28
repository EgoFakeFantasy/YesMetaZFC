import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness
import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy
import YesMetaZFC.Model.SetTheory.KPInduction
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # Jensen 层存在唯一性的对象句子

这是对已有内部 J 层接口的原推导核封装，背景为原 ZF。
它验证本工程的公式、任意模型语义和正式可推导性连接，不承担 YesMetaZFC.SetTheory.InnerModel.FiniteTruth 下降结论。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

universe u

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

/-- 每个内部序数处都有一个且只有一个原 Jensen 层。 -/
def levelExistsUnique : Project.Sentence := .ofFormula
  (.forallE (.imp (KP.ord0_m .newest)
    (.existsE (.conj (jh_value_m (.bound 1) .newest)
      (.forallE (.imp (jh_value_m (.bound 2) .newest)
        (Formula.extensionalEq .newest (.bound 1))))))))
  (by
    simp [Definitional.Formula.FreeClosed]
    exact ⟨KP.ord0_m_freeClosed _ rfl, jh_value_m_freeClosed _ _ rfl rfl,
      jh_value_m_freeClosed _ _ rfl rfl⟩)

/-- 任意 ZF 模型都满足这个原对象句子；不假定外部标准性。 -/
theorem levelExistsUnique_models (M : SetTheory.Structure.{u})
    (hZF : M.Models ZF) : M.SatisfiesSentence levelExistsUnique := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0) levelExistsUnique.formula
  simp only [levelExistsUnique, Project.Sentence.ofFormula,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l,
    Formula.satisfies_extensionalEq_iff_eq hZF.1]
  intro a _
  obtain ⟨Y, hY⟩ := jh_value_exists_l (ZF.models_kpi_l hZF) a
  exact ⟨Y, hY, fun Z hZ => jh_value_unique_l (ZF.models_kpi_l hZF) hZ hY⟩

/-- 原 ZF 中的正式推导证书。 -/
theorem levelExistsUnique_derives : Project.Derives ZF levelExistsUnique :=
  ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => levelExistsUnique_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
