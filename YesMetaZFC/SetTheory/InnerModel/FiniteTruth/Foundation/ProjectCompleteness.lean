import YesMetaZFC.Model.SetTheory.ProjectExtensional
import YesMetaZFC.Model.SetTheory.ProjectSoundness
import YesMetaZFC.Model.Henkin.StrongCompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserSchedule

/-! # 任意 Project 模型上的证明回到原推导核

理论显式包含原外延性公理。纯语言载体 universe 为零时，原强完备性
已经足够；传入的数学结论仍须覆盖所有该 universe 中的背景模型。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.SetTheory.Definitional.Project

/-- 任意背景模型中的闭句证明给出原纯隶属 Hilbert 推导。 -/
theorem derives_of_models {T : Project.Theory} (hExt : T Axioms.extensionality)
    {φ : Project.Sentence}
    (h : ∀ M : SetTheory.Structure.{0}, M.Models T → M.SatisfiesSentence φ) :
    Project.Derives T φ := by
  apply Logic.FirstOrder.Completeness.strong_completeness
    Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserSchedule.target
  intro M hM
  have he : Extensional (FirstOrderSemantics.reduct M) :=
    FirstOrderSemantics.extensional_iff_l.mp
      (hM _ ⟨Axioms.extensionality, hExt, rfl⟩)
  exact (FirstOrderSemantics.sentence_correct he φ).mpr
    (h (FirstOrderSemantics.reduct M) ((FirstOrderSemantics.models_iff he T).mp hM))

/-- 对包含外延性的理论，模型语义与原闭句推导准确对应。 -/
theorem derives_iff_models {T : Project.Theory} (hExt : T Axioms.extensionality)
    (φ : Project.Sentence) :
    Project.Derives T φ ↔
      ∀ M : SetTheory.Structure.{0}, M.Models T → M.SatisfiesSentence φ := by
  constructor
  · intro h M hM
    exact FirstOrderSemantics.sound_l hM h
  · exact derives_of_models hExt

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge
