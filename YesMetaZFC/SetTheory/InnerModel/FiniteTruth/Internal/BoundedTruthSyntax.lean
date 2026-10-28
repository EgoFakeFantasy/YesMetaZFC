import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthNode
import YesMetaZFC.Model.SetTheory.Internal.Truth

/-! # 内部有界程序的真值递归公式

一步输出是完整赋值空间中的实际分离集。公式统一处理模型内程序与序数长度，
递归参数中的语法容器只约束指令码，不截断历史中的真值集。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def Bdomain_d (r H : M.Domain) : Prop := ∀ i, M.mem i r ↔ ∃ A, Rd_entry_d i A H

def bdomain_m {d} (r H : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest r.weaken) (.existsE (rd_entry_m (.bound 1) .newest H.weaken.weaken)))
derive_free_closed bdomain_m

theorem bdomain_sat_l (hE : Extensional M) {d} (ρ : Env M d) (r H : Term d) :
    Formula.satisfies ρ (bdomain_m r H) ↔ Bdomain_d (r.eval ρ) (H.eval ρ) := by
  simp only [bdomain_m, Bdomain_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rd_entry_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

def BtruthAt_d (T n X E F H f : M.Domain) : Prop :=
  ∃ r c, Bdomain_d r H ∧ Rd_entry_d r c F ∧ BtruthNode_d T n X E H c f

def btruthAt_m {d} (T n X E F H f : Term d) : Formula 1 d :=
  .existsE <| .existsE <| .conj (bdomain_m (.bound 1) H.weaken.weaken) <|
    .conj (rd_entry_m (.bound 1) .newest F.weaken.weaken)
      (btruthNode_m T.weaken.weaken n.weaken.weaken X.weaken.weaken E.weaken.weaken
        H.weaken.weaken .newest f.weaken.weaken)
derive_free_closed btruthAt_m

theorem btruthAt_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T n X E F H f : Term d) :
    Formula.satisfies ρ (btruthAt_m T n X E F H f) ↔
      BtruthAt_d (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [btruthAt_m, BtruthAt_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bdomain_sat_l hE, rd_entry_sat_l hE, btruthNode_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

def BtruthStep_d (T n X E F H Y : M.Domain) : Prop :=
  ∀ f, M.mem f Y ↔ M.mem f E ∧ BtruthAt_d T n X E F H f

def btruthStep_m {d} (T n X E F H Y : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest Y.weaken) (.conj (.mem .newest E.weaken)
    (btruthAt_m T.weaken n.weaken X.weaken E.weaken F.weaken H.weaken .newest)))
derive_free_closed btruthStep_m

theorem btruthStep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T n X E F H Y : Term d) :
    Formula.satisfies ρ (btruthStep_m T n X E F H Y) ↔
      BtruthStep_d (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (Y.eval ρ) := by
  simp only [btruthStep_m, BtruthStep_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, btruthAt_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

def btruth_s : BinarySchema 5 := {
  body := btruthStep_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

def btruth_env_l (T n X E F : M.Domain) : Env M 5 :=
  ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push n).push X).push E).push F

theorem btruth_op_l (hE : Extensional M) (ρ : Env M 5) :
    btruth_s.denote ρ = BtruthStep_d (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext H Y
  exact propext (btruthStep_sat_l hE ((ρ.push H).push Y) _ _ _ _ _ _ _)

def BtruthEval_d (I : kpair_convention_l.Interpretation M) (T n X E F length H : M.Domain) : Prop :=
  M.IsRecursiveSequence I (BtruthStep_d T n X E F) H length

def btruthEval_m {d} (T n X E F length H : Term d) : Formula 1 d :=
  Formula.isRecursiveSequence kpair_convention_l btruth_s
    (YesMetaZFC.SetTheory.Definitional.TermVector.ofFn
      (Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (fun _ => T)))))) H length

@[simp] theorem btruthEval_closed_l {d} (T n X E F length H : Term d)
    (hT : T.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hl : length.freeSupport = [])
    (hH : H.freeSupport = []) : (btruthEval_m T n X E F length H).FreeClosed := by
  apply Formula.isRecursiveSequence_freeClosed
  · intro i
    simp only [YesMetaZFC.SetTheory.Definitional.TermVector.get_ofFn]
    exact Fin.cases hF (Fin.cases hE (Fin.cases hX (Fin.cases hn (fun _ => hT)))) i
  · exact hH
  · exact hl

theorem btruthEval_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T n X E F length H : Term d) :
    Formula.satisfies ρ (btruthEval_m T n X E F length H) ↔
      BtruthEval_d (kp_pair_l hKP) (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ)
        (F.eval ρ) (length.eval ρ) (H.eval ρ) := by
  rw [btruthEval_m, Formula.satisfies_isRecursiveSequence_iff (kp_pair_l hKP) hKP.1, btruth_op_l hKP.1]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
