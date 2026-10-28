import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthNode

/-! # 原递归核中的统一内部谓词真值历史 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PtruthAt_d (T A n X E F H f : M.Domain) : Prop :=
  ∃ r c, Bdomain_d r H ∧ Rd_entry_d r c F ∧ PtruthNode_d T A n X E H c f

def ptruthAt_m {d} (T A n X E F H f : Term d) : Formula 1 d :=
  .existsE <| .existsE <| .conj (bdomain_m (.bound 1) H.weaken.weaken) <|
    .conj (rd_entry_m (.bound 1) .newest F.weaken.weaken)
      (ptruthNode_m T.weaken.weaken A.weaken.weaken n.weaken.weaken X.weaken.weaken E.weaken.weaken
        H.weaken.weaken .newest f.weaken.weaken)

@[simp] theorem ptruthAt_closed_l {d} (T A n X E F H f : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = []) (hf : f.freeSupport = []) :
    (ptruthAt_m T A n X E F H f).FreeClosed := by
  simp -implicitDefEqProofs [ptruthAt_m,Definitional.Formula.FreeClosed,hT,hA,hn,hX,hE,hF,hH,hf]

theorem ptruthAt_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A n X E F H f : Term d) :
    Formula.satisfies ρ (ptruthAt_m T A n X E F H f) ↔
      PtruthAt_d (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ptruthAt_m,PtruthAt_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    bdomain_sat_l hE,rd_entry_sat_l hE,ptruthNode_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def PtruthStep_d (T A n X E F H Y : M.Domain) : Prop :=
  ∀ f, M.mem f Y ↔ M.mem f E ∧ PtruthAt_d T A n X E F H f

def ptruthStep_m {d} (T A n X E F H Y : Term d) : Formula 1 d :=
  .forallE <| .iff (.mem .newest Y.weaken) <| .conj (.mem .newest E.weaken)
    (ptruthAt_m T.weaken A.weaken n.weaken X.weaken E.weaken F.weaken H.weaken .newest)

@[simp] theorem ptruthStep_closed_l {d} (T A n X E F H Y : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = []) (hY : Y.freeSupport = []) :
    (ptruthStep_m T A n X E F H Y).FreeClosed := by
  simp -implicitDefEqProofs [ptruthStep_m,Definitional.Formula.FreeClosed,hT,hA,hn,hX,hE,hF,hH,hY]

theorem ptruthStep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A n X E F H Y : Term d) :
    Formula.satisfies ρ (ptruthStep_m T A n X E F H Y) ↔
      PtruthStep_d (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (Y.eval ρ) := by
  simp only [ptruthStep_m,PtruthStep_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,ptruthAt_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def ptruth_s : BinarySchema 6 := {
  body := ptruthStep_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

def ptruth_env_l (T A n X E F : M.Domain) : Env M 6 :=
  ⟨Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (Fin.cases A (fun _ => T))))),fun _ => T⟩

theorem ptruth_op_l (hE : Extensional M) (ρ : Env M 6) :
    ptruth_s.denote ρ = PtruthStep_d (ρ.bound 5) (ρ.bound 4) (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext H Y
  exact propext (ptruthStep_sat_l hE ((ρ.push H).push Y) _ _ _ _ _ _ _ _)

def PtruthEval_d (I : kpair_convention_l.Interpretation M) (T A n X E F length H : M.Domain) : Prop :=
  M.IsRecursiveSequence I (PtruthStep_d T A n X E F) H length

def ptruthEval_m {d} (T A n X E F length H : Term d) : Formula 1 d :=
  Formula.isRecursiveSequence kpair_convention_l ptruth_s
    (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (Fin.cases A (fun _ => T))))))) H length

@[simp] theorem ptruthEval_closed_l {d} (T A n X E F length H : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hl : length.freeSupport = []) (hH : H.freeSupport = []) :
    (ptruthEval_m T A n X E F length H).FreeClosed := by
  apply Formula.isRecursiveSequence_freeClosed
  · intro i
    simp only [Definitional.TermVector.get_ofFn]
    exact Fin.cases hF (Fin.cases hE (Fin.cases hX (Fin.cases hn (Fin.cases hA (fun _ => hT))))) i
  · exact hH
  · exact hl

theorem ptruthEval_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T A n X E F length H : Term d) :
    Formula.satisfies ρ (ptruthEval_m T A n X E F length H) ↔
      PtruthEval_d (kp_pair_l hKP) (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ)
        (F.eval ρ) (length.eval ρ) (H.eval ρ) := by
  rw [ptruthEval_m,Formula.satisfies_isRecursiveSequence_iff (kp_pair_l hKP) hKP.1,ptruth_op_l hKP.1]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
