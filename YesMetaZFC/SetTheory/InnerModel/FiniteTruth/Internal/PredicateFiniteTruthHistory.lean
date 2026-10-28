import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthLocalStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthHistory

/-! # 全部内部有限谓词历史的同层构造

原对象公式的内部 ω 归纳；实际图与行同步追加，不预设当前层 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem ptruthEval_snoc_l (hZF : M.Models ZF) {T A n X E F r s H Y K : M.Domain}
    (hs : M.IsOrdinal s) (succ : M.SuccessorOf s r)
    (history : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F r H)
    (step : PtruthStep_d T A n X E F H Y) (snoc : Snoc_d (kp_pair_l (ZF.modelsKP hZF)) H r Y K) :
    PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F s K := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨G,large⟩ := ptruthEval_exists_l hZF T A n X E F hs
  have hrs := succ.predecessor_mem
  obtain ⟨Z,value⟩ := (large.1.2.2 r).mp hrs
  obtain ⟨P,pref,atRow⟩ := large.2 r hrs Z value
  have eqP := ptruthEval_unique_l hZF (large.restriction hrs pref) history
  subst P
  have eqZ := ptruthStep_unique_l hZF.1 atRow step
  subst Z
  have gsnoc : Snoc_d I H r Y G := (snoc_iff_entries_l I history.1.2.1.1).mpr ⟨large.1.2.1.1,by
    intro i v
    constructor
    · intro entry
      rcases (succ i).mp ((large.1.2.2 i).mpr ⟨v,entry⟩) with old | same
      · exact Or.inl ((pref.2 i v).mpr ⟨old,entry⟩)
      · have eq := hZF.1.eq_of_same_members i r same
        subst i
        exact Or.inr ⟨rfl,large.1.2.1.2 r v Y entry value⟩
    · rintro (entry | ⟨rfl,rfl⟩)
      · exact ((pref.2 i v).mp entry).2
      · exact value⟩
  have eq : K = G := hZF.1.eq_of_same_members K G (fun v => (snoc v).trans (gsnoc v).symm)
  exact eq.symm ▸ large

def pfiniteTruthHistory_m {d} (C T A n X E F r : Term d) : Formula 1 d :=
  .existsE <| .conj (.mem .newest C.weaken)
    (ptruthEval_m T.weaken A.weaken n.weaken X.weaken E.weaken F.weaken r.weaken .newest)

@[simp] theorem pfiniteTruthHistory_closed_l {d} (C T A n X E F r : Term d)
    (hC : C.freeSupport = []) (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = [])
    (hX : X.freeSupport = []) (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hr : r.freeSupport = []) :
    (pfiniteTruthHistory_m C T A n X E F r).FreeClosed := by
  simp -implicitDefEqProofs [pfiniteTruthHistory_m,Definitional.Formula.FreeClosed,hC,hT,hA,hn,hX,hE,hF,hr]

theorem pfiniteTruthHistory_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (C T A n X E F r : Term d) :
    Formula.satisfies ρ (pfiniteTruthHistory_m C T A n X E F r) ↔
      ∃ H, M.mem H (C.eval ρ) ∧ PtruthEval_d (kp_pair_l hKP)
        (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (r.eval ρ) H := by
  simp only [pfiniteTruthHistory_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,ptruthEval_sat_l hKP,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem rd_finite_ptruthHistory_l (hZF : M.Models ZF) {C T A n X E F L ω : M.Domain}
    (rud : Rd_closed_d C) (trans : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hAC : M.mem A C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hEC : M.mem E C) (hFC : M.mem F C) (program : Fn0_d L T F) :
    ∀ r, M.mem r ω → ∃ H, M.mem H C ∧ PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F r H := by
  let hKP := ZF.modelsKP hZF
  let ρ := (ptruth_env_l T A n X E F).push C
  let φ : UnarySchema 7 := {
    body := pfiniteTruthHistory_m (.bound 1) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest }
  have sat r : φ.denote ρ r ↔ ∃ H, M.mem H C ∧ PtruthEval_d (kp_pair_l hKP) T A n X E F r H := by
    simp only [φ,UnarySchema.denote,pfiniteTruthHistory_sat_l hKP]
    rfl
  apply hω.induction (fun r => ∃ H, M.mem H C ∧ PtruthEval_d (kp_pair_l hKP) T A n X E F r H)
  · obtain ⟨S,sep⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨S,fun r => (sep r).trans (and_congr_right fun _ => sat r)⟩
  · intro e empty
    have heC : M.mem e C := rud .diff ω ω ω hωC hωC hωC e
      (fun p => iff_of_false (empty p) (fun bad => bad.2 bad.1))
    exact ⟨e,heC,⟨Structure.IsSequenceOfLength.empty (kp_pair_l hKP) empty,fun r hr => (empty r hr).elim⟩⟩
  · intro r hr ih s succ
    obtain ⟨H,hHC,history⟩ := ih
    have hrC := trans ω hωC r hr
    obtain ⟨Y,hYC,step⟩ := rd_ptruthStep_exists_l hKP rud trans cover hTC hAC hnC hXC hEC hFC hrC hHC
      (fun i c entry => (program.bound_l entry).2) history.1.2.2
    obtain ⟨K,hKC,snoc⟩ := rd_snoc_exists_l hKP rud hHC hrC hYC
    have hs := KP.successor_isOrdinal hKP (hω.members_areOrdinals hZF r hr) succ
    exact ⟨K,hKC,ptruthEval_snoc_l hZF hs succ history step snoc⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
