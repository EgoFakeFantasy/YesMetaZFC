import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthLocalStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteAssignmentSpace

/-! # 全部内部有限真值历史的同层性

归纳谓词是原对象公式，并由背景 ZF 分离提供实际归纳集。rud 闭包中的每一步
只作有界分离和有限次配对、并集；小层不承担 KP、Collection 或幂集假设。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 同层实际函数图追加，不把追加运算作为新的闭包假设。 -/
theorem rd_snoc_exists_l (hKP : M.Models KP) {C H r Y : M.Domain} (hC : Rd_closed_d C)
    (hHC : M.mem H C) (hrC : M.mem r C) (hYC : M.mem Y C) :
    ∃ K, M.mem K C ∧ Snoc_d (kp_pair_l hKP) H r Y K := by
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total r Y
  have hpC := hC .opair r Y r hrC hYC hrC p (rd_opair_value_l hKP.1 hp)
  obtain ⟨S, hSC, hS⟩ := hC.exists_l hKP .pair hpC hpC hpC
  obtain ⟨K, hKC, hK⟩ := hC.union_l hKP hHC hSC
  refine ⟨K, hKC, fun v => (hK v).trans (or_congr Iff.rfl ?_)⟩
  exact (hS v).trans ⟨fun eq => (eq.elim id id).symm ▸ hp,
    fun hv => Or.inl ((kp_pair_l hKP).unique hv hp)⟩

/-- 同一下一步和完整追加方程恢复原递归序列，不另建推导或递归核。 -/
theorem btruthEval_snoc_l (hZF : M.Models ZF) {T n X E F r s H Y K : M.Domain}
    (hs : M.IsOrdinal s) (hrs : M.SuccessorOf s r)
    (hH : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F r H)
    (step : BtruthStep_d T n X E F H Y) (snoc : Snoc_d (kp_pair_l (ZF.modelsKP hZF)) H r Y K) :
    BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F s K := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨G, hG⟩ := btruthEval_exists_l hZF T n X E F hs
  have hrsMem := hrs.predecessor_mem
  obtain ⟨Z, hZ⟩ := (hG.1.2.2 r).mp hrsMem
  obtain ⟨P, hp, ps⟩ := hG.2 r hrsMem Z hZ
  have eqP := btruthEval_unique_l hZF (hG.restriction hrsMem hp) hH
  subst P
  have eqZ := btruthStep_unique_l hZF.1 ps step
  subst Z
  have gsnoc : Snoc_d I H r Y G := (snoc_iff_entries_l I hH.1.2.1.1).mpr ⟨hG.1.2.1.1, by
    intro i v
    constructor
    · intro hiv
      rcases (hrs i).mp ((hG.1.2.2 i).mpr ⟨v, hiv⟩) with hi | hi
      · exact Or.inl ((hp.2 i v).mpr ⟨hi, hiv⟩)
      · have eq := hZF.1.eq_of_same_members i r hi
        subst i
        exact Or.inr ⟨rfl, hG.1.2.1.2 r v Y hiv hZ⟩
    · rintro (hiv | ⟨rfl, rfl⟩)
      · exact ((hp.2 i v).mp hiv).2
      · exact hZ⟩
  have eq : K = G := hZF.1.eq_of_same_members K G (fun v => (snoc v).trans (gsnoc v).symm)
  exact eq.symm ▸ hG

def finiteTruthHistory_m {d} (C T n X E F r : Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest C.weaken)
    (btruthEval_m T.weaken n.weaken X.weaken E.weaken F.weaken r.weaken .newest))
derive_free_closed finiteTruthHistory_m

theorem finiteTruthHistory_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (C T n X E F r : Term d) :
    Formula.satisfies ρ (finiteTruthHistory_m C T n X E F r) ↔
      ∃ H, M.mem H (C.eval ρ) ∧ BtruthEval_d (kp_pair_l hKP)
        (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (r.eval ρ) H := by
  simp only [finiteTruthHistory_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, btruthEval_sat_l hKP,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 逐参数有同层传递包络的 rud 闭包包含全部内部有限操作历史。 -/
theorem rd_finite_btruthHistory_l (hZF : M.Models ZF) {C T n X E F L ω : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hnC : M.mem n C)
    (hXC : M.mem X C) (hEC : M.mem E C) (hFC : M.mem F C) (hF : Fn0_d L T F) :
    ∀ r, M.mem r ω → ∃ H, M.mem H C ∧
      BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F r H := by
  let hKP := ZF.modelsKP hZF
  let ρ := (btruth_env_l T n X E F).push C
  let φ : UnarySchema 6 := {
    body := finiteTruthHistory_m (.bound 1) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest }
  have sat r : φ.denote ρ r ↔ ∃ H, M.mem H C ∧ BtruthEval_d (kp_pair_l hKP) T n X E F r H := by
    simp only [φ, UnarySchema.denote, finiteTruthHistory_sat_l hKP]
    rfl
  apply hω.induction (fun r => ∃ H, M.mem H C ∧ BtruthEval_d (kp_pair_l hKP) T n X E F r H)
  · obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨S, fun r => (hS r).trans (and_congr_right fun _ => sat r)⟩
  · intro e he
    have heC : M.mem e C := hC .diff ω ω ω hωC hωC hωC e
      (fun p => iff_of_false (he p) (fun h => h.2 h.1))
    exact ⟨e, heC, ⟨Structure.IsSequenceOfLength.empty (kp_pair_l hKP) he,
      fun r hr => (he r hr).elim⟩⟩
  · intro r hr ih s hrs
    obtain ⟨H, hHC, hH⟩ := ih
    have hrC := hc ω hωC r hr
    obtain ⟨Y, hYC, step⟩ := rd_btruthStep_exists_l hKP hC hc cover hTC hnC hXC hEC hFC hrC hHC
      (fun i c hic => (hF.bound_l hic).2) hH.1.2.2
    obtain ⟨K, hKC, snoc⟩ := rd_snoc_exists_l hKP hC hHC hrC hYC
    have hs := KP.successor_isOrdinal hKP (hω.members_areOrdinals hZF r hr) hrs
    exact ⟨K, hKC, btruthEval_snoc_l hZF hs hrs hH step snoc⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
