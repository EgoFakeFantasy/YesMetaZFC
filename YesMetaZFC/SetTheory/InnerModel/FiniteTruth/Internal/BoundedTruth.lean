import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthSyntax

/-! # 内部有界程序的整张真值历史

一步总性由分离证明；原对象序数递归产生整张历史，并给出唯一性、逐行展开及
输出集合的统一赋值界。此处尚不证明历史属于给定小 J 层或原公式编译正确性。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem btruthStep_exists_l (hZF : M.Models ZF) (T n X E F H : M.Domain) :
    ∃ Y, BtruthStep_d T n X E F H Y := by
  let ρ := (btruth_env_l T n X E F).push H
  let φ : UnarySchema 6 := {
    body := btruthAt_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Y, hY⟩ := ZF.separation_exists_d hZF φ ρ E
  exact ⟨Y, fun f => (hY f).trans (and_congr_right fun _ => btruthAt_sat_l hZF.1 (ρ.push f) _ _ _ _ _ _ _)⟩

theorem btruthStep_unique_l (hE : Extensional M) {T n X E F H Y Z : M.Domain}
    (hy : BtruthStep_d T n X E F H Y) (hz : BtruthStep_d T n X E F H Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun f => (hy f).trans (hz f).symm)

theorem btruth_class_l (hZF : M.Models ZF) (T n X E F : M.Domain) :
    M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF)) (BtruthStep_d T n X E F) := by
  intro H _
  obtain ⟨Y, hY⟩ := btruthStep_exists_l hZF T n X E F H
  exact ⟨Y, hY, fun Z hZ => btruthStep_unique_l hZF.1 hZ hY⟩

/-- 量化模型内序数长度，包含模型内的非标准有限程序。 -/
theorem btruthEval_exists_l (hZF : M.Models ZF) (T n X E F : M.Domain) {length : M.Domain}
    (hl : M.IsOrdinal length) : ∃ H, BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length H := by
  have ho : btruth_s.denote (btruth_env_l T n X E F) = BtruthStep_d T n X E F :=
    btruth_op_l hZF.1 (btruth_env_l T n X E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF))
      (btruth_s.denote (btruth_env_l T n X E F)) := by
    rw [ho]
    exact btruth_class_l hZF T n X E F
  obtain ⟨H, hH⟩ := ZF.recursiveSequence_exists hZF (kp_pair_l (ZF.modelsKP hZF))
    (btruth_env_l T n X E F) btruth_s hc hl
  exact ⟨H, by simpa only [ho, BtruthEval_d] using hH⟩

theorem btruthEval_unique_l (hZF : M.Models ZF) {T n X E F length H J : M.Domain}
    (hH : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length H)
    (hJ : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length J) : H = J := by
  have ho : btruth_s.denote (btruth_env_l T n X E F) = BtruthStep_d T n X E F :=
    btruth_op_l hZF.1 (btruth_env_l T n X E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF))
      (btruth_s.denote (btruth_env_l T n X E F)) := by
    rw [ho]
    exact btruth_class_l hZF T n X E F
  exact ZF.recursiveSequence_unique hZF (kp_pair_l (ZF.modelsKP hZF))
    (btruth_env_l T n X E F) btruth_s hc
    (by simpa only [ho, BtruthEval_d] using hH) (by simpa only [ho, BtruthEval_d] using hJ)

/-- 逐行展开使用精确前缀，指令和真值行均为原图中的实际条目。 -/
theorem btruthEval_unfold_l (hKP : M.Models KP) {T n X E F length H r c Y : M.Domain}
    (hF : M.IsSetFunction (kp_pair_l hKP) F)
    (hH : BtruthEval_d (kp_pair_l hKP) T n X E F length H)
    (hc : Rd_entry_d r c F) (hY : Rd_entry_d r Y H) :
    ∃ P, M.IsRestrictionOf (kp_pair_l hKP) P H r ∧ Bdomain_d r P ∧
      ∀ f, M.mem f Y ↔ M.mem f E ∧ BtruthNode_d T n X E P c f := by
  have hr := (hH.1.2.2 r).mpr ⟨Y, hY⟩
  obtain ⟨P, hP, step⟩ := hH.2 r hr Y hY
  have hd := (hH.restriction hr hP).1.2.2
  refine ⟨P, hP, hd, fun f => (step f).trans (and_congr_right fun _ => ?_)⟩
  constructor
  · rintro ⟨k, d, hk, hkd, node⟩
    have eq := (show M.IsDomainOf (kp_pair_l hKP) k P from hk).eq hKP.1 hd
    subst k
    have eq := hF.2 r d c hkd hc
    subst d
    exact node
  · exact fun node => ⟨r, c, hd, hc, node⟩

theorem btruthEval_range_l (hKP : M.Models KP) {T n X E F length H r Y : M.Domain}
    (hH : BtruthEval_d (kp_pair_l hKP) T n X E F length H) (hY : Rd_entry_d r Y H) :
    M.MemberSubset Y E := by
  have hr := (hH.1.2.2 r).mpr ⟨Y, hY⟩
  obtain ⟨P, _, step⟩ := hH.2 r hr Y hY
  exact fun f hf => ((step f).mp hf).1

def BtruthSat_d (I : kpair_convention_l.Interpretation M) (T n X E F length r f : M.Domain) : Prop :=
  ∃ H Y, BtruthEval_d I T n X E F length H ∧ Rd_entry_d r Y H ∧ M.mem f Y

def btruthSat_m {d} (T n X E F length r f : Term d) : Formula 1 d :=
  .existsE <| .existsE <|
    .conj (btruthEval_m T.weaken.weaken n.weaken.weaken X.weaken.weaken E.weaken.weaken
      F.weaken.weaken length.weaken.weaken (.bound 1)) <|
      .conj (rd_entry_m r.weaken.weaken .newest (.bound 1)) (.mem f.weaken.weaken .newest)
derive_free_closed btruthSat_m

theorem btruthSat_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T n X E F length r f : Term d) :
    Formula.satisfies ρ (btruthSat_m T n X E F length r f) ↔
      BtruthSat_d (kp_pair_l hKP) (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ)
        (F.eval ρ) (length.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [btruthSat_m, BtruthSat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    btruthEval_sat_l hKP, rd_entry_sat_l hKP.1, Formula.satisfies_mem_iff,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem btruthSat_value_l (hZF : M.Models ZF) {T n X E F length H r Y : M.Domain}
    (hH : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length H)
    (hY : Rd_entry_d r Y H) (f : M.Domain) :
    BtruthSat_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length r f ↔ M.mem f Y := by
  constructor
  · rintro ⟨J, Z, hJ, hZ, hf⟩
    have eq := btruthEval_unique_l hZF hJ hH
    subst J
    exact hH.1.2.1.2 r Z Y hZ hY ▸ hf
  · exact fun hf => ⟨H, Y, hH, hY, hf⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
