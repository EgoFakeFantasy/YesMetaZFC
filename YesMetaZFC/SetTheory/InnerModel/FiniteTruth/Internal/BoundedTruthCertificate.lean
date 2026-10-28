import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthRows

/-! # 整张内部真值历史的有界核验

核验显式给出真值行容器 Z，并检查整个函数图、全部行的赋值界和完整递推方程。
Z 只约束实际历史的值域，不截断指令读取；同层存在预算仍须另证。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def BtruthCheck_d (T n X E F length Z H : M.Domain) : Prop :=
  Fn0_d length Z H ∧ ∀ r, M.mem r length → ∀ c, M.mem c T → Rd_entry_d r c F →
    ∀ Y, M.mem Y Z → Rd_entry_d r Y H → M.MemberSubset Y E ∧
      ∀ f, M.mem f E → (M.mem f Y ↔ BtruthNode_d T n X E H c f)

def btruthCheck_m {d} (T n X E F length Z H : Term d) : Formula 1 d :=
  .conj (fn0_m length Z H) <| Formula.forallMem length <| Formula.forallMem T.weaken <|
    .imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken) <| Formula.forallMem Z.weaken.weaken <|
      .imp (rd_entry0_m (.bound 2) .newest H.weaken.weaken.weaken) <|
        .conj (Formula.subset .newest E.weaken.weaken.weaken) <|
          Formula.forallMem E.weaken.weaken.weaken <|
            .iff (.mem .newest (.bound 1))
              (btruthNode_m T.weaken.weaken.weaken.weaken n.weaken.weaken.weaken.weaken
                X.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken
                H.weaken.weaken.weaken.weaken (.bound 2) .newest)
derive_free_closed btruthCheck_m

theorem btruthCheck_delta_l {d} (T n X E F length Z H : Term d) :
    (btruthCheck_m T n X E F length Z H).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.forallMem _ (.imp (rd_entry0_delta_l ..) (.conj (.atom _ _ _)
      (.forallMem _ (.iff (.mem _ _) (btruthNode_delta_l ..)))))))))

theorem btruthCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (T n X E F length Z H : Term d) :
    Formula.satisfies ρ (btruthCheck_m T n X E F length Z H) ↔
      BtruthCheck_d (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ)
        (length.eval ρ) (Z.eval ρ) (H.eval ρ) := by
  simp only [btruthCheck_m, BtruthCheck_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    btruthNode_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

/-- 完整有界核验在任意内部传递层中准确，不假定该层满足 KP。 -/
theorem btruthCheck_local_l (hE : Extensional M) {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C})
    (T n X E F length Z H : (rt_model_l C hn).Domain) :
    BtruthCheck_d T n X E F length Z H ↔
      BtruthCheck_d T.val n.val X.val E.val F.val length.val Z.val H.val := by
  let ρ : Env (rt_model_l C hn) 8 :=
    ⟨Fin.cases T (Fin.cases n (Fin.cases X (Fin.cases E (Fin.cases F
      (Fin.cases length (Fin.cases Z (fun _ => H))))))), fun _ => T⟩
  exact (btruthCheck_sat_l (rt_model_ext_l hE hc hn) ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)).symm.trans
    ((rt_model_delta_l hc hn (btruthCheck_delta_l _ _ _ _ _ _ _ _) ρ).trans
      (btruthCheck_sat_l hE (image_env_l Subtype.val ρ)
        (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)))

/-- 已有递归历史给出完整核验；Z 可以是任何包含全部实际行的容器。 -/
theorem btruthCheck_of_eval_l (hKP : M.Models KP) {T ω n X E F length Z H : M.Domain}
    (valid : BoundedFormula_d T ω n length F)
    (hH : BtruthEval_d (kp_pair_l hKP) T n X E F length H) (fn : Fn0_d length Z H) :
    BtruthCheck_d T n X E F length Z H := by
  refine ⟨fn, fun r hr c hc hrc Y _ hY => ⟨btruthEval_range_l hKP hH hY, ?_⟩⟩
  have row := btruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 hH hrc hY
    (valid.row r hr c hc hrc)
  exact fun f hf => (row f).trans (and_iff_right hf)

/-- 完整核验反向给出原递归历史；前缀是原 ZF 中的实际限制图。 -/
theorem btruthEval_of_check_l (hZF : M.Models ZF) {T ω n X E F length Z H : M.Domain}
    (valid : BoundedFormula_d T ω n length F) (check : BtruthCheck_d T n X E F length Z H) :
    BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length H := by
  let hKP := ZF.modelsKP hZF
  have fn := fn0_function_l hKP check.1
  have seq : M.IsSequenceOfLength (kp_pair_l hKP) H length := ⟨valid.ordinal, fn.1, fn.2.1⟩
  refine ⟨seq, fun r hr Y hY => ?_⟩
  obtain ⟨c, hc, hrc⟩ := valid.graph.2.1 r hr
  obtain ⟨P, hp⟩ := ZF.exists_restriction hZF (kp_pair_l hKP) H r
  have hd := (seq.restriction hr hp).2.2
  obtain ⟨sub, row⟩ := check.2 r hr c hc hrc Y (check.1.bound_l hY).2 hY
  have atRow (f : M.Domain) : BtruthAt_d T n X E F P f ↔ BtruthNode_d T n X E P c f := by
    constructor
    · rintro ⟨k, d, hk, hkd, node⟩
      have eq := (show M.IsDomainOf (kp_pair_l hKP) k P from hk).eq hZF.1 hd
      subst k
      have eq := (fn0_function_l hKP valid.graph).1.2 r d c hkd hrc
      subst d
      exact node
    · exact fun node => ⟨r, c, hd, hrc, node⟩
  refine ⟨P, hp, fun f => ?_⟩
  have value : M.mem f Y ↔ M.mem f E ∧ BtruthNode_d T n X E H c f :=
    ⟨fun hy => ⟨sub f hy, (row f (sub f hy)).mp hy⟩,
      fun ⟨hf, node⟩ => (row f hf).mpr node⟩
  exact value.trans (and_congr_right fun _ =>
    (btruthNode_restriction_l hKP hp (valid.row r hr c hc hrc)).symm.trans (atRow f).symm)

/-- 有效内部程序上的核验规格与整张原递归历史准确等价。 -/
theorem btruthCheck_correct_l (hZF : M.Models ZF) {T ω n X E F length Z H : M.Domain}
    (valid : BoundedFormula_d T ω n length F) :
    BtruthCheck_d T n X E F length Z H ↔ Fn0_d length Z H ∧
      BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F length H :=
  ⟨fun check => ⟨check.1, btruthEval_of_check_l hZF valid check⟩,
    fun ⟨fn, eval⟩ => btruthCheck_of_eval_l (ZF.modelsKP hZF) valid eval fn⟩

/-- 整张操作历史与其实际行容器都在背景中存在，不假设小 J 层资格。 -/
theorem btruthCertificate_exists_l (hZF : M.Models ZF) {T ω n X E F length : M.Domain}
    (valid : BoundedFormula_d T ω n length F) :
    ∃ Z H, BtruthCheck_d T n X E F length Z H := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨H, hH⟩ := btruthEval_exists_l hZF T n X E F valid.ordinal
  obtain ⟨Z, hZ⟩ := rd_fun_exists_l hKP .range H H H
  have fn : Fn0_d length Z H := fn0_of_function_l hKP ⟨hH.1.2.1, hH.1.2.2, fun r hr => by
    obtain ⟨Y, hY⟩ := (hH.1.2.2 r).mp hr
    exact ⟨Y, (hZ Y).mpr ⟨r, hY⟩, hY⟩⟩
  exact ⟨Z, H, btruthCheck_of_eval_l hKP valid hH fn⟩

/-- 行容器可以不同，完整历史图仍由合法程序唯一确定。 -/
theorem btruthCertificate_unique_l (hZF : M.Models ZF) {T ω n X E F length Z H W J : M.Domain}
    (valid : BoundedFormula_d T ω n length F)
    (hh : BtruthCheck_d T n X E F length Z H) (hj : BtruthCheck_d T n X E F length W J) : H = J :=
  btruthEval_unique_l hZF (btruthEval_of_check_l hZF valid hh) (btruthEval_of_check_l hZF valid hj)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
