import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthCertificate
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded

/-! # 真值递归一步的同层构造

函数图的值界把下一条指令的搜索变为有界搜索；精确历史定义域消去无界的行搜索。
同层分离只使用 rud 闭包、传递性与逐参数的实际传递包络，不假设层内 KP。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def BtruthRow_d (T n X E F r H f : M.Domain) : Prop :=
  ∃ c, M.mem c T ∧ Rd_entry_d r c F ∧ BtruthNode_d T n X E H c f

def btruthRow_m {d} (T n X E F r H f : Term d) : Formula 1 d :=
  Formula.existsMem T (.conj (rd_entry0_m r.weaken .newest F.weaken)
    (btruthNode_m T.weaken n.weaken X.weaken E.weaken H.weaken .newest f.weaken))
derive_free_closed btruthRow_m

theorem btruthRow_delta_l {d} (T n X E F r H f : Term d) :
    (btruthRow_m T n X E F r H f).IsDelta0 :=
  .existsMem _ (.conj (rd_entry0_delta_l ..) (btruthNode_delta_l ..))

theorem btruthRow_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T n X E F r H f : Term d) :
    Formula.satisfies ρ (btruthRow_m T n X E F r H f) ↔
      BtruthRow_d (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (r.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [btruthRow_m, BtruthRow_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, btruthNode_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 历史的准确定义域和程序的全局值界使下一步关系成为实际有界矩阵。 -/
theorem btruthAt_row_l (hKP : M.Models KP) {T n X E F r H f : M.Domain}
    (bound : ∀ i c, Rd_entry_d i c F → M.mem c T) (hd : Bdomain_d r H) :
    BtruthAt_d T n X E F H f ↔ BtruthRow_d T n X E F r H f := by
  constructor
  · rintro ⟨k, c, hk, hkc, node⟩
    have eq := (show M.IsDomainOf (kp_pair_l hKP) k H from hk).eq hKP.1 hd
    subst k
    exact ⟨c, bound r c hkc, hkc, node⟩
  · rintro ⟨c, _, hrc, node⟩
    exact ⟨r, c, hd, hrc, node⟩

/-- 参数逐个有同层传递包络时，任意固定有界分离集留在该 rud 闭包。 -/
theorem rd_locally_enclosed_separation_l (hKP : M.Models KP) {C X : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    {d} (φ : Delta0UnarySchema d) (ρ : Env M d) (hρ : ∀ i, M.mem (ρ.bound i) C) (hX : M.mem X C) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  obtain ⟨U, hUC, hu, hXU⟩ := cover X hX
  obtain ⟨V, hVC, hv, uv, params⟩ := rd_finite_enclosed_l hKP hC hUC hu (List.ofFn ρ.bound) (by
    intro A hA
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact cover (ρ.bound i) (hρ i))
  exact rd_separation_l hKP hC hc hVC hv φ ρ
    (fun i => params _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) (uv X hXU)

/-- 下一真值集是同层实际分离集；这里不使用层内 Collection。 -/
theorem rd_btruthStep_exists_l (hKP : M.Models KP) {C T n X E F r H : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    (hTC : M.mem T C) (hnC : M.mem n C) (hXC : M.mem X C) (hEC : M.mem E C)
    (hFC : M.mem F C) (hrC : M.mem r C) (hHC : M.mem H C)
    (bound : ∀ i c, Rd_entry_d i c F → M.mem c T) (hd : Bdomain_d r H) :
    ∃ Y, M.mem Y C ∧ BtruthStep_d T n X E F H Y := by
  let ρ := ((btruth_env_l T n X E F).push r).push H
  let φ : Delta0UnarySchema 7 := {
    body := btruthRow_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := btruthRow_delta_l .. }
  have params : ∀ i, M.mem (ρ.bound i) C :=
    Fin.cases hHC (Fin.cases hrC (Fin.cases hFC (Fin.cases hEC
      (Fin.cases hXC (Fin.cases hnC (fun _ => hTC))))))
  obtain ⟨Y, hYC, hY⟩ := rd_locally_enclosed_separation_l hKP hC hc cover φ ρ params hEC
  have row (f : M.Domain) : φ.toUnarySchema.denote ρ f ↔ BtruthRow_d T n X E F r H f := by
    simp only [φ, UnarySchema.denote, btruthRow_sat_l hKP.1]
    rfl
  exact ⟨Y, hYC, fun f => (hY f).trans (and_congr_right fun _ =>
    (row f).trans (btruthAt_row_l hKP bound hd).symm)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
