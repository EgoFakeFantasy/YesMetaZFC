import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless.CollapseIsomorphism
import YesMetaZFC.SetTheory.InnerModel.Separation.Formula

/-! # 整张塌缩图的有界核验

在给定传递值域和完整函数图上，所有值方程只需在值域内核对。
图的定义域、值域完整性和全部方程一并核验，避免把截断方程当成真实塌缩。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def CollapseCheck_d (X R T F : M.Domain) : Prop :=
  Fn0_d X T F ∧ M.TransitiveSet T ∧
    (∀ y, M.mem y T → ∃ a, M.mem a X ∧ Rd_entry_d a y F) ∧
    ∀ a, M.mem a X → ∀ x, M.mem x T → Rd_entry_d a x F →
      ∀ y, M.mem y T → (M.mem y x ↔
        ∃ b, M.mem b X ∧ Rd_entry_d b a R ∧ Rd_entry_d b y F)

def collapseCheck_m {n} (X R T F : Project.Term n) : Formula 1 n :=
  .conj (fn0_m X T F) <| .conj (Formula.isTransitive T) <| .conj
    (Formula.forallMem T (Formula.existsMem X.weaken
      (rd_entry0_m .newest (.bound 1) F.weaken.weaken)))
    (Formula.forallMem X <| Formula.forallMem T.weaken <|
      .imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken) <|
        Formula.forallMem T.weaken.weaken <|
          .iff (.mem .newest (.bound 1)) <| Formula.existsMem X.weaken.weaken.weaken <|
            .conj (rd_entry0_m .newest (.bound 3) R.weaken.weaken.weaken.weaken)
              (rd_entry0_m .newest (.bound 1) F.weaken.weaken.weaken.weaken))
derive_free_closed collapseCheck_m

theorem collapseCheck_delta_l {n} (X R T F : Project.Term n) :
    (collapseCheck_m X R T F).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (Formula.isTransitive_delta0 _) (.conj
    (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
      (.forallMem _ (.iff (.mem _ _) (.existsMem _
        (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))

theorem collapseCheck_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R T F : Project.Term n) :
    Formula.satisfies ρ (collapseCheck_m X R T F) ↔
      CollapseCheck_d (X.eval ρ) (R.eval ρ) (T.eval ρ) (F.eval ρ) := by
  simp only [collapseCheck_m, CollapseCheck_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 有界核验恰好表达完整真实塌缩及精确传递值域。 -/
theorem collapseCheck_correct_l {X R T F : M.Domain} :
    CollapseCheck_d X R T F ↔ Fn0_d X T F ∧ Wc_graph_d X R F ∧
      M.TransitiveSet T ∧ (∀ y, M.mem y T ↔ ∃ a, Rd_entry_d a y F) := by
  constructor
  · rintro ⟨fn, ht, onto, step⟩
    refine ⟨fn, ⟨?_, ?_⟩, ht, ?_⟩
    · intro p hp
      obtain ⟨a, _, x, _, hpa⟩ := fn.1 p hp
      exact ⟨a, x, hpa⟩
    · intro a x hax
      have ax := fn.bound_l hax
      refine ⟨ax.1, fun b hb _ => (fn.2.1 b hb).imp fun _ h => h.2, fun y => ?_⟩
      constructor
      · intro hy
        exact (step a ax.1 x ax.2 hax y (ht x ax.2 y hy)).mp hy
      · rintro ⟨b, hb, hba, hby⟩
        exact (step a ax.1 x ax.2 hax y (fn.bound_l hby).2).mpr ⟨b, hb, hba, hby⟩
    · intro y
      exact ⟨fun hy => (onto y hy).imp fun _ h => h.2,
        fun ⟨a, hay⟩ => (fn.bound_l hay).2⟩
  · rintro ⟨fn, hg, ht, range⟩
    refine ⟨fn, ht, ?_, fun a _ x _ hax y _ => (hg.2 a x hax).2.2 y⟩
    intro y hy
    obtain ⟨a, hay⟩ := (range y).mp hy
    exact ⟨a, (fn.bound_l hay).1, hay⟩

/-- 同一完整有界证书在任意传递子结构中准确。 -/
theorem collapseCheck_local_l (hE : Extensional M) {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C})
    (X R T F : (rt_model_l C hn).Domain) :
    CollapseCheck_d X R T F ↔ CollapseCheck_d X.val R.val T.val F.val := by
  let ρ : Env (rt_model_l C hn) 4 :=
    ⟨Fin.cases X (Fin.cases R (Fin.cases T (fun _ => F))), fun _ => X⟩
  exact (collapseCheck_sat_l (rt_model_ext_l hE hc hn) ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3)).symm.trans
    ((rt_model_delta_l hc hn (collapseCheck_delta_l _ _ _ _) ρ).trans
      (collapseCheck_sat_l hE (image_env_l Subtype.val ρ)
        (.bound 0) (.bound 1) (.bound 2) (.bound 3)))

/-- 在弱背景理论中，完整有界塌缩证书唯一，包括其值域。 -/
theorem collapseCheck_unique_l (hP : M.Models ZFMinus) {X R T F U G : M.Domain}
    (hf : CollapseCheck_d X R T F) (hg : CollapseCheck_d X R U G) : T = U ∧ F = G := by
  obtain ⟨fn, wf, _, rangeF⟩ := collapseCheck_correct_l.mp hf
  obtain ⟨gn, wg, _, rangeG⟩ := collapseCheck_correct_l.mp hg
  have eq := wc_total_graph_unique_l hP (wf_of_collapse_l hP fn wf) fn gn wf wg
  subst G
  exact ⟨hP.1.eq_of_same_members T U (fun y => (rangeF y).trans (rangeG y).symm), rfl⟩

/-- 层内证书与任意背景证书确定同一实际图和值域。 -/
theorem collapseCheck_up_unique_l (hP : M.Models ZFMinus) {C : M.Domain}
    (hc : M.TransitiveSet C) (hn : Nonempty {x : M.Domain // M.mem x C})
    (X R T F : (rt_model_l C hn).Domain) {U G : M.Domain}
    (hl : CollapseCheck_d X R T F) (hh : CollapseCheck_d X.val R.val U G) :
    T.val = U ∧ F.val = G :=
  collapseCheck_unique_l hP ((collapseCheck_local_l hP.1 hc hn X R T F).mp hl) hh

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
