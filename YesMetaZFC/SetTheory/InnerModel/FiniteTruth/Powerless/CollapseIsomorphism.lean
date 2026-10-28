import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless.CollapseExistence

/-! # 编码外延关系的塌缩同构与唯一性

同值节点的相等由实际公式的内部关系归纳证明；不借助宿主良基递归。
总图唯一性随后用于比较不同传递模型中构造的塌缩图。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} (hP : M.Models ZFMinus) {X R : M.Domain}

def ExtensionalRelation_d (X R : M.Domain) : Prop :=
  ∀ a, M.mem a X → ∀ b, M.mem b X →
    (∀ c, M.mem c X → (Rd_entry_d c a R ↔ Rd_entry_d c b R)) → a = b

include hP

/-- 内部良基外延关系的总塌缩图是单射。 -/
theorem wc_injective_l (hw : Wf_rel_d X R) (he : ExtensionalRelation_d X R)
    {T F : M.Domain} (fn : Fn0_d X T F) (hg : Wc_graph_d X R F) :
    ∀ a b y, Rd_entry_d a y F → Rd_entry_d b y F → a = b := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push F
  let φ : UnarySchema 2 := {
    body := Formula.forallMem (.bound 2) (.forallE (.imp
      (.conj (rd_entry_m (.bound 2) .newest (.bound 3))
        (rd_entry_m (.bound 1) .newest (.bound 3)))
      (Formula.extensionalEq (.bound 2) (.bound 1)))) }
  have sat a : φ.denote ρ a ↔ ∀ b, M.mem b X → ∀ y,
      Rd_entry_d a y F ∧ Rd_entry_d b y F → a = b := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hP.1, Formula.satisfies_extensionalEq_iff_eq hP.1]
    rfl
  have all := wf_rel_ind_l hP hw φ ρ (fun a ha ih => (sat a).mpr (by
    rintro b hb y ⟨hay, hby⟩
    apply he a ha b hb
    intro c hc
    constructor
    · intro hca
      obtain ⟨z, _, hcz⟩ := fn.2.1 c hc
      have hzy := ((hg.2 a y hay).2.2 z).mpr ⟨c, hc, hca, hcz⟩
      obtain ⟨d, hd, hdb, hdz⟩ := ((hg.2 b y hby).2.2 z).mp hzy
      have eq := (sat c).mp (ih c hc hca) d hd z ⟨hcz, hdz⟩
      exact eq.symm ▸ hdb
    · intro hcb
      obtain ⟨z, _, hcz⟩ := fn.2.1 c hc
      have hzy := ((hg.2 b y hby).2.2 z).mpr ⟨c, hc, hcb, hcz⟩
      obtain ⟨d, hd, hda, hdz⟩ := ((hg.2 a y hay).2.2 z).mp hzy
      have eq := (sat d).mp (ih d hd hda) c hc z ⟨hdz, hcz⟩
      exact eq ▸ hda))
  intro a b y hay hby
  exact (sat a).mp (all a (fn.bound_l hay).1) b (fn.bound_l hby).1 y ⟨hay, hby⟩

/-- 单射塌缩图同时保持和反映原编码关系。 -/
theorem wc_member_iff_l (hw : Wf_rel_d X R) (he : ExtensionalRelation_d X R)
    {T F a b x y : M.Domain} (fn : Fn0_d X T F) (hg : Wc_graph_d X R F)
    (hax : Rd_entry_d a x F) (hby : Rd_entry_d b y F) :
    Rd_entry_d a b R ↔ M.mem x y := by
  constructor
  · intro hab
    exact ((hg.2 b y hby).2.2 x).mpr ⟨a, (fn.bound_l hax).1, hab, hax⟩
  · intro hxy
    obtain ⟨c, _, hcb, hcx⟩ := ((hg.2 b y hby).2.2 x).mp hxy
    exact (wc_injective_l hP hw he fn hg a c x hax hcx).symm ▸ hcb

/-- 两张全域塌缩图逐点相容，因而是同一个实际集合。 -/
theorem wc_total_graph_unique_l (hw : Wf_rel_d X R) {T U F G : M.Domain}
    (fn : Fn0_d X T F) (gn : Fn0_d X U G)
    (hf : Wc_graph_d X R F) (hg : Wc_graph_d X R G) : F = G := by
  have sub {T U F G : M.Domain} (fn : Fn0_d X T F) (gn : Fn0_d X U G)
      (hf : Wc_graph_d X R F) (hg : Wc_graph_d X R G) : M.MemberSubset F G := by
    intro p hp
    obtain ⟨a, ha, x, _, hpa⟩ := fn.1 p hp
    obtain ⟨y, _, hay⟩ := gn.2.1 a ha
    have eq := wc_value_unique_l hP hw ⟨F, hf, p, hpa, hp⟩ ⟨G, hg, hay⟩
    have hax : Rd_entry_d a x G := eq.symm ▸ hay
    obtain ⟨q, hqa, hq⟩ := hax
    exact (kpair_unique_l M hP.1 hpa hqa).symm ▸ hq
  exact hP.1.eq_of_same_members F G (fun p => ⟨sub fn gn hf hg p, sub gn fn hg hf p⟩)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
