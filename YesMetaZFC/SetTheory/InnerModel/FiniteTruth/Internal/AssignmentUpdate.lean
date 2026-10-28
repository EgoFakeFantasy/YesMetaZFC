import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteAssignmentSpace
import YesMetaZFC.Model.SetTheory.Internal.Assignment

/-! # 有限赋值的有界更新核验

已给出完整有限赋值空间时，只需在有限变量域与对象域上双向检查更新方程。
候选更新仍属于同一赋值空间；核验公式携带实际 Δ₀ 证书。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}

def UpdateCheck_d (I : 𝒞.Interpretation M) (n X f i x g : M.Domain) : Prop :=
  ∀ j, M.mem j n → ∀ y, M.mem y X →
    (M.PairMember I j y g ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ M.PairMember I j y f))

def updateCheck_m {d} (n X f i x g : Term d) : Formula 1 d :=
  Formula.forallMem n <| Formula.forallMem X.weaken <|
    .iff (rd_entry0_m (.bound 1) .newest g.weaken.weaken) <|
      .disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken)
        (Formula.extensionalEq .newest x.weaken.weaken))
        (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken))
          (rd_entry0_m (.bound 1) .newest f.weaken.weaken))
derive_free_closed updateCheck_m

theorem updateCheck_delta_l {d} (n X f i x g : Term d) :
    (updateCheck_m n X f i x g).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _))
      (.conj (.neg (.atom _ _ _)) (rd_entry0_delta_l ..)))))

theorem updateCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (n X f i x g : Term d) :
    Formula.satisfies ρ (updateCheck_m n X f i x g) ↔
      UpdateCheck_d (kp_pair_l hKP) (n.eval ρ) (X.eval ρ) (f.eval ρ)
        (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [updateCheck_m, UpdateCheck_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1, rd_entry0_sat_l hKP.1,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

/-- 合法赋值之间，有界核验恰好等价于原完整更新方程。 -/
theorem updateCheck_correct_l (I : 𝒞.Interpretation M) {n X f i x g : M.Domain}
    (hf : M.IsSetFunctionFromTo I f n X) (hg : M.IsSetFunctionFromTo I g n X)
    (hi : M.mem i n) (hx : M.mem x X) :
    UpdateCheck_d I n X f i x g ↔ SetTheory.Internal.Senv_update_d I f i x g := by
  constructor
  · intro h
    refine ⟨hg.1.1, fun j y => ?_⟩
    by_cases good : M.mem j n ∧ M.mem y X
    · exact h j good.1 y good.2
    · apply iff_of_false
      · intro hjy
        exact good ⟨hg.input_mem_of_pairMember hjy, hg.output_mem_of_pairMember hjy⟩
      · rintro (⟨rfl, rfl⟩ | ⟨_, hjy⟩)
        · exact good ⟨hi, hx⟩
        · exact good ⟨hf.input_mem_of_pairMember hjy, hf.output_mem_of_pairMember hjy⟩
  · intro h j _ y _
    exact h.2 j y

/-- 更新对象确实存在，并留在原完整赋值空间中。 -/
theorem finite_update_exists_l (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {E n X f i x : M.Domain} (hE : M.IsFunctionSpace I E n X)
    (hf : M.mem f E) (hi : M.mem i n) (hx : M.mem x X) :
    ∃ g, M.mem g E ∧ SetTheory.Internal.Senv_update_d I f i x g ∧ UpdateCheck_d I n X f i x g := by
  obtain ⟨g, hg, hgn⟩ := SetTheory.Internal.senv_update_exists_l I hZF ((hE f).mp hf) hi hx
  exact ⟨g, (hE g).mpr hgn, hg, (updateCheck_correct_l I ((hE f).mp hf) hgn hi hx).mpr hg⟩

/-- 全部内部有限长度下，原赋值及其更新都属于同一个同层空间。 -/
theorem rd_finite_update_l (hZF : M.Models ZF) {C A ω X : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C) (hA : M.mem A C) (ha : M.TransitiveSet A)
    (hω : M.IsOmega ω) (hωA : M.mem ω A) (hXA : M.mem X A)
    {n f i x : M.Domain} (hn : M.mem n ω)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (hi : M.mem i n) (hx : M.mem x X) :
    ∃ E g, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X ∧
      M.mem f E ∧ M.mem g E ∧ UpdateCheck_d (kp_pair_l (ZF.modelsKP hZF)) n X f i x g := by
  obtain ⟨E, hEC, hE⟩ := rd_finite_functionSpace_l hZF hC hc hA ha hω hωA hXA n hn
  have hfE := (hE f).mpr hf
  obtain ⟨g, hgE, _, hg⟩ := finite_update_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hE hfE hi hx
  exact ⟨E, g, hEC, hE, hfE, hgE, hg⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
