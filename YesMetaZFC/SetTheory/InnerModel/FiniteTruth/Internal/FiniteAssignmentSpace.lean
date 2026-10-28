import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteAssignmentStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 全部内部有限长度的同层赋值空间

自然数归纳的谓词是实际原公式，并以背景 ZF 的分离构造归纳集。结论覆盖模型
内部的所有 n∈ω，不把长度替换成宿主 Nat，也不预设层内 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

@[simp] theorem functionSpace_closed_l {d} (E n X : Term d)
    (hE : E.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l E n X).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace,
    YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, hE, hn, hX]

def finiteSpace_m {d} (C n X : Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest C.weaken)
    (Formula.isFunctionSpace kpair_convention_l .newest n.weaken X.weaken))
derive_free_closed finiteSpace_m

theorem finiteSpace_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (C n X : Term d) :
    Formula.satisfies ρ (finiteSpace_m C n X) ↔
      ∃ E, M.mem E (C.eval ρ) ∧
        M.IsFunctionSpace (kp_pair_l hKP) E (n.eval ρ) (X.eval ρ) := by
  simp only [finiteSpace_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isFunctionSpace_iff (kp_pair_l hKP) hKP.1,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 空定义域上只有空函数，与值域是否非空无关。 -/
theorem empty_functionSpace_l (hKP : M.Models KP) {e S X : M.Domain}
    (he : ∀ p, ¬ M.mem p e) (hS : M.IsSingletonOf S e) :
    M.IsFunctionSpace (kp_pair_l hKP) S e X := by
  let I := kp_pair_l hKP
  have emptyFn : M.IsSetFunctionFromTo I e e X :=
    ⟨(Structure.IsSequenceOfLength.empty I he).2.1,
      (Structure.IsSequenceOfLength.empty I he).2.2, fun i hi => (he i hi).elim⟩
  intro f
  constructor
  · intro hf
    have eq := (hS f).mp hf
    exact eq ▸ emptyFn
  · intro hf
    have hempty (p : M.Domain) (hp : M.mem p f) : False := by
      obtain ⟨i, x, hpx⟩ := hf.1.1 p hp
      exact he i (hf.input_mem_of_pairMember ⟨p, hpx, hp⟩)
    have eq := hKP.1.eq_of_same_members f e (fun p => iff_of_false (hempty p) (he p))
    exact (hS f).mpr eq

/-- 任意内部有限函数空间都留在原 rud 闭包中。 -/
theorem rd_finite_functionSpace_l (hZF : M.Models ZF) {C A ω X : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C) (hA : M.mem A C) (ha : M.TransitiveSet A)
    (hω : M.IsOmega ω) (hωA : M.mem ω A) (hXA : M.mem X A) :
    ∀ n, M.mem n ω → ∃ E, M.mem E C ∧
      M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  let ρ : Env M 2 := ⟨Fin.cases C (fun _ => X), fun _ => C⟩
  let φ : UnarySchema 2 := { body := finiteSpace_m (.bound 1) .newest (.bound 2) }
  have sat n : φ.denote ρ n ↔ ∃ E, M.mem E C ∧ M.IsFunctionSpace I E n X := by
    simp only [φ, UnarySchema.denote, finiteSpace_sat_l hKP]
    rfl
  apply hω.induction (fun n => ∃ E, M.mem E C ∧ M.IsFunctionSpace I E n X)
  · obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨S, fun n => (hS n).trans (and_congr_right fun _ => sat n)⟩
  · intro e he
    have heC : M.mem e C := hC .diff A A A hA hA hA e
      (fun p => iff_of_false (he p) (fun h => h.2 h.1))
    obtain ⟨S, hSC, hS⟩ := hC.exists_l hKP .pair heC heC heC
    exact ⟨S, hSC, empty_functionSpace_l hKP he
      (fun p => (hS p).trans ⟨fun h => h.elim id id, Or.inl⟩)⟩
  · intro n hn ih s hns
    obtain ⟨E, hEC, hE⟩ := ih
    have nA := ha ω hωA n hn
    obtain ⟨T, hTC, ht, hET⟩ := rd_functionSpace_enclosed_l hKP hC hA ha hEC
      (fun i hi => ha n nA i hi) (fun x hx => ha X hXA x hx) hE
    obtain ⟨B, hBC, hB⟩ := hC.union_l hKP hA hTC
    have hb : M.TransitiveSet B := by
      intro x hx y hy
      exact (hB y).mpr (((hB x).mp hx).elim
        (fun h => Or.inl (ha x h y hy)) (fun h => Or.inr (ht x h y hy)))
    have hnOrd := hω.members_areOrdinals hZF n hn
    exact rd_functionSpace_succ_l hZF hC hc hBC hb
      ((hB E).mpr (Or.inr hET)) ((hB X).mpr (Or.inl hXA)) ((hB n).mpr (Or.inl nA))
      hnOrd (KP.successor_isOrdinal hKP hnOrd hns) hns hE

private def finiteSpaceBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (rd_closed_m (.bound 3)) <| .imp (Formula.isTransitive (.bound 3)) <|
      .imp (.mem (.bound 2) (.bound 3)) <| .imp (Formula.isTransitive (.bound 2)) <|
        .imp (.mem (.bound 1) (.bound 2)) <| .imp (.mem .newest (.bound 2)) <|
          .imp (Formula.isOmega (.bound 1)) <| Formula.forallMem (.bound 1) <|
            finiteSpace_m (.bound 4) .newest (.bound 1)

/-- 对全部内部自然数统一的同层赋值空间闭句。 -/
def finiteAssignmentSpaces : Sentence := .ofFormula finiteSpaceBody
  (by simp -implicitDefEqProofs [finiteSpaceBody, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed])

theorem finiteAssignmentSpaces_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence finiteAssignmentSpaces := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0) finiteSpaceBody
  simp only [finiteSpaceBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forallMem_iff, rd_closed_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_isTransitive_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isOmega_iff, finiteSpace_sat_l (ZF.modelsKP hZF)]
  intro C A ω X hC hc hA ha hωA hXA hω n hn
  exact rd_finite_functionSpace_l hZF hC hc hA ha hω hωA hXA n hn

/-- 原 ZF 推导核中的统一内部有限赋值空间定理。 -/
theorem finiteAssignmentSpaces_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF finiteAssignmentSpaces :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => finiteAssignmentSpaces_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
