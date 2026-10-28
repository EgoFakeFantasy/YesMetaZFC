import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentRealization
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteAssignmentSpace

/-! # 原同一 Jensen 层中的框架与赋值

规范数码和整个有限寄存器向量都在原层内。完整赋值空间只构造一次，
随后每个源环境的实际赋值图均属于该空间，不要求小层满足 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_registerFrame_l (hZF : M.Models ZF) (k : Nat) {a C ω : M.Domain}
    (_ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ n, ∃ v : Fin k → M.Domain, M.mem n C ∧ RegisterFrame_d k n v ∧ ∀ i, M.mem (v i) C := by
  obtain ⟨n,v,frame⟩ := registerFrame_exists_l (ZF.modelsKP hZF) k
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  exact ⟨n,v,trans ω hωC n (frame.omega_l hZF.1 hω),frame,
    fun i => trans ω hωC (v i) (num_mem_l hZF.1 hω (frame.slots i))⟩

/-- 一份同层完整空间同时包含每个域内源环境的实际实现。 -/
theorem jh_assignment_realize_l (hZF : M.Models ZF) {d} (v : Fin d → M.Domain)
    {a C ω n X default : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hXC : M.mem X C) (hn : M.mem n ω)
    (bound : ∀ i, M.mem (v i) n) (injective : Function.Injective v) (inhabited : M.mem default X) :
    ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X ∧
      ∀ σ : Fin d → M.Domain, (∀ i, M.mem (σ i) X) →
        ∃ f, M.mem f E ∧ M.mem f C ∧ Fn0_d n X f ∧ ∀ i, Rd_entry_d (v i) (σ i) f := by
  obtain ⟨E,hEC,full⟩ := jh_finite_functionSpace_l hZF ha h hω hωC hXC n hn
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  refine ⟨E,hEC,full,fun σ values => ?_⟩
  obtain ⟨f,fn,corr⟩ := assignment_realize_l hZF v σ bound injective values inhabited
  have hfE := (full f).mpr (fn0_function_l (ZF.modelsKP hZF) fn)
  exact ⟨f,hfE,trans E hEC f hfE,fn,corr⟩

private def jensenRegisterFrameBody (k : Nat) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 2)) <| .imp (jh_value_m (.bound 2) (.bound 1)) <|
      .imp (Formula.isOmega .newest) <| .imp (.mem .newest (.bound 1)) <|
        .existsE <| .conj (.mem .newest (.bound 2)) <| existsBlock_m k <|
          .conj (registerFrame_m k (oldTerm_m (.bound 0 : Term 4)) (fun i => sourceTerm_m 4 i))
            (finConj_m k (fun i => .mem (sourceTerm_m 4 i) (oldTerm_m (.bound 2 : Term 4))))

def jensenRegisterFrame (k : Nat) : Sentence := .ofFormula (jensenRegisterFrameBody k)
  (by simp -implicitDefEqProofs [jensenRegisterFrameBody,registerFrame_closed_l,sourceTerm_m,Definitional.Formula.FreeClosed])

theorem jensenRegisterFrame_models (k : Nat) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenRegisterFrame k) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (jensenRegisterFrameBody k)
  simp only [jensenRegisterFrameBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    existsBlock_sat_l,registerFrame_sat_l hZF.1,finConj_sat_l,oldTerm_eval_l,sourceTerm_eval_l]
  intro a C ω ha h hω hωC
  obtain ⟨n,v,hnC,frame,slots⟩ := jh_registerFrame_l hZF k ha h hω hωC
  exact ⟨n,hnC,v,frame,slots⟩

theorem jensenRegisterFrame_derives (k : Nat) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenRegisterFrame k) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenRegisterFrame_models k M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
