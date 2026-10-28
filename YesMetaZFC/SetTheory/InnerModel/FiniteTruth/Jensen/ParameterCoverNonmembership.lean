import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruthHistory

/-! # 全参数覆盖集合的非成员性

仅使用实际双层 Kuratowski 条目、同层传递包络与背景 Foundation。
此结论不声称小域分离失败或主编码资格。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def ParameterCover_d (C T : M.Domain) : Prop :=
  ∀ x, M.mem x C → ∃ input params c i,
    M.mem input T ∧ KPair_d M input c params ∧ Rd_entry_d i x params

def parameterCover_m {n} (C T : Term n) : Formula 1 n :=
  Formula.forallMem C <| .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (.mem (.bound 3) T.weaken.weaken.weaken.weaken.weaken) <|
      .conj (kpair0_m (.bound 3) (.bound 1) (.bound 2))
        (rd_entry_m .newest (.bound 4) (.bound 2))

@[simp] theorem parameterCover_closed_l {n} (C T : Term n)
    (hC : C.freeSupport = []) (hT : T.freeSupport = []) :
    (parameterCover_m C T).FreeClosed := by
  simp -implicitDefEqProofs [parameterCover_m,hC,hT,Definitional.Formula.FreeClosed]

theorem parameterCover_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C T : Term n) :
    Formula.satisfies ρ (parameterCover_m C T) ↔ ParameterCover_d (C.eval ρ) (T.eval ρ) := by
  simp only [parameterCover_m,ParameterCover_d,Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    kpair0_sat_l hE,rd_entry_sat_l hE,Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest,Term.eval_bound] <;> rfl

theorem parameterCover_not_mem_l (hKP : M.Models KP) {C T : M.Domain}
    (enclosure : ∀ x, M.mem x C → ∃ V, M.mem V C ∧ M.TransitiveSet V ∧ M.mem x V)
    (cover : ParameterCover_d C T) : ¬ M.mem T C := by
  intro hTC
  obtain ⟨V,hVC,trans,hTV⟩ := enclosure T hTC
  obtain ⟨input,params,c,i,hit,pair,entry⟩ := cover V hVC
  have hinV := trans T hTV input hit
  have hpV := (po_pair_bound_l trans hinV pair).2
  obtain ⟨q,entryPair,hq⟩ := entry
  have hqV := trans params hpV q hq
  exact KP.mem_irrefl_d hKP V (po_pair_bound_l trans hqV entryPair).2

theorem jh_parameterCover_not_mem_l (hZF : M.Models ZF) {α C T : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (cover : ParameterCover_d C T) : ¬ M.mem T C :=
  parameterCover_not_mem_l (ZF.modelsKP hZF) (jh_local_enclosure_l (ZF.models_kpi_l hZF) hα hC) cover

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
