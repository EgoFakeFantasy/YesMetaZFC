import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LocalObjectTheorem
import YesMetaZFC.SetTheory.ProductConstruction
import YesMetaZFC.SetTheory.Separation

/-! # 固定原 Σ₁ 源的实际受限编码真值集合

集合由背景 ZF 在完整原笛卡尔积上分离得到。完整原见证受 C 约束；不假设
该集合属于 C，也不假设 C 的集合论公理或主编码资格。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def RestrictedTruthDomain_d {n} (φ : S1_binary n) (ρ : Env M n) (C input : M.Domain) : Prop :=
  ∃ y, M.mem y C ∧ Within_d φ ρ input y C

def restrictedTruthDomain_m {n d} (φ : S1_binary n) (e : Fin n → Term d) (C input : Term d) : Formula 1 d :=
  Formula.existsMem C (within_m φ (fun i => (e i).weaken) input.weaken .newest C.weaken)

@[simp] theorem restrictedTruthDomain_closed_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (C input : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = []) (hi : input.freeSupport = []) :
    (restrictedTruthDomain_m φ e C input).FreeClosed := by
  simp -implicitDefEqProofs [restrictedTruthDomain_m,he,hC,hi]

theorem restrictedTruthDomain_delta_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (C input : Term d) :
    (restrictedTruthDomain_m φ e C input).IsDelta0 :=
  .existsMem _ (within_delta_l ..)

theorem restrictedTruthDomain_sat_l {n d} (φ : S1_binary n) (ρ : Env M d)
    (e : Fin n → Term d) (C input : Term d) :
    Formula.satisfies ρ (restrictedTruthDomain_m φ e C input) ↔
      RestrictedTruthDomain_d φ (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M n) (C.eval ρ) (input.eval ρ) := by
  simp only [restrictedTruthDomain_m,RestrictedTruthDomain_d,Formula.satisfies_existsMem_iff,
    within_sat_l,Definitional.Term.eval_weaken,Definitional.Term.eval_newest] <;> rfl

def RestrictedTruthTable_d {n} (φ : S1_binary n) (ρ : Env M n) (ω U C T : M.Domain) : Prop :=
  ∀ input, M.mem input T ↔
    (∃ c, M.mem c ω ∧ ∃ x, M.mem x U ∧ KPair_d M input c x) ∧ RestrictedTruthDomain_d φ ρ C input

def restrictedTruthTable_m {n d} (φ : S1_binary n) (e : Fin n → Term d) (ω U C T : Term d) : Formula 1 d :=
  .forallE <| .iff (.mem .newest T.weaken) <| .conj
    (Formula.existsMem ω.weaken <| Formula.existsMem U.weaken.weaken <| kpair0_m (.bound 2) (.bound 1) .newest)
    (restrictedTruthDomain_m φ (fun i => (e i).weaken) C.weaken .newest)

@[simp] theorem restrictedTruthTable_closed_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (ω U C T : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hω : ω.freeSupport = []) (hU : U.freeSupport = [])
    (hC : C.freeSupport = []) (hT : T.freeSupport = []) :
    (restrictedTruthTable_m φ e ω U C T).FreeClosed := by
  simp -implicitDefEqProofs [restrictedTruthTable_m,he,hω,hU,hC,hT,Definitional.Formula.FreeClosed]

theorem restrictedTruthTable_sat_l (hE : Extensional M) {n d} (φ : S1_binary n) (ρ : Env M d)
    (e : Fin n → Term d) (ω U C T : Term d) :
    Formula.satisfies ρ (restrictedTruthTable_m φ e ω U C T) ↔
      RestrictedTruthTable_d φ (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M n)
        (ω.eval ρ) (U.eval ρ) (C.eval ρ) (T.eval ρ) := by
  simp only [restrictedTruthTable_m,RestrictedTruthTable_d,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_existsMem_iff,kpair0_sat_l hE,restrictedTruthDomain_sat_l,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound] <;> rfl

private def restrictedTruthDomain_b {n} (φ : S1_binary n) : Delta0UnarySchema (n+1) where
  body := restrictedTruthDomain_m φ (fun i => .bound i.succ.succ) (.bound 1) .newest
  delta0 := restrictedTruthDomain_delta_l ..

private theorem restrictedTruthDomain_schema_sat_l {n} (φ : S1_binary n) (ρ : Env M n) (C input : M.Domain) :
    (restrictedTruthDomain_b φ).toUnarySchema.denote (⟨Fin.cases C ρ.bound,ρ.free⟩ : Env M (n+1)) input ↔
      RestrictedTruthDomain_d φ ρ C input := by
  change Formula.satisfies ((⟨Fin.cases C ρ.bound,ρ.free⟩ : Env M (n+1)).push input)
    (restrictedTruthDomain_m φ (fun i => .bound i.succ.succ) (.bound 1) .newest) ↔ _
  rw [restrictedTruthDomain_sat_l] <;> rfl

theorem RestrictedTruthTable_d.subset_l (hKP : M.Models KP) {n φ ρ ω U C T D}
    (table : RestrictedTruthTable_d (n := n) φ ρ ω U C T)
    (product : M.IsCartesianProduct (kp_pair_l hKP) D ω U) : M.MemberSubset T D := by
  intro input hit
  exact (product input).mpr ((table input).mp hit).1

theorem RestrictedTruthTable_d.pair_l {n φ ρ ω U C T input c x}
    (table : RestrictedTruthTable_d (n := n) φ ρ ω U C T)
    (hc : M.mem c ω) (hx : M.mem x U) (pair : KPair_d M input c x) :
    M.mem input T ↔ RestrictedTruthDomain_d φ ρ C input :=
  ⟨fun hit => ((table input).mp hit).2,fun hit => (table input).mpr ⟨⟨c,hc,x,hx,pair⟩,hit⟩⟩

theorem restrictedTruthTable_unique_l (hE : Extensional M) {n} {φ : S1_binary n} {ρ : Env M n}
    {ω U C T V : M.Domain}
    (left : RestrictedTruthTable_d (n := n) φ ρ ω U C T)
    (right : RestrictedTruthTable_d φ ρ ω U C V) : T = V := by
  apply hE.eq_of_same_members
  intro input
  exact (left input).trans (right input).symm

theorem restrictedTruthTable_exists_l (hZF : M.Models ZF) {n} (φ : S1_binary n)
    (ρ : Env M n) (ω U C : M.Domain) :
    ∃ D T, M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) D ω U ∧
      RestrictedTruthTable_d φ ρ ω U C T ∧ M.MemberSubset T D := by
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF (kp_pair_l (ZF.modelsKP hZF)) ω U
  let η : Env M (n+1) := ⟨Fin.cases C ρ.bound,ρ.free⟩
  obtain ⟨T,separated⟩ := ZF.separation_exists_d hZF (restrictedTruthDomain_b φ).toUnarySchema η D
  have table : RestrictedTruthTable_d φ ρ ω U C T := by
    intro input
    exact (separated input).trans (and_congr (product input) (restrictedTruthDomain_schema_sat_l φ ρ C input))
  exact ⟨D,T,product,table,table.subset_l (ZF.modelsKP hZF) product⟩

theorem restrictedTruthTable_existsUnique_l (hZF : M.Models ZF) {n} (φ : S1_binary n)
    (ρ : Env M n) (ω U C : M.Domain) :
    ∃ T, RestrictedTruthTable_d φ ρ ω U C T ∧ ∀ V, RestrictedTruthTable_d φ ρ ω U C V → V = T := by
  obtain ⟨_,T,_,table,_⟩ := restrictedTruthTable_exists_l hZF φ ρ ω U C
  exact ⟨T,table,fun V other => restrictedTruthTable_unique_l (M := M) hZF.1 other table⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
