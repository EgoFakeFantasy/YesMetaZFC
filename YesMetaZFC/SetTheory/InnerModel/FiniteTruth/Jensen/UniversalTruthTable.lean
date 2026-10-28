import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RestrictedTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedPredicateWitness
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSkolemQuery

/-! # 全部内部参数图上的实际通用真值表

第二坐标遍历 C 的全部成员；没有预先固定参数前缀 P。背景 ZF 构造实际表，
原 Jensen 层的完整见证域定理给出 T ⊆ C，不预设 T 属于 C 或任何 amenability。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def UniversalTruthTable_d (ρ : Env M 2) (C T : M.Domain) : Prop :=
  RestrictedTruthTable_d indexedPredicateWitness_s ρ (ρ.bound 1) C C T

def universalTruthTable_m {d} (A ω C T : Term d) : Formula 1 d :=
  restrictedTruthTable_m indexedPredicateWitness_s (predicatePairParams_m A ω) ω C C T

@[simp] theorem universalTruthTable_closed_l {d} (A ω C T : Term d)
    (hA : A.freeSupport = []) (hω : ω.freeSupport = [])
    (hC : C.freeSupport = []) (hT : T.freeSupport = []) :
    (universalTruthTable_m A ω C T).FreeClosed :=
  restrictedTruthTable_closed_l indexedPredicateWitness_s (predicatePairParams_m A ω) ω C C T
    (predicatePairParams_closed_l A ω hA hω) hω hC hC hT

theorem universalTruthTable_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (A ω C T : Term d) :
    Formula.satisfies ρ (universalTruthTable_m A ω C T) ↔
      UniversalTruthTable_d (⟨Fin.cases (A.eval ρ) (fun _ => ω.eval ρ),ρ.free⟩ : Env M 2)
        (C.eval ρ) (T.eval ρ) := by
  unfold universalTruthTable_m
  rw [restrictedTruthTable_sat_l hE,predicatePairParams_env_l]
  rfl

theorem universalTruthTable_exists_l (hZF : M.Models ZF) (ρ : Env M 2) (C : M.Domain) :
    ∃ T, UniversalTruthTable_d ρ C T := by
  obtain ⟨T,table,_⟩ := restrictedTruthTable_existsUnique_l hZF indexedPredicateWitness_s ρ (ρ.bound 1) C C
  exact ⟨T,table⟩

theorem universalTruthTable_unique_l (hE : Extensional M) {ρ : Env M 2} {C T V : M.Domain}
    (left : UniversalTruthTable_d ρ C T) (right : UniversalTruthTable_d ρ C V) : T = V :=
  restrictedTruthTable_unique_l (M := M) hE left right

theorem jh_universalTruthTable_subset_l (hZF : M.Models ZF) {α C T : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (table : UniversalTruthTable_d ρ C T) : M.MemberSubset T C := by
  intro input hit
  obtain ⟨y,_,selected⟩ := ((table input).mp hit).2
  exact (jh_indexedPredicateWitness_domain_l hZF hα h ρ hω hωC selected).2.1

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
