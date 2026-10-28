import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateCanonicalCertificates

/-! # 原局部关系统一选择的完整对象规格 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def LocalUniformizes_d {n} (φ ψ : S1_binary n) (ρ : Env M n) (C : M.Domain) : Prop :=
  ∀ x, M.mem x C →
    ((∃ y, M.mem y C ∧ Within_d φ ρ x y C) ↔ ∃ y, M.mem y C ∧ Within_d ψ ρ x y C) ∧
      ∀ y, M.mem y C → Within_d ψ ρ x y C → Within_d φ ρ x y C ∧
        ∀ z, M.mem z C → Within_d ψ ρ x z C → z = y

def localUniformizes_m {n d} (φ ψ : S1_binary n) (e : Fin n → Term d) (C : Term d) : Formula 1 d :=
  Formula.forallMem C <| .conj
    (.iff (Formula.existsMem C.weaken <| within_m φ (fun i => (e i).weaken.weaken) (.bound 1) .newest C.weaken.weaken)
      (Formula.existsMem C.weaken <| within_m ψ (fun i => (e i).weaken.weaken) (.bound 1) .newest C.weaken.weaken))
    (Formula.forallMem C.weaken <| .imp
      (within_m ψ (fun i => (e i).weaken.weaken) (.bound 1) .newest C.weaken.weaken) <| .conj
        (within_m φ (fun i => (e i).weaken.weaken) (.bound 1) .newest C.weaken.weaken)
        (Formula.forallMem C.weaken.weaken <| .imp
          (within_m ψ (fun i => (e i).weaken.weaken.weaken) (.bound 2) .newest C.weaken.weaken.weaken)
          (Formula.extensionalEq .newest (.bound 1))))

@[simp] theorem localUniformizes_closed_l {n d} (φ ψ : S1_binary n) (e : Fin n → Term d) (C : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = []) : (localUniformizes_m φ ψ e C).FreeClosed := by
  simp -implicitDefEqProofs [localUniformizes_m,Definitional.Formula.FreeClosed,he,hC]

theorem localUniformizes_sat_l (hE : Extensional M) {n d} (φ ψ : S1_binary n) (ρ : Env M d)
    (e : Fin n → Term d) (C : Term d) : Formula.satisfies ρ (localUniformizes_m φ ψ e C) ↔
      LocalUniformizes_d φ ψ (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M n) (C.eval ρ) := by
  simp only [localUniformizes_m,LocalUniformizes_d,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_imp_iff,within_sat_l,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
