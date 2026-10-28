import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AmenableSeparation

/-! # 带实际外部集合谓词的分离结论之原公式 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def predicateSeparation_m {p d} (φ : UnarySchema (p+1)) (e : Fin p → Term d) (C A X : Term d) : Formula 1 d :=
  Formula.existsMem C <| .forallE <| .iff (.mem .newest (.bound 1)) <|
    .conj (.mem .newest X.weaken.weaken)
      (pred_m φ (Fin.cases A.weaken.weaken (fun i => (e i).weaken.weaken)) .newest)

@[simp] theorem predicateSeparation_closed_l {p d} (φ : UnarySchema (p+1)) (e : Fin p → Term d) (C A X : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = []) (hA : A.freeSupport = []) (hX : X.freeSupport = []) :
    (predicateSeparation_m φ e C A X).FreeClosed := by
  simp -implicitDefEqProofs [predicateSeparation_m,Definitional.Formula.FreeClosed,hC,hX]
  exact pred_m_freeClosed φ _ _ (Fin.cases (by simpa using hA) (fun i => by simpa using he i)) rfl

theorem predicateSeparation_sat_l {p d} (φ : UnarySchema (p+1)) (ρ : Env M d) (e : Fin p → Term d) (C A X : Term d) :
    Formula.satisfies ρ (predicateSeparation_m φ e C A X) ↔
      ∃ Y, M.mem Y (C.eval ρ) ∧ ∀ x, M.mem x Y ↔ M.mem x (X.eval ρ) ∧
        φ.denote ((⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M p).push (A.eval ρ)) x := by
  simp only [predicateSeparation_m,Formula.satisfies_existsMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,pred_sat_l,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,Term.eval_bound_one_push,Term.eval_bound_zero_push]
  apply exists_congr
  intro Y
  apply and_congr Iff.rfl
  apply forall_congr'
  intro x
  have envEq : (⟨fun i : Fin (p+1) => (Fin.cases (motive := fun _ : Fin (p+1) => Term (d+2)) A.weaken.weaken (fun j : Fin p => (e j).weaken.weaken) i).eval ((ρ.push Y).push x),((ρ.push Y).push x).free⟩ : Env M (p+1)) =
      (⟨fun i => (e i).eval ρ,ρ.free⟩ : Env M p).push (A.eval ρ) := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change A.weaken.weaken.eval ((ρ.push Y).push x) = A.eval ρ
        simp only [Definitional.Term.eval_weaken]
      · change (e j).weaken.weaken.eval ((ρ.push Y).push x) = (e j).eval ρ
        simp only [Definitional.Term.eval_weaken]
    · rfl
  rw [envEq]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
