import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.VariableBlocks

/-! # 原变量块上的指定槽排除合取 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def protectedConj_m {n d} (a : Fin d) (φ : Fin d → Formula 1 n) : Formula 1 n :=
  finConj_m d (fun i => if i = a then .truth else φ i)

theorem protectedConj_sat_l {n d} (ρ : Env M n) (a : Fin d) (φ : Fin d → Formula 1 n) :
    Formula.satisfies ρ (protectedConj_m a φ) ↔ ∀ i, i ≠ a → Formula.satisfies ρ (φ i) := by
  rw [protectedConj_m,finConj_sat_l]
  constructor
  · intro all i different
    simpa only [if_neg different] using all i
  · intro all i
    by_cases eq : i = a
    · simp only [if_pos eq,Formula.satisfies_truth_iff]
    · simpa only [if_neg eq] using all i eq

@[simp] theorem protectedConj_closed_l {n d} (a : Fin d) (φ : Fin d → Formula 1 n)
    (hc : ∀ i, (φ i).FreeClosed) : (protectedConj_m a φ).FreeClosed := by
  unfold protectedConj_m
  apply finConj_closed_l
  intro i
  split
  · simp [Definitional.Formula.FreeClosed]
  · exact hc i

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
