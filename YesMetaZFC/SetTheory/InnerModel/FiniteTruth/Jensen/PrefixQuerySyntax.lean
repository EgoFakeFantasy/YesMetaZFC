import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixIndexedWitness

/-! # 三个真实背景参数在原对象公式中的嵌入 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def prefixParams_m {d} (A ω P : Term d) : Fin 3 → Term d := Fin.cases A (Fin.cases ω (fun _ => P))

@[simp] theorem prefixParams_closed_l {d} (A ω P : Term d)
    (hA : A.freeSupport = []) (hω : ω.freeSupport = []) (hP : P.freeSupport = []) :
    ∀ i, (prefixParams_m A ω P i).freeSupport = [] := Fin.cases hA (Fin.cases hω (fun _ => hP))

theorem prefixParams_env_l {d} (ρ : Env M d) (A ω P : Term d) :
    (⟨fun i => (prefixParams_m A ω P i).eval ρ,ρ.free⟩ : Env M 3) =
      ⟨Fin.cases (A.eval ρ) (Fin.cases (ω.eval ρ) (fun _ => P.eval ρ)),ρ.free⟩ := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))),rfl⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
