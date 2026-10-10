import YesMetaZFC.Logic.Arithmetic.Comprehension.Induction
import YesMetaZFC.Model.Arithmetic.Z2.Standard

/-! # 受限理解的模型接口

以下接口读取已证明的对象模式；载体保持同一 universe，不预设数域标准、
集域为外部幂集或模型外部良基。标准模型一致性单独标明为 Lean 元层结论。
-/
namespace YesMetaZFC.Model.Arithmetic.Comprehension
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

theorem models_of_z2_m {ℳ : Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : Nat) : Theory.Models ℳ (Logic.Arithmetic.Comprehension.theory_m n) :=
  fun _ h => hℳ _ (Logic.Arithmetic.Comprehension.z2_extends_m n h)

theorem models_mono_m {ℳ : Structure.{0, 0, 0, u} signature_m} {m n : Nat}
    (hℳ : Theory.Models ℳ (Logic.Arithmetic.Comprehension.theory_m n)) (hmn : m ≤ n) :
    Theory.Models ℳ (Logic.Arithmetic.Comprehension.theory_m m) :=
  fun _ h => hℳ _ (Logic.Arithmetic.Comprehension.extends_m hmn h)

/-- 见证留在模型原集域中，没有选择宿主函数或扩大 universe。 -/
theorem comprehension_m {ℳ : Structure.{0, 0, 0, u} signature_m} {n : Nat}
    (hℳ : Theory.Models ℳ (Logic.Arithmetic.Comprehension.theory_m n)) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : Logic.Arithmetic.Comprehension.pi_m n φ) (η : Env ℳ [] Δ) :
    ∃ X : Z2.set_l ℳ, ∀ k : Z2.num_l ℳ,
      Z2.mem_l k X ↔ Formula.satisfies (η.pushFree k) φ := by
  have h := (Logic.Arithmetic.Comprehension.comprehension_derives_m (Γ := []) (fun h => h) φ hφ).sound hℳ η
    (by intro ψ hψ; cases hψ)
  exact (Z2.comprehension_sat_m φ η).mp h

theorem induction_m {ℳ : Structure.{0, 0, 0, u} signature_m} {n : Nat}
    (hℳ : Theory.Models ℳ (Logic.Arithmetic.Comprehension.theory_m n)) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : Logic.Arithmetic.Comprehension.pi_m n φ) (η : Env ℳ [] Δ)
    (h₀ : Formula.satisfies (η.pushFree (Z2.zero_l ℳ)) φ)
    (h₁ : ∀ k, Formula.satisfies (η.pushFree k) φ →
      Formula.satisfies (η.pushFree (Z2.succ_l k)) φ) :
    ∀ k, Formula.satisfies (η.pushFree k) φ := by
  have h := (Logic.Arithmetic.Comprehension.induction_derives_m (Γ := []) (fun h => h) φ hφ).sound hℳ η
    (by intro ψ hψ; cases hψ)
  exact (Z2.induction_sat_m φ η).mp h ⟨h₀, h₁⟩

theorem standard_models_m (n : Nat) : Theory.Models Z2.standard_m (Logic.Arithmetic.Comprehension.theory_m n) :=
  models_of_z2_m Z2.models_m n

/-- 这是当前 Lean 背景中的模型可靠性结论，不是 CA₀ 内部的一致性证明。 -/
theorem consistent_m (n : Nat) : ¬Derives (Logic.Arithmetic.Comprehension.theory_m n) [] (.falsum : Sentence signature_m) := by
  intro h
  exact h.sound (standard_models_m n) Env.empty (by intro φ hφ; cases hφ)

end YesMetaZFC.Model.Arithmetic.Comprehension
