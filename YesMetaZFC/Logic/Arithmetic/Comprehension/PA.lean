import YesMetaZFC.Logic.Arithmetic.Comprehension.Induction
import YesMetaZFC.Logic.Arithmetic.PA.Interpretation

/-! # PA 在各级 CA₀ 中的对象解释

复用原项、公式和六规则的翻译，仅验证所需的公理像。PA 的归纳正文
翻译后仍是算术公式，因此 ACA₀ 已足够；任意局部上下文一起传输。
-/
namespace YesMetaZFC.Logic.Arithmetic.Comprehension
open FirstOrder
set_option autoImplicit false

theorem pa_arith_m {Γ Δ : SortContext Arithmetic.signature_m}
    (φ : Formula Arithmetic.signature_m Γ Δ) : arith_m (PA.Translation.formula_m φ) := by
  induction φ with
  | rel r _ => cases r
  | forallE s φ ih => cases s; exact ih
  | existsE s φ ih => cases s; exact ih
  | _ => simp_all [PA.Translation.formula_m, arith_m]

theorem pa_axiom_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {φ : Sentence Arithmetic.signature_m}
    (h : PA.theory_m φ) : Provable T (PA.Translation.formula_m φ) := by
  cases h with
  | robinson h =>
    cases h with
    | base k =>
      rw [PA.Translation.number_image_m]
      exact Provable.theory_axiom (hT (axiom_m.number k))
  | induction φ =>
    rw [PA.Translation.formula_close_m, PA.Translation.induction_image_m]
    exact Metatheory.Derives.forall_close_of_derives
      (induction_derives_m hT _ (.arith (pa_arith_m φ)))

/-- 目标理论只需扩张相应 CA₀，不需完整 Z₂ 理解或标准模型。 -/
theorem pa_derives_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {Δ : SortContext Arithmetic.signature_m}
    {Γ : Context Arithmetic.signature_m Δ} {φ : Formula Arithmetic.signature_m [] Δ}
    (h : Derives PA.theory_m Γ φ) :
    Derives T (Γ.map PA.Translation.formula_m) (PA.Translation.formula_m φ) :=
  PA.Translation.derives_of_axioms_m (pa_axiom_m hT) h

end YesMetaZFC.Logic.Arithmetic.Comprehension
