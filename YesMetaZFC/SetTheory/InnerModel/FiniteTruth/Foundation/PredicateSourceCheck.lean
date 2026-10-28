import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateDelta0

/-! # 原有界 AST 的可计算谓词专用出现核验

核验器只检查原公式语法；正确性在原 IsDelta0 证据上证明。
它不是模型内的全公式真值谓词。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project

def predicateUseCheck {d} (a : Fin d) : Formula 1 d → Bool
  | .falsum | .truth => true
  | .mem t _ => decide (t ≠ .bound a)
  | .atom _ _ args => decide (∀ i, args i ≠ .bound a)
  | .neg φ => predicateUseCheck a φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => predicateUseCheck a φ && predicateUseCheck a ψ
  | .forallE body => match body with
      | .imp (.mem t s) φ => decide (t = .newest) && decide (s ≠ .bound a.succ) && predicateUseCheck a.succ φ
      | _ => false
  | .existsE body => match body with
      | .conj (.mem t s) φ => decide (t = .newest) && decide (s ≠ .bound a.succ) && predicateUseCheck a.succ φ
      | _ => false

theorem predicateUseCheck_sound_l {d} {φ : Formula 1 d} (hd : φ.IsDelta0) (a : Fin d)
    (checked : predicateUseCheck a φ = true) : PredicateDelta0 a φ := by
  induction hd with
  | falsum => exact .falsum _
  | truth => exact .truth _
  | mem t s =>
      have apart : t ≠ .bound a := of_decide_eq_true checked
      by_cases same : s = .bound a
      · subst s
        exact .predicate a t apart
      · exact .mem a t s apart same
  | atom symbol stage args => exact .atom a symbol stage args (of_decide_eq_true checked)
  | neg h ih => exact .neg (ih a checked)
  | conj h g ih jh =>
      simp only [predicateUseCheck,Bool.and_eq_true] at checked
      exact .conj (ih a checked.1) (jh a checked.2)
  | disj h g ih jh =>
      simp only [predicateUseCheck,Bool.and_eq_true] at checked
      exact .disj (ih a checked.1) (jh a checked.2)
  | imp h g ih jh =>
      simp only [predicateUseCheck,Bool.and_eq_true] at checked
      exact .imp (ih a checked.1) (jh a checked.2)
  | iff h g ih jh =>
      simp only [predicateUseCheck,Bool.and_eq_true] at checked
      exact .iff (ih a checked.1) (jh a checked.2)
  | forallMem t h ih =>
      simp only [Formula.forallMem,predicateUseCheck,Bool.and_eq_true,decide_eq_true_eq,true_and] at checked
      have apart : t ≠ .bound a := by
        intro eq
        apply checked.1
        rw [eq]
        rfl
      exact .forallMem a t apart (ih a.succ checked.2)
  | existsMem t h ih =>
      simp only [Formula.existsMem,predicateUseCheck,Bool.and_eq_true,decide_eq_true_eq,true_and] at checked
      have apart : t ≠ .bound a := by
        intro eq
        apply checked.1
        rw [eq]
        rfl
      exact .existsMem a t apart (ih a.succ checked.2)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
