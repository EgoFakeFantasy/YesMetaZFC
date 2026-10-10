import YesMetaZFC.Logic.Arithmetic.Comprehension.Axioms
import YesMetaZFC.Logic.Arithmetic.Z2.Induction

/-! # 受限理解导出的归纳

集合归纳经实际理解实例传回 Π¹ₙ 正文。理论本身只含集合归纳公理，
此处不给不属于模式的任意公式免费添加归纳。
-/
namespace YesMetaZFC.Logic.Arithmetic.Comprehension
open FirstOrder Z2
set_option autoImplicit false

theorem induction_derives_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {Δ : SortContext Z2.signature_m}
    {Γ : Context Z2.signature_m Δ} (φ : Formula Z2.signature_m [] (.num :: Δ)) (hφ : pi_m n φ) :
    Derives T Γ (Z2.induction_m φ) := by
  apply Z2.induction_of_comprehension_m φ (comprehension_derives_m hT φ hφ)
  have h : Derives T ([] : Context Z2.signature_m (.set :: Δ))
      (Formula.fromSentence Z2.set_induction_m) :=
    Derives.theory_axiom (hT axiom_m.set_induction)
  exact Derives.forall_elim (.fvar .here) h

theorem induction_rule_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {Δ : SortContext Z2.signature_m}
    {Γ : Context Z2.signature_m Δ} {φ : Formula Z2.signature_m [] (.num :: Δ)} (hφ : pi_m n φ)
    (h₀ : Derives T Γ (φ.instantiateFreeTop Z2.zero_m))
    (h₁ : Derives T (FreshVariable.extendContext Z2.sort_m.num Γ)
      (.imp φ (φ.substituteFree Z2.next_m))) : Derives T Γ (φ.forallFreeTop Z2.sort_m.num) :=
  Derives.imp_elim (induction_derives_m hT φ hφ) (Derives.conj_intro h₀ (Derives.forall_intro h₁))

end YesMetaZFC.Logic.Arithmetic.Comprehension
