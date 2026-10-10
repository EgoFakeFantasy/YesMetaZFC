import YesMetaZFC.Logic.Arithmetic.Comprehension.Hierarchy
import YesMetaZFC.Logic.Arithmetic.Z2.Axioms

/-! # ACA₀ 与 Π¹ₙ-CA₀ 的对象公理模式

复用 Z₂ 的数目公理、外延性、集合归纳和新鲜见证槽。理解正文受 Π¹ₙ
语法证书约束；不添加全公式归纳或选择公理。n=0 是 ACA₀。
-/
namespace YesMetaZFC.Logic.Arithmetic.Comprehension
open FirstOrder Z2
set_option autoImplicit false

inductive axiom_m (n : Nat) : Sentence Z2.signature_m → Prop where
  | number (k : Robinson.base_m) : axiom_m n (number_m k)
  | extensionality : axiom_m n extensionality_m
  | set_induction : axiom_m n set_induction_m
  | comprehension {Δ : SortContext Z2.signature_m} (φ : Formula Z2.signature_m [] (.num :: Δ))
      (h : pi_m n φ) : axiom_m n (Metatheory.Formula.forall_close (comprehension_m φ))

def theory_m (n : Nat) : Theory Z2.signature_m := axiom_m n

def aca0_m : Theory Z2.signature_m := theory_m 0
def pi11_ca0_m : Theory Z2.signature_m := theory_m 1
def pi12_ca0_m : Theory Z2.signature_m := theory_m 2

theorem extends_m {m n : Nat} (hmn : m ≤ n) : Theory.Extends (theory_m n) (theory_m m) := by
  intro φ h
  cases h with
  | number k => exact .number k
  | extensionality => exact .extensionality
  | set_induction => exact .set_induction
  | comprehension φ h => exact .comprehension φ (mono_m h hmn)

theorem z2_extends_m (n : Nat) : Theory.Extends Z2.theory_m (theory_m n) := by
  intro φ h
  cases h with
  | number k => exact Z2.axiom_m.number k
  | extensionality => exact Z2.axiom_m.extensionality
  | set_induction => exact Z2.axiom_m.set_induction
  | comprehension φ _ => exact Z2.axiom_m.comprehension φ

/-- 任意理论扩张、混合参数和局部上下文中的实际理解推导。 -/
theorem comprehension_derives_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {Δ : SortContext Z2.signature_m}
    {Γ : Context Z2.signature_m Δ} (φ : Formula Z2.signature_m [] (.num :: Δ)) (hφ : pi_m n φ) :
    Derives T Γ (comprehension_m φ) :=
  Derives.of_provable (Metatheory.Derives.forall_close_open _
    (Derives.theory_axiom (hT (axiom_m.comprehension φ hφ))))

theorem arith_comprehension_m {n : Nat} {T : Theory Z2.signature_m}
    (hT : Theory.Extends T (theory_m n)) {Δ : SortContext Z2.signature_m}
    {Γ : Context Z2.signature_m Δ} (φ : Formula Z2.signature_m [] (.num :: Δ)) (hφ : arith_m φ) :
    Derives T Γ (comprehension_m φ) :=
  comprehension_derives_m hT φ (.arith hφ)

end YesMetaZFC.Logic.Arithmetic.Comprehension
