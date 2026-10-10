import YesMetaZFC.Logic.Arithmetic.Z2.Syntax

/-! # 分析层级的带参数语法

算术矩阵允许任意数目量词及自由数集参数，但不允许数集量词。
Π¹ₙ／Σ¹ₙ 使用至多 n 个交替数集量词块；同类块可含任意有限多个量词。
本层只识别前束代表，不把模型中的等价当作语法复杂度证明。
-/
namespace YesMetaZFC.Logic.Arithmetic.Comprehension
open FirstOrder Z2
set_option autoImplicit false

def arith_m {Γ Δ : SortContext Z2.signature_m} : Formula Z2.signature_m Γ Δ → Prop
  | .falsum | .truth | .rel _ _ | .equal _ _ => True
  | .neg φ => arith_m φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => arith_m φ ∧ arith_m ψ
  | .forallE .num φ | .existsE .num φ => arith_m φ
  | .forallE .set _ | .existsE .set _ => False

/-- true 表示 Σ，false 表示 Π；指标是允许的量词块数。 -/
inductive analytic_m : Bool → Nat → {Γ Δ : SortContext Z2.signature_m} →
    Formula Z2.signature_m Γ Δ → Prop where
  | arith {p : Bool} {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m Γ Δ} (h : arith_m φ) : analytic_m p n φ
  | lift {p : Bool} {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m Γ Δ} (h : analytic_m p n φ) : analytic_m p (n + 1) φ
  | all {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m (.set :: Γ) Δ}
      (h : analytic_m true n φ) : analytic_m false (n + 1) (.forallE .set φ)
  | ex {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m (.set :: Γ) Δ}
      (h : analytic_m false n φ) : analytic_m true (n + 1) (.existsE .set φ)
  | all_block {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m (.set :: Γ) Δ}
      (h : analytic_m false (n + 1) φ) : analytic_m false (n + 1) (.forallE .set φ)
  | ex_block {n : Nat} {Γ Δ : SortContext Z2.signature_m}
      {φ : Formula Z2.signature_m (.set :: Γ) Δ}
      (h : analytic_m true (n + 1) φ) : analytic_m true (n + 1) (.existsE .set φ)

abbrev pi_m {Γ Δ : SortContext Z2.signature_m} (n : Nat)
    (φ : Formula Z2.signature_m Γ Δ) : Prop := analytic_m false n φ

abbrev sigma_m {Γ Δ : SortContext Z2.signature_m} (n : Nat)
    (φ : Formula Z2.signature_m Γ Δ) : Prop := analytic_m true n φ

theorem zero_iff_m {p : Bool} {Γ Δ : SortContext Z2.signature_m}
    {φ : Formula Z2.signature_m Γ Δ} : analytic_m p 0 φ ↔ arith_m φ := by
  constructor
  · intro h
    cases h with
    | arith h => exact h
  · exact analytic_m.arith

theorem mono_m {p : Bool} {m n : Nat} {Γ Δ : SortContext Z2.signature_m}
    {φ : Formula Z2.signature_m Γ Δ} (h : analytic_m p m φ) (hmn : m ≤ n) :
    analytic_m p n φ := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact .lift ih

theorem arith_rename_m {Γ Δ Γ₁ Δ₁ : SortContext Z2.signature_m}
    (φ : Formula Z2.signature_m Γ Δ) (ρ : VariableRenaming Γ Γ₁)
    (τ : VariableRenaming Δ Δ₁) (h : arith_m φ) : arith_m (φ.renameMapped ρ τ) := by
  induction φ generalizing Γ₁ Δ₁ with
  | forallE s φ ih =>
    cases s <;> simp_all [arith_m, Formula.renameMapped]
  | existsE s φ ih =>
    cases s <;> simp_all [arith_m, Formula.renameMapped]
  | _ => simp_all [arith_m, Formula.renameMapped]

theorem rename_m {p : Bool} {n : Nat} {Γ Δ Γ₁ Δ₁ : SortContext Z2.signature_m}
    {φ : Formula Z2.signature_m Γ Δ} (h : analytic_m p n φ)
    (ρ : VariableRenaming Γ Γ₁) (τ : VariableRenaming Δ Δ₁) :
    analytic_m p n (φ.renameMapped ρ τ) := by
  induction h generalizing Γ₁ Δ₁ with
  | arith h => exact .arith (arith_rename_m _ ρ τ h)
  | lift _ ih => exact .lift (ih ρ τ)
  | all _ ih => exact .all (ih (VariableRenaming.lift ρ) τ)
  | ex _ ih => exact .ex (ih (VariableRenaming.lift ρ) τ)
  | all_block _ ih => exact .all_block (ih (VariableRenaming.lift ρ) τ)
  | ex_block _ ih => exact .ex_block (ih (VariableRenaming.lift ρ) τ)

/-- 新鲜集合槽不进入理解正文，自由参数的复杂度保持不变。 -/
theorem insert_m {p : Bool} {n : Nat} {Δ : SortContext Z2.signature_m}
    {φ : Formula Z2.signature_m [] (.num :: Δ)} (h : analytic_m p n φ) :
    analytic_m p n (Z2.insert_m φ) :=
  rename_m h VariableRenaming.id
    (VariableRenaming.lift (introduced := Z2.sort_m.num) (VariableRenaming.weaken Z2.sort_m.set))

end YesMetaZFC.Logic.Arithmetic.Comprehension
