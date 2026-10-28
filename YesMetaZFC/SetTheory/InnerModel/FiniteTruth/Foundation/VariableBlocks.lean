import YesMetaZFC.SetTheory.Definitional.Project

/-! # 原对象语言的有限变量块

只在固定外部模板的语法中装配量词块。模型内程序长度与内部 ω 均不受此
外部块索引限制；环境栈顶的顺序与原 Project binder 约定精确一致。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def blockEnv_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) : Env M (n+k) where
  bound i := if h : i.val < k then σ ⟨i.val,h⟩ else ρ.bound ⟨i.val-k,by omega⟩
  free := ρ.free

theorem blockEnv_zero_l {n} (ρ : Env M n) (σ : Fin 0 → M.Domain) : blockEnv_l ρ σ = ρ := by
  cases ρ
  dsimp only [blockEnv_l]
  rw [Env.mk.injEq]
  constructor
  · funext i
    rw [dif_neg (Nat.not_lt_zero i.val)]
    simp only [Nat.sub_zero]
    cases i
    rfl
  · rfl

theorem blockEnv_succ_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (x : M.Domain) :
    blockEnv_l ρ (Fin.cases x σ) = (blockEnv_l ρ σ).push x := by
  dsimp only [blockEnv_l,Env.push]
  rw [Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cases_succ,Fin.val_succ]
      by_cases hj : j.val < k
      · rw [dif_pos (show j.val+1 < k+1 by omega),dif_pos hj]
        rfl
      · rw [dif_neg (show ¬ j.val+1 < k+1 by omega),dif_neg hj]
        exact congrArg ρ.bound (Fin.ext (show j.val+1-(k+1) = j.val-k by omega))
  · rfl

theorem blockEnv_source_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (i : Fin k) :
    (blockEnv_l ρ σ).bound ⟨i.val,by omega⟩ = σ i := by
  simp only [blockEnv_l,dif_pos i.isLt]

theorem blockEnv_old_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (i : Fin n) :
    (blockEnv_l ρ σ).bound ⟨k+i.val,by omega⟩ = ρ.bound i := by
  change (if h : k+i.val < k then σ ⟨k+i.val,h⟩ else ρ.bound ⟨k+i.val-k,by omega⟩) = _
  rw [dif_neg (by omega)]
  exact congrArg ρ.bound (Fin.ext (show k+i.val-k = i.val by omega))

def forallBlock_m {n} : (k : Nat) → Formula 1 (n+k) → Formula 1 n
  | 0, φ => φ
  | k+1, φ => forallBlock_m k (.forallE φ)

@[simp] theorem forallBlock_closed_iff_l {n k} (φ : Formula 1 (n+k)) :
    (forallBlock_m k φ).FreeClosed ↔ φ.FreeClosed := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [forallBlock_m,ih]
    simp only [Definitional.Formula.FreeClosed]

theorem forallBlock_closed_l {n k} (φ : Formula 1 (n+k)) (hc : φ.FreeClosed) :
    (forallBlock_m k φ).FreeClosed := (forallBlock_closed_iff_l φ).mpr hc

/-- 量词块量化所有源变量值，保留原参数环境。 -/
theorem forallBlock_sat_l {n k} (ρ : Env M n) (φ : Formula 1 (n+k)) :
    Formula.satisfies ρ (forallBlock_m k φ) ↔ ∀ σ : Fin k → M.Domain, Formula.satisfies (blockEnv_l ρ σ) φ := by
  induction k with
  | zero =>
    rw [forallBlock_m]
    simp only [blockEnv_zero_l]
    exact ⟨fun h _ => h,fun h => h Fin.elim0⟩
  | succ k ih =>
    rw [forallBlock_m,ih]
    simp only [Formula.satisfies_forall_iff]
    constructor
    · intro h σ
      have result := h (fun i => σ i.succ) (σ 0)
      have he : Fin.cases (σ 0) (fun i => σ i.succ) = σ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [← blockEnv_succ_l,he] at result
      exact result
    · intro h σ x
      simpa only [blockEnv_succ_l] using h (Fin.cases x σ)

def sourceIndex_l (n k : Nat) (i : Fin k) : Fin (n+k) := ⟨i.val,by omega⟩

/-- 原公式重命名到新变量块后，环境恰为原源变量向量。 -/
theorem sourceRename_sat_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (φ : Formula 1 k) :
    Formula.satisfies (blockEnv_l ρ σ) (φ.rename (sourceIndex_l n k)) ↔
      Formula.satisfies (⟨σ,ρ.free⟩ : Env M k) φ := by
  rw [Formula.satisfies_rename]
  have he : Env.reindex (blockEnv_l ρ σ) (sourceIndex_l n k) = (⟨σ,ρ.free⟩ : Env M k) := by
    dsimp only [Env.reindex]
    rw [Env.mk.injEq]
    exact ⟨funext (fun i => blockEnv_source_l ρ σ i),rfl⟩
  rw [he]

def finConj_m {n} : (k : Nat) → (Fin k → Formula 1 n) → Formula 1 n
  | 0, _ => .truth
  | k+1, φ => .conj (φ 0) (finConj_m k (fun i => φ i.succ))

@[simp] theorem finConj_closed_iff_l {n k} (φ : Fin k → Formula 1 n) :
    (finConj_m k φ).FreeClosed ↔ ∀ i, (φ i).FreeClosed := by
  induction k with
  | zero =>
    rw [finConj_m]
    simp only [Definitional.Formula.FreeClosed]
    exact ⟨fun _ i => Fin.elim0 i,fun _ => trivial⟩
  | succ k ih =>
    rw [finConj_m]
    simp only [Definitional.Formula.FreeClosed]
    rw [ih]
    exact ⟨fun ⟨h,hs⟩ i => Fin.cases h hs i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

theorem finConj_closed_l {n k} (φ : Fin k → Formula 1 n) (hc : ∀ i, (φ i).FreeClosed) :
    (finConj_m k φ).FreeClosed := (finConj_closed_iff_l φ).mpr hc

theorem finConj_sat_l {n k} (ρ : Env M n) (φ : Fin k → Formula 1 n) :
    Formula.satisfies ρ (finConj_m k φ) ↔ ∀ i, Formula.satisfies ρ (φ i) := by
  induction k with
  | zero =>
    rw [finConj_m,Formula.satisfies_truth_iff]
    exact ⟨fun _ i => Fin.elim0 i,fun _ => trivial⟩
  | succ k ih =>
    rw [finConj_m,Formula.satisfies_conj_iff,ih]
    exact ⟨fun ⟨h,hs⟩ i => Fin.cases h hs i,fun h => ⟨h 0,fun i => h i.succ⟩⟩

def oldIndex_l (n k : Nat) (i : Fin n) : Fin (n+k) := ⟨k+i.val,by omega⟩
def oldTerm_m {n k} (t : Term n) : Term (n+k) := t.rename (oldIndex_l n k)

theorem oldTerm_eval_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (t : Term n) :
    (oldTerm_m t).eval (blockEnv_l ρ σ) = t.eval ρ := by
  cases t with
  | bound i => exact blockEnv_old_l ρ σ i
  | free i => rfl

@[simp] theorem oldTerm_support_l {n k} (t : Term n) :
    (oldTerm_m (k := k) t).freeSupport = t.freeSupport := by
  exact Definitional.Term.freeSupport_rename _ _

def sourceTerm_m (n : Nat) {k} (i : Fin k) : Term (n+k) := .bound (sourceIndex_l n k i)

theorem sourceTerm_eval_l {n k} (ρ : Env M n) (σ : Fin k → M.Domain) (i : Fin k) :
    (sourceTerm_m n i).eval (blockEnv_l ρ σ) = σ i := blockEnv_source_l ρ σ i

def existsBlock_m {n} : (k : Nat) → Formula 1 (n+k) → Formula 1 n
  | 0, φ => φ
  | k+1, φ => existsBlock_m k (.existsE φ)

@[simp] theorem existsBlock_closed_iff_l {n k} (φ : Formula 1 (n+k)) :
    (existsBlock_m k φ).FreeClosed ↔ φ.FreeClosed := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [existsBlock_m,ih]
    simp only [Definitional.Formula.FreeClosed]

/-- 存在变量块对应一份实际有限对象向量，保持原参数环境。 -/
theorem existsBlock_sat_l {n k} (ρ : Env M n) (φ : Formula 1 (n+k)) :
    Formula.satisfies ρ (existsBlock_m k φ) ↔ ∃ σ : Fin k → M.Domain, Formula.satisfies (blockEnv_l ρ σ) φ := by
  induction k with
  | zero =>
    rw [existsBlock_m]
    simp only [blockEnv_zero_l]
    exact ⟨fun h => ⟨Fin.elim0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ k ih =>
    rw [existsBlock_m,ih]
    simp only [Formula.satisfies_exists_iff]
    constructor
    · rintro ⟨σ,x,h⟩
      exact ⟨Fin.cases x σ,(blockEnv_succ_l ρ σ x).symm ▸ h⟩
    · rintro ⟨σ,h⟩
      have he : Fin.cases (σ 0) (fun i => σ i.succ) = σ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      refine ⟨fun i => σ i.succ,σ 0,?_⟩
      have eq := blockEnv_succ_l ρ (fun i => σ i.succ) (σ 0)
      rw [he] at eq
      exact eq ▸ h

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
