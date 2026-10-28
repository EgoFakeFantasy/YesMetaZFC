import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedFormulaCode
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.VariableBlocks

/-! # 实际数码构成的规范有限寄存器框架

框架的槽号是固定源模板的外部有限索引，槽值与变量域均是模型内实际序数码。
有限向量通过归纳逐项装配，不从任意模型中抽取全局选择函数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u
variable {M : SetTheory.Structure.{u}}

theorem numeral_vector_exists_l (hKP : M.Models KP) (k : Nat) :
    ∃ v : Fin k → M.Domain, ∀ i, Num_d i.val (v i) := by
  induction k with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih
    obtain ⟨x,hx⟩ := num_exists_l hKP k
    refine ⟨Fin.lastCases x v,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last,Fin.val_last] using hx
    · simpa only [Fin.lastCases_castSucc,Fin.val_castSucc] using hv j

structure RegisterFrame_d (k : Nat) (n : M.Domain) (v : Fin k → M.Domain) : Prop where
  arity : Num_d k n
  slots : ∀ i, Num_d i.val (v i)

theorem registerFrame_exists_l (hKP : M.Models KP) (k : Nat) :
    ∃ n, ∃ v : Fin k → M.Domain, RegisterFrame_d k n v := by
  obtain ⟨n,hn⟩ := num_exists_l hKP k
  obtain ⟨v,hv⟩ := numeral_vector_exists_l hKP k
  exact ⟨n,v,hn,hv⟩

theorem RegisterFrame_d.unique_l (hE : Extensional M) {k n m} {v w : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (other : RegisterFrame_d k m w) : n = m ∧ v = w :=
  ⟨num_unique_l hE frame.arity other.arity,funext (fun i => num_unique_l hE (frame.slots i) (other.slots i))⟩

theorem RegisterFrame_d.bound_l (hE : Extensional M) {k n} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (i : Fin k) : M.mem (v i) n :=
  num_lt_l hE (frame.slots i) frame.arity i.isLt

theorem RegisterFrame_d.omega_l (hE : Extensional M) {k n ω} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (hω : M.IsOmega ω) : M.mem n ω := num_mem_l hE hω frame.arity

theorem RegisterFrame_d.injective_l (hKP : M.Models KP) {k n} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) : Function.Injective v := by
  intro i j eq
  have hj : Num_d j.val (v i) := eq.symm ▸ frame.slots j
  exact Fin.ext (num_injective_l hKP (frame.slots i) hj)

def framePrefix_l {d k} (hdk : d ≤ k) (v : Fin k → M.Domain) (i : Fin d) : M.Domain := v ⟨i.val,by omega⟩

theorem RegisterFrame_d.prefix_bound_l (hE : Extensional M) {d k n} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (hdk : d ≤ k) (i : Fin d) : M.mem (framePrefix_l hdk v i) n :=
  frame.bound_l hE ⟨i.val,by omega⟩

theorem RegisterFrame_d.prefix_injective_l (hKP : M.Models KP) {d k n} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (hdk : d ≤ k) : Function.Injective (framePrefix_l hdk v) := by
  intro i j eq
  have he := frame.injective_l hKP eq
  exact Fin.ext (congrArg (fun x : Fin k => x.val) he)

/-- 任一保留槽都与全部原源变量槽不同。 -/
theorem RegisterFrame_d.fresh_l (hKP : M.Models KP) {d k n} {v : Fin k → M.Domain}
    (frame : RegisterFrame_d k n v) (hdk : d ≤ k) {j : Nat} (hdj : d ≤ j) (hjk : j < k) :
    ∀ i : Fin d, v ⟨j,hjk⟩ ≠ framePrefix_l hdk v i := by
  intro i eq
  have he := congrArg Fin.val (frame.injective_l hKP eq)
  change j = i.val at he
  omega

/-- 原 Project 新 binder 对应栈顶新寄存器，旧寄存器沿 Fin.succ 保持。 -/
theorem register_push_injective_l {d} {v : Fin d → M.Domain} {fresh : M.Domain}
    (injective : Function.Injective v) (unused : ∀ i, fresh ≠ v i) :
    Function.Injective (Fin.cases fresh v) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · intro h
      exact (unused j h).elim
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (unused i h.symm).elim
    · intro h
      exact congrArg Fin.succ (injective h)

theorem finConj_delta_l {m k} (φ : Fin k → Formula 1 m) (hd : ∀ i, (φ i).IsDelta0) :
    (finConj_m k φ).IsDelta0 := by
  induction k with
  | zero => rw [finConj_m]; exact .truth
  | succ k ih => rw [finConj_m]; exact .conj (hd 0) (ih (fun i => φ i.succ) (fun i => hd i.succ))

def registerFrame_m (k : Nat) {m} (n : Term m) (v : Fin k → Term m) : Formula 1 m :=
  .conj (pc_num_m k n) (finConj_m k (fun i => pc_num_m i.val (v i)))

theorem registerFrame_closed_l (k : Nat) {m} (n : Term m) (v : Fin k → Term m)
    (hn : n.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) : (registerFrame_m k n v).FreeClosed := by
  simp -implicitDefEqProofs [registerFrame_m,Definitional.Formula.FreeClosed,hn,hv]

theorem registerFrame_delta_l (k : Nat) {m} (n : Term m) (v : Fin k → Term m) :
    (registerFrame_m k n v).IsDelta0 := .conj (pc_num_delta_l ..) (finConj_delta_l _ (fun _ => pc_num_delta_l ..))

theorem registerFrame_sat_l (hE : Extensional M) (k : Nat) {m} (ρ : Env M m) (n : Term m) (v : Fin k → Term m) :
    Formula.satisfies ρ (registerFrame_m k n v) ↔ RegisterFrame_d k (n.eval ρ) (fun i => (v i).eval ρ) := by
  simp only [registerFrame_m,Formula.satisfies_conj_iff,pc_num_sat_l hE,finConj_sat_l]
  exact ⟨fun ⟨a,b⟩ => ⟨a,b⟩,fun h => ⟨h.arity,h.slots⟩⟩

def registersBound_m {m d} (v : Fin d → Term m) (n : Term m) : Formula 1 m :=
  finConj_m d (fun i => .mem (v i) n)

theorem registersBound_closed_l {m d} (v : Fin d → Term m) (n : Term m)
    (hv : ∀ i, (v i).freeSupport = []) (hn : n.freeSupport = []) : (registersBound_m v n).FreeClosed := by
  simp -implicitDefEqProofs [registersBound_m,Definitional.Formula.FreeClosed,hv,hn]

theorem registersBound_delta_l {m d} (v : Fin d → Term m) (n : Term m) :
    (registersBound_m v n).IsDelta0 := finConj_delta_l _ (fun _ => .mem _ _)

theorem registersBound_sat_l {m d} (ρ : Env M m) (v : Fin d → Term m) (n : Term m) :
    Formula.satisfies ρ (registersBound_m v n) ↔ ∀ i, M.mem ((v i).eval ρ) (n.eval ρ) := by
  simp only [registersBound_m,finConj_sat_l,Formula.satisfies_mem_iff]

def registersInjective_m {m d} (v : Fin d → Term m) : Formula 1 m :=
  finConj_m d (fun i => finConj_m d (fun j => if i = j then .truth else .neg (Formula.extensionalEq (v i) (v j))))

theorem registersInjective_closed_l {m d} (v : Fin d → Term m) (hv : ∀ i, (v i).freeSupport = []) :
    (registersInjective_m v).FreeClosed := by
  apply finConj_closed_l
  intro i
  apply finConj_closed_l
  intro j
  by_cases h : i = j
  · simp only [h,↓reduceIte,Definitional.Formula.FreeClosed]
  · simp only [h,↓reduceIte,Definitional.Formula.FreeClosed,Formula.extensionalEq_freeClosed_iff,hv]
    trivial

theorem registersInjective_delta_l {m d} (v : Fin d → Term m) : (registersInjective_m v).IsDelta0 := by
  apply finConj_delta_l
  intro i
  apply finConj_delta_l
  intro j
  by_cases h : i = j
  · rw [if_pos h]
    exact .truth
  · rw [if_neg h]
    exact .neg (.atom _ _ _)

theorem registersInjective_sat_l (hE : Extensional M) {m d} (ρ : Env M m) (v : Fin d → Term m) :
    Formula.satisfies ρ (registersInjective_m v) ↔ Function.Injective (fun i => (v i).eval ρ) := by
  simp only [registersInjective_m,finConj_sat_l]
  constructor
  · intro h i j eq
    by_cases hij : i = j
    · exact hij
    · have different := h i j
      rw [if_neg hij,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE] at different
      exact (different eq).elim
  · intro h i j
    by_cases hij : i = j
    · rw [if_pos hij,Formula.satisfies_truth_iff]
      trivial
    · rw [if_neg hij,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE]
      exact fun eq => hij (h eq)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
