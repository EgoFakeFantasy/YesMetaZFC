import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateDelta0

/-! # 外部集合谓词在原有界公式中的准确迹局部化 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

structure PredicateTraceEnv_d {d} (a : Fin d) (U : M.Domain) (ρ η : Env M d) : Prop where
  boundEq : ∀ i, i ≠ a → ρ.bound i = η.bound i
  freeEq : ρ.free = η.free
  boundMem : ∀ i, i ≠ a → M.mem (ρ.bound i) U
  freeMem : ∀ v, M.mem (ρ.free v) U
  trace : PredicateTrace_d (ρ.bound a) U (η.bound a)

theorem PredicateTraceEnv_d.term_eq_l {d a U} {ρ η : Env M d} (h : PredicateTraceEnv_d a U ρ η)
    (t : Term d) (ht : t ≠ .bound a) : t.eval ρ = t.eval η := by
  cases t with
  | bound i => exact h.boundEq i (fun eq => ht (congrArg Definitional.Term.bound eq))
  | free v => exact congrFun h.freeEq v

theorem PredicateTraceEnv_d.term_mem_l {d a U} {ρ η : Env M d} (h : PredicateTraceEnv_d a U ρ η)
    (t : Term d) (ht : t ≠ .bound a) : M.mem (t.eval ρ) U := by
  cases t with
  | bound i => exact h.boundMem i (fun eq => ht (congrArg Definitional.Term.bound eq))
  | free v => exact h.freeMem v

theorem PredicateTraceEnv_d.push_l {d a U} {ρ η : Env M d} (h : PredicateTraceEnv_d a U ρ η)
    {x : M.Domain} (hx : M.mem x U) : PredicateTraceEnv_d a.succ U (ρ.push x) (η.push x) := by
  constructor
  · intro i
    refine Fin.cases (fun _ => rfl) (fun j ne => ?_) i
    exact h.boundEq j (fun eq => ne (congrArg Fin.succ eq))
  · exact h.freeEq
  · intro i
    refine Fin.cases (fun _ => hx) (fun j ne => ?_) i
    exact h.boundMem j (fun eq => ne (congrArg Fin.succ eq))
  · exact h.freeMem
  · exact h.trace

theorem PredicateDelta0.localize_l {d a} {φ : Formula 1 d} (h : PredicateDelta0 a φ)
    {U : M.Domain} (trans : M.TransitiveSet U) (ρ η : Env M d) (env : PredicateTraceEnv_d a U ρ η) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  induction h with
  | falsum => simp only [Formula.satisfies_falsum_iff]
  | truth => simp only [Formula.satisfies_truth_iff]
  | mem a t s ht hs =>
      simp only [Formula.satisfies_mem_iff,env.term_eq_l t ht,env.term_eq_l s hs]
  | predicate a t ht =>
      simp only [Formula.satisfies_mem_iff]
      change M.mem (t.eval ρ) (ρ.bound a) ↔ M.mem (t.eval η) (η.bound a)
      rw [←env.term_eq_l t ht]
      exact ⟨fun hz => (env.trace _).mpr ⟨env.term_mem_l t ht,hz⟩,
        fun hz => ((env.trace _).mp hz).2⟩
  | atom a symbol stage args ha =>
      cases symbol with
      | extensionalEq =>
          simp only [Formula.satisfies_atom_extensionalEq_iff,env.term_eq_l (args 0) (ha 0),env.term_eq_l (args 1) (ha 1)]
      | subset =>
          simp only [Formula.satisfies_atom_subset_iff,env.term_eq_l (args 0) (ha 0),env.term_eq_l (args 1) (ha 1)]
  | neg h ih =>
      simp only [Formula.satisfies_neg_iff]
      exact not_congr (ih ρ η env)
  | conj h g ih jh =>
      simp only [Formula.satisfies_conj_iff]
      exact and_congr (ih ρ η env) (jh ρ η env)
  | disj h g ih jh =>
      simp only [Formula.satisfies_disj_iff]
      exact or_congr (ih ρ η env) (jh ρ η env)
  | imp h g ih jh =>
      simp only [Formula.satisfies_imp_iff]
      exact imp_congr (ih ρ η env) (jh ρ η env)
  | iff h g ih jh =>
      simp only [Formula.satisfies_iff_iff]
      exact iff_congr (ih ρ η env) (jh ρ η env)
  | forallMem a t ht h ih =>
      simp only [Formula.satisfies_forallMem_iff]
      rw [←env.term_eq_l t ht]
      constructor
      · intro all x hx
        exact (ih (ρ.push x) (η.push x) (env.push_l (trans _ (env.term_mem_l t ht) x hx))).mp (all x hx)
      · intro all x hx
        exact (ih (ρ.push x) (η.push x) (env.push_l (trans _ (env.term_mem_l t ht) x hx))).mpr (all x hx)
  | existsMem a t ht h ih =>
      simp only [Formula.satisfies_existsMem_iff]
      rw [←env.term_eq_l t ht]
      constructor
      · rintro ⟨x,hx,good⟩
        exact ⟨x,hx,(ih (ρ.push x) (η.push x) (env.push_l (trans _ (env.term_mem_l t ht) x hx))).mp good⟩
      · rintro ⟨x,hx,good⟩
        exact ⟨x,hx,(ih (ρ.push x) (η.push x) (env.push_l (trans _ (env.term_mem_l t ht) x hx))).mpr good⟩


theorem predicateUnary_localize_l {p} (φ : UnarySchema (p+1))
    (useCert : PredicateDelta0 (1 : Fin (p+2)) φ.body) (ρ : Env M p) {A B U X : M.Domain}
    (trans : M.TransitiveSet U) (hX : M.mem X U) (params : ∀ i, M.mem (ρ.bound i) U)
    (trace : PredicateTrace_d A U B) {x : M.Domain} (hx : M.mem x X) :
    φ.denote (ρ.push A) x ↔ φ.denote (ρ.push B) x := by
  let τ : Env M p := ⟨ρ.bound,fun _ => X⟩
  let σA := (τ.push A).push x
  let σB := (τ.push B).push x
  have bridge : PredicateTraceEnv_d (1 : Fin (p+2)) U σA σB := by
    constructor
    · intro i
      exact Fin.cases (fun _ => rfl) (fun j => Fin.cases (fun ne => False.elim (ne rfl)) (fun _ _ => rfl) j) i
    · rfl
    · intro i
      exact Fin.cases (fun _ => trans X hX x hx)
        (fun j => Fin.cases (fun ne => False.elim (ne rfl)) (fun k _ => params k) j) i
    · exact fun _ => hX
    · exact trace
  have leftBridge : φ.denote (ρ.push A) x ↔ Formula.satisfies σA φ.body :=
    Formula.closed_env_l _ φ.freeClosed rfl
  have rightBridge : φ.denote (ρ.push B) x ↔ Formula.satisfies σB φ.body :=
    Formula.closed_env_l _ φ.freeClosed rfl
  exact leftBridge.trans ((useCert.localize_l trans σA σB bridge).trans rightBridge.symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
