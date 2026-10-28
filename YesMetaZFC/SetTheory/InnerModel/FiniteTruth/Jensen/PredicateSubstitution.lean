import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UnrestrictedCanonicalWithin

/-! # 原 AST 谓词出现证书的绑定替换运输 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project


theorem predicate_bound_succ_inj_l {d} {i j : Fin d}
    (eq : (Definitional.Term.bound i.succ : Term (d+1)) = .bound j.succ) : i = j := by
  apply Fin.ext
  have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
  change i.val+1 = j.val+1 at vals
  omega

theorem predicate_weaken_apart_l {d} {a : Fin d} {t : Term d} (apart : t ≠ .bound a) :
    t.weaken ≠ .bound a.succ := by
  cases t with
  | bound i =>
      intro eq
      apply apart
      exact congrArg Definitional.Term.bound (predicate_bound_succ_inj_l eq)
  | free v => intro eq; cases eq

theorem predicate_term_bind_apart_l {d m} {a : Fin d} {b : Fin m} (e : Fin d → Term m)
    (ordinary : ∀ i, i ≠ a → e i ≠ .bound b) (t : Term d) (apart : t ≠ .bound a) :
    t.bind e ≠ .bound b := by
  cases t with
  | bound i => exact ordinary i (fun eq => apart (congrArg Definitional.Term.bound eq))
  | free v => intro eq; cases eq

theorem predicate_term_bind_all_l {d m} {b : Fin m} (e : Fin d → Term m)
    (ordinary : ∀ i, e i ≠ .bound b) (t : Term d) : t.bind e ≠ .bound b := by
  cases t with
  | bound i => exact ordinary i
  | free v => intro eq; cases eq

theorem predicate_lift_substitution_l {d m} {a : Fin d} {b : Fin m} (e : Fin d → Term m)
    (protectedSlot : e a = .bound b) (ordinary : ∀ i, i ≠ a → e i ≠ .bound b) :
    Term.liftSubstitution e a.succ = .bound b.succ ∧
      ∀ i, i ≠ a.succ → Term.liftSubstitution e i ≠ .bound b.succ := by
  constructor
  · change (e a).weaken = .bound b.succ
    rw [protectedSlot]
    rfl
  · intro i
    refine Fin.cases (fun _ eq => ?_) (fun j ne => ?_) i
    · have bad : (0 : Fin (m+1)) = b.succ := Definitional.Term.bound.inj eq
      have vals := congrArg Fin.val bad
      change (0 : Nat) = b.val+1 at vals
      omega
    · exact predicate_weaken_apart_l (ordinary j (fun eq => ne (congrArg Fin.succ eq)))

theorem PredicateDelta0.bind_l {d a} {φ : Formula 1 d} (h : PredicateDelta0 a φ)
    {m} {b : Fin m} (e : Fin d → Term m) (protectedSlot : e a = .bound b)
    (ordinary : ∀ i, i ≠ a → e i ≠ .bound b) : PredicateDelta0 b (φ.bind e) := by
  induction h generalizing m with
  | falsum => exact .falsum _
  | truth => exact .truth _
  | mem a t s ht hs =>
      exact .mem _ _ _ (predicate_term_bind_apart_l e ordinary t ht) (predicate_term_bind_apart_l e ordinary s hs)
  | predicate a t ht =>
      simpa only [Definitional.Formula.bind,Definitional.Term.bind,protectedSlot] using!
        (PredicateDelta0.predicate b (t.bind e) (predicate_term_bind_apart_l e ordinary t ht))
  | atom a symbol stage args apart =>
      apply PredicateDelta0.atom
      intro i
      simpa only [Definitional.TermVector.get_bind] using predicate_term_bind_apart_l e ordinary (args i) (apart i)
  | neg h ih => exact .neg (ih e protectedSlot ordinary)
  | conj h g ih jh => exact .conj (ih e protectedSlot ordinary) (jh e protectedSlot ordinary)
  | disj h g ih jh => exact .disj (ih e protectedSlot ordinary) (jh e protectedSlot ordinary)
  | imp h g ih jh => exact .imp (ih e protectedSlot ordinary) (jh e protectedSlot ordinary)
  | iff h g ih jh => exact .iff (ih e protectedSlot ordinary) (jh e protectedSlot ordinary)
  | forallMem a t ht h ih =>
      obtain ⟨protectNext,ordinaryNext⟩ := predicate_lift_substitution_l e protectedSlot ordinary
      have termLift : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      have newestLift : Term.bind (Term.liftSubstitution e) Term.newest = (Term.newest : Term (m+1)) := rfl
      simpa only [Formula.forallMem,Definitional.Formula.bind,termLift,newestLift] using!
        (PredicateDelta0.forallMem b (t.bind e) (predicate_term_bind_apart_l e ordinary t ht)
          (ih (Term.liftSubstitution e) protectNext ordinaryNext))
  | existsMem a t ht h ih =>
      obtain ⟨protectNext,ordinaryNext⟩ := predicate_lift_substitution_l e protectedSlot ordinary
      have termLift : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      have newestLift : Term.bind (Term.liftSubstitution e) Term.newest = (Term.newest : Term (m+1)) := rfl
      simpa only [Formula.existsMem,Definitional.Formula.bind,termLift,newestLift] using!
        (PredicateDelta0.existsMem b (t.bind e) (predicate_term_bind_apart_l e ordinary t ht)
          (ih (Term.liftSubstitution e) protectNext ordinaryNext))

theorem PredicateDelta0.weaken_l {d a} {φ : Formula 1 d} (h : PredicateDelta0 a φ) :
    PredicateDelta0 a.succ φ.weaken := by
  apply h.bind_l (fun i => .bound i.succ) rfl
  intro i ne eq
  exact ne (predicate_bound_succ_inj_l eq)

theorem delta0_predicate_bind_l {d} {φ : Formula 1 d} (h : φ.IsDelta0) {m} (b : Fin m)
    (e : Fin d → Term m) (ordinary : ∀ i, e i ≠ .bound b) : PredicateDelta0 b (φ.bind e) := by
  induction h generalizing m with
  | falsum => exact .falsum _
  | truth => exact .truth _
  | mem t s => exact .mem _ _ _ (predicate_term_bind_all_l e ordinary t) (predicate_term_bind_all_l e ordinary s)
  | atom symbol stage args =>
      apply PredicateDelta0.atom
      intro i
      simpa only [Definitional.TermVector.get_bind] using predicate_term_bind_all_l e ordinary (args i)
  | neg h ih => exact .neg (ih b e ordinary)
  | conj h g ih jh => exact .conj (ih b e ordinary) (jh b e ordinary)
  | disj h g ih jh => exact .disj (ih b e ordinary) (jh b e ordinary)
  | imp h g ih jh => exact .imp (ih b e ordinary) (jh b e ordinary)
  | iff h g ih jh => exact .iff (ih b e ordinary) (jh b e ordinary)
  | forallMem t h ih =>
      have next : ∀ i, Term.liftSubstitution e i ≠ .bound b.succ := by
        intro i
        refine Fin.cases (fun eq => ?_) (fun j => predicate_weaken_apart_l (ordinary j)) i
        have bad : (0 : Fin (m+1)) = b.succ := Definitional.Term.bound.inj eq
        have vals := congrArg Fin.val bad
        change (0 : Nat) = b.val+1 at vals
        omega
      have termLift : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      have newestLift : Term.bind (Term.liftSubstitution e) Term.newest = (Term.newest : Term (m+1)) := rfl
      simpa only [Formula.forallMem,Definitional.Formula.bind,termLift,newestLift] using!
        (PredicateDelta0.forallMem b (t.bind e) (predicate_term_bind_all_l e ordinary t)
          (ih b.succ (Term.liftSubstitution e) next))
  | existsMem t h ih =>
      have next : ∀ i, Term.liftSubstitution e i ≠ .bound b.succ := by
        intro i
        refine Fin.cases (fun eq => ?_) (fun j => predicate_weaken_apart_l (ordinary j)) i
        have bad : (0 : Fin (m+1)) = b.succ := Definitional.Term.bound.inj eq
        have vals := congrArg Fin.val bad
        change (0 : Nat) = b.val+1 at vals
        omega
      have termLift : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      have newestLift : Term.bind (Term.liftSubstitution e) Term.newest = (Term.newest : Term (m+1)) := rfl
      simpa only [Formula.existsMem,Definitional.Formula.bind,termLift,newestLift] using!
        (PredicateDelta0.existsMem b (t.bind e) (predicate_term_bind_all_l e ordinary t)
          (ih b.succ (Term.liftSubstitution e) next))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
