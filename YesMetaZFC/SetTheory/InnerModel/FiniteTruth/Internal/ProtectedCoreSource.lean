import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CoreSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateDelta0

/-! # 原 Cp_test 上指定谓词槽的正规化分类

这是原语法的 Prop 证书，未新增公式 AST。解析和原或非/有界存在正规化保持
指定槽不作普通输入或量词界；mem 的右项可以是该谓词槽。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

inductive ProtectedCore_d : {d : Nat} → Fin d → Cp_test d → Prop where
  | falsum {d} (a : Fin d) : ProtectedCore_d a .falsum
  | truth {d} (a : Fin d) : ProtectedCore_d a .truth
  | mem {d} (a i j : Fin d) (hi : i ≠ a) : ProtectedCore_d a (.mem i j)
  | eq {d} (a i j : Fin d) (hi : i ≠ a) (hj : j ≠ a) : ProtectedCore_d a (.eq i j)
  | nor {d a} {p q : Cp_test d} : ProtectedCore_d a p → ProtectedCore_d a q → ProtectedCore_d a (cpNor_l p q)
  | any {d} (a i : Fin d) (hi : i ≠ a) {p : Cp_test (d+1)} :
      ProtectedCore_d a.succ p → ProtectedCore_d a (.any i p)

theorem ProtectedCore_d.neg_l {d a} {p : Cp_test d} (hp : ProtectedCore_d a p) :
    ProtectedCore_d a (cpNot_l p) := .nor hp hp

theorem ProtectedCore_d.disj_l {d a} {p q : Cp_test d} (hp : ProtectedCore_d a p) (hq : ProtectedCore_d a q) :
    ProtectedCore_d a (cpOr_l p q) := (ProtectedCore_d.nor hp hq).neg_l

theorem ProtectedCore_d.conj_l {d a} {p q : Cp_test d} (hp : ProtectedCore_d a p) (hq : ProtectedCore_d a q) :
    ProtectedCore_d a (cpAnd_l p q) := .nor hp.neg_l hq.neg_l

theorem ProtectedCore_d.imp_l {d a} {p q : Cp_test d} (hp : ProtectedCore_d a p) (hq : ProtectedCore_d a q) :
    ProtectedCore_d a (cpImp_l p q) := hp.neg_l.disj_l hq

theorem ProtectedCore_d.iff_l {d a} {p q : Cp_test d} (hp : ProtectedCore_d a p) (hq : ProtectedCore_d a q) :
    ProtectedCore_d a (cpIff_l p q) := (hp.imp_l hq).conj_l (hq.imp_l hp)

private theorem closed_bound_term_l {d} (t : Term d) (hc : t.freeSupport = []) : ∃ i, t = .bound i := by
  cases t with
  | bound i => exact ⟨i,rfl⟩
  | free i => cases hc

/-- 原 PredicateDelta0 的每个闭合模板都经原解析器和正规化得到准确分类。 -/
theorem predicate_parse_core_l {d a} {φ : Formula 1 d} (hp : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateDelta0 a φ)
    (hc : φ.FreeClosed) : ∃ p, cp_parse_l φ = some p ∧ ProtectedCore_d a (sourceToCore_l p) := by
  induction hp with
  | falsum a => exact ⟨.falsum,rfl,.falsum a⟩
  | truth a => exact ⟨.truth,rfl,.truth a⟩
  | mem a t s ht _ =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨i,rfl⟩ := closed_bound_term_l t hc.1
    obtain ⟨j,rfl⟩ := closed_bound_term_l s hc.2
    exact ⟨.mem i j,rfl,.mem a i j (fun eq => ht (congrArg Term.bound eq))⟩
  | predicate a t ht =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨i,rfl⟩ := closed_bound_term_l t hc.1
    exact ⟨.mem i a,rfl,.mem a i a (fun eq => ht (congrArg Term.bound eq))⟩
  | atom a symbol stage args ha =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨i,hi⟩ := closed_bound_term_l (args.get 0) (hc 0)
    obtain ⟨j,hj⟩ := closed_bound_term_l (args.get 1) (hc 1)
    have ni : i ≠ a := fun eq => ha 0 (hi.trans (congrArg Term.bound eq))
    have nj : j ≠ a := fun eq => ha 1 (hj.trans (congrArg Term.bound eq))
    cases symbol with
    | extensionalEq => exact ⟨.eq i j, (by simp [cp_parse_l,hi,hj,cp_term_l]), .eq a i j ni nj⟩
    | subset =>
      have nz : (0 : Fin _) ≠ a.succ := by
        intro eq
        have values := congrArg Fin.val eq
        change 0 = a.val+1 at values
        omega
      exact ⟨.subset i j, (by simp [cp_parse_l,hi,hj,cp_term_l]),
        (ProtectedCore_d.any a i ni (ProtectedCore_d.mem a.succ 0 j.succ nz).neg_l).neg_l⟩
  | neg _ ih =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p,parsed,core⟩ := ih hc
    exact ⟨.neg p, (by simp [cp_parse_l,parsed]), core.neg_l⟩
  | conj _ _ ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p,parsed,core⟩ := ih hc.1
    obtain ⟨q,other,next⟩ := jh hc.2
    exact ⟨.conj p q, (by simp [cp_parse_l,parsed,other]), core.conj_l next⟩
  | disj _ _ ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p,parsed,core⟩ := ih hc.1
    obtain ⟨q,other,next⟩ := jh hc.2
    exact ⟨.disj p q, (by simp [cp_parse_l,parsed,other]), core.disj_l next⟩
  | imp _ _ ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p,parsed,core⟩ := ih hc.1
    obtain ⟨q,other,next⟩ := jh hc.2
    exact ⟨.imp p q, (by simp [cp_parse_l,parsed,other]), core.imp_l next⟩
  | iff _ _ ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p,parsed,core⟩ := ih hc.1
    obtain ⟨q,other,next⟩ := jh hc.2
    exact ⟨.iff p q, (by simp [cp_parse_l,parsed,other]), core.iff_l next⟩
  | forallMem a t ht _ ih =>
    have closed := (Formula.forallMem_freeClosed t _).mp hc
    obtain ⟨p,parsed,core⟩ := ih closed.2
    obtain ⟨i,rfl⟩ := closed_bound_term_l t closed.1
    refine ⟨.all i p,?_,(ProtectedCore_d.any a i (fun eq => ht (congrArg Term.bound eq)) core.neg_l).neg_l⟩
    change (do let q ← cp_parse_l _; pure (Cp_test.all i q)) = _
    simp [parsed]
  | existsMem a t ht _ ih =>
    have closed := (Formula.existsMem_freeClosed t _).mp hc
    obtain ⟨p,parsed,core⟩ := ih closed.2
    obtain ⟨i,rfl⟩ := closed_bound_term_l t closed.1
    refine ⟨.any i p,?_,ProtectedCore_d.any a i (fun eq => ht (congrArg Term.bound eq)) core⟩
    change (do let q ← cp_parse_l _; pure (Cp_test.any i q)) = _
    simp [parsed]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
