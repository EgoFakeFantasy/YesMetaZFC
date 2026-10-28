import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BooleanSource

/-! # 全部原 Cp_test 的或非/有界存在正规化

复用原源语法。子集化为一个有界全称条件，再以否定和有界存在表示；
全部量词的正文仍按原 Project 栈顶 binder 约定解释。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

inductive CoreSource_d : {d : Nat} → Cp_test d → Prop where
  | falsum {d : Nat} : CoreSource_d (.falsum : Cp_test d)
  | truth {d : Nat} : CoreSource_d (.truth : Cp_test d)
  | mem {d : Nat} (i j : Fin d) : CoreSource_d (.mem i j)
  | eq {d : Nat} (i j : Fin d) : CoreSource_d (.eq i j)
  | nor {d : Nat} {p q : Cp_test d} : CoreSource_d p → CoreSource_d q → CoreSource_d (cpNor_l p q)
  | any {d : Nat} (i : Fin d) {p : Cp_test (d+1)} : CoreSource_d p → CoreSource_d (.any i p)

theorem CoreSource_d.neg_l {d} {p : Cp_test d} (hp : CoreSource_d p) : CoreSource_d (cpNot_l p) := .nor hp hp
theorem CoreSource_d.disj_l {d} {p q : Cp_test d} (hp : CoreSource_d p) (hq : CoreSource_d q) :
    CoreSource_d (cpOr_l p q) := (CoreSource_d.nor hp hq).neg_l
theorem CoreSource_d.conj_l {d} {p q : Cp_test d} (hp : CoreSource_d p) (hq : CoreSource_d q) :
    CoreSource_d (cpAnd_l p q) := .nor hp.neg_l hq.neg_l
theorem CoreSource_d.imp_l {d} {p q : Cp_test d} (hp : CoreSource_d p) (hq : CoreSource_d q) :
    CoreSource_d (cpImp_l p q) := hp.neg_l.disj_l hq
theorem CoreSource_d.iff_l {d} {p q : Cp_test d} (hp : CoreSource_d p) (hq : CoreSource_d q) :
    CoreSource_d (cpIff_l p q) := (hp.imp_l hq).conj_l (hq.imp_l hp)

def sourceToCore_l : {d : Nat} → Cp_test d → Cp_test d
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem i j => .mem i j
  | _, .eq i j => .eq i j
  | _, .subset i j => cpNot_l (.any i (cpNot_l (.mem 0 j.succ)))
  | _, .neg p => cpNot_l (sourceToCore_l p)
  | _, .conj p q => cpAnd_l (sourceToCore_l p) (sourceToCore_l q)
  | _, .disj p q => cpOr_l (sourceToCore_l p) (sourceToCore_l q)
  | _, .imp p q => cpImp_l (sourceToCore_l p) (sourceToCore_l q)
  | _, .iff p q => cpIff_l (sourceToCore_l p) (sourceToCore_l q)
  | _, .all i p => cpNot_l (.any i (cpNot_l (sourceToCore_l p)))
  | _, .any i p => .any i (sourceToCore_l p)

theorem sourceToCore_shape_l {d} (p : Cp_test d) : CoreSource_d (sourceToCore_l p) := by
  induction p with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem i j => exact .mem i j
  | eq i j => exact .eq i j
  | subset i j => exact (CoreSource_d.any i (CoreSource_d.mem 0 j.succ).neg_l).neg_l
  | neg _ ih => exact ih.neg_l
  | conj _ _ ihp ihq => exact ihp.conj_l ihq
  | disj _ _ ihp ihq => exact ihp.disj_l ihq
  | imp _ _ ihp ihq => exact ihp.imp_l ihq
  | iff _ _ ihp ihq => exact ihp.iff_l ihq
  | all i _ ih => exact (CoreSource_d.any i ih.neg_l).neg_l
  | any i _ ih => exact .any i ih

def sourceDepth_l : {d : Nat} → Cp_test d → Nat
  | _, .falsum | _, .truth | _, .mem _ _ | _, .eq _ _ => 0
  | _, .subset _ _ => 1
  | _, .neg p => sourceDepth_l p
  | _, .conj p q | _, .disj p q | _, .imp p q | _, .iff p q => max (sourceDepth_l p) (sourceDepth_l q)
  | _, .all _ p | _, .any _ p => sourceDepth_l p + 1

/-- 包含子集和全部有界量词的原源语义，在正规化后保持。 -/
theorem sourceToCore_sat_l {d} (p : Cp_test d) (ρ : Env M d) :
    Formula.satisfies ρ (cp_test_formula_l (sourceToCore_l p)) ↔ Formula.satisfies ρ (cp_test_formula_l p) := by
  classical
  induction p with
  | falsum | truth | mem _ _ | eq _ _ => exact Iff.rfl
  | neg _ ih =>
    simpa only [sourceToCore_l,cpNot_sat_l,cp_test_formula_l,Formula.satisfies_neg_iff] using not_congr (ih ρ)
  | conj _ _ ihp ihq =>
    simpa only [sourceToCore_l,cpAnd_sat_l,cp_test_formula_l,Formula.satisfies_conj_iff] using and_congr (ihp ρ) (ihq ρ)
  | disj _ _ ihp ihq =>
    simpa only [sourceToCore_l,cpOr_sat_l,cp_test_formula_l,Formula.satisfies_disj_iff] using or_congr (ihp ρ) (ihq ρ)
  | imp _ _ ihp ihq =>
    simpa only [sourceToCore_l,cpImp_sat_l,cp_test_formula_l,Formula.satisfies_imp_iff] using imp_congr (ihp ρ) (ihq ρ)
  | iff _ _ ihp ihq =>
    simpa only [sourceToCore_l,cpIff_sat_l,cp_test_formula_l,Formula.satisfies_iff_iff] using iff_congr (ihp ρ) (ihq ρ)
  | any i p ih =>
    simp only [sourceToCore_l,cp_test_formula_l,Formula.satisfies_existsMem_iff]
    exact exists_congr (fun x => and_congr_right (fun _ => ih (ρ.push x)))
  | all i p ih =>
    simp only [sourceToCore_l,cpNot_sat_l,cp_test_formula_l,Formula.satisfies_existsMem_iff,Formula.satisfies_forallMem_iff]
    constructor
    · intro h x hx
      by_cases yes : Formula.satisfies (ρ.push x) (cp_test_formula_l p)
      · exact yes
      · exact (h ⟨x,hx,fun hn => yes ((ih (ρ.push x)).mp hn)⟩).elim
    · intro h hx
      obtain ⟨x,mem,hn⟩ := hx
      exact hn ((ih (ρ.push x)).mpr (h x mem))
  | subset i j =>
    simp only [sourceToCore_l,cpNot_sat_l,cp_test_formula_l,Formula.satisfies_existsMem_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_subset_iff]
    change (¬ ∃ x, M.mem x (ρ.bound i) ∧ ¬ M.mem x (ρ.bound j)) ↔ M.MemberSubset (ρ.bound i) (ρ.bound j)
    constructor
    · intro h x hx
      by_cases yes : M.mem x (ρ.bound j)
      · exact yes
      · exact (h ⟨x,hx,yes⟩).elim
    · intro h hx
      obtain ⟨x,mem,hn⟩ := hx
      exact hn (h x mem)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
