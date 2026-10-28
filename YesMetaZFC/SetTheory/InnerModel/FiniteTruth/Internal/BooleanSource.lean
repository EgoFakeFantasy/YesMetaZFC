import YesMetaZFC.SetTheory.InnerModel.Computation.Delta0

/-! # 原 Cp_test 布尔片段的或非正规化

仅为上游原语法加片段谓词，不引入平行公式 AST 或推导核。子集原子和有界
量词不在本片段；它们仍须在后续新鲜变量布局下编译。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def cpNor_l {d} (p q : Cp_test d) : Cp_test d := .neg (.disj p q)
def cpNot_l {d} (p : Cp_test d) : Cp_test d := cpNor_l p p
def cpOr_l {d} (p q : Cp_test d) : Cp_test d := cpNot_l (cpNor_l p q)
def cpAnd_l {d} (p q : Cp_test d) : Cp_test d := cpNor_l (cpNot_l p) (cpNot_l q)
def cpImp_l {d} (p q : Cp_test d) : Cp_test d := cpOr_l (cpNot_l p) q
def cpIff_l {d} (p q : Cp_test d) : Cp_test d := cpAnd_l (cpImp_l p q) (cpImp_l q p)

inductive NorSource_d {d : Nat} : Cp_test d → Prop where
  | falsum : NorSource_d .falsum
  | truth : NorSource_d .truth
  | mem (i j : Fin d) : NorSource_d (.mem i j)
  | eq (i j : Fin d) : NorSource_d (.eq i j)
  | nor {p q} : NorSource_d p → NorSource_d q → NorSource_d (cpNor_l p q)

theorem NorSource_d.neg_l {d} {p : Cp_test d} (hp : NorSource_d p) : NorSource_d (cpNot_l p) := .nor hp hp
theorem NorSource_d.disj_l {d} {p q : Cp_test d} (hp : NorSource_d p) (hq : NorSource_d q) :
    NorSource_d (cpOr_l p q) := (NorSource_d.nor hp hq).neg_l
theorem NorSource_d.conj_l {d} {p q : Cp_test d} (hp : NorSource_d p) (hq : NorSource_d q) :
    NorSource_d (cpAnd_l p q) := .nor hp.neg_l hq.neg_l
theorem NorSource_d.imp_l {d} {p q : Cp_test d} (hp : NorSource_d p) (hq : NorSource_d q) :
    NorSource_d (cpImp_l p q) := hp.neg_l.disj_l hq
theorem NorSource_d.iff_l {d} {p q : Cp_test d} (hp : NorSource_d p) (hq : NorSource_d q) :
    NorSource_d (cpIff_l p q) := (hp.imp_l hq).conj_l (hq.imp_l hp)

def BooleanSource_d : {d : Nat} → Cp_test d → Prop
  | _, .falsum | _, .truth | _, .mem _ _ | _, .eq _ _ => True
  | _, .subset _ _ | _, .all _ _ | _, .any _ _ => False
  | _, .neg p => BooleanSource_d p
  | _, .conj p q | _, .disj p q | _, .imp p q | _, .iff p q => BooleanSource_d p ∧ BooleanSource_d q

def booleanToNor_l : {d : Nat} → Cp_test d → Cp_test d
  | _, .falsum => .falsum
  | _, .truth => .truth
  | _, .mem i j => .mem i j
  | _, .eq i j => .eq i j
  | _, .subset i j => .subset i j
  | _, .all i p => .all i p
  | _, .any i p => .any i p
  | _, .neg p => cpNot_l (booleanToNor_l p)
  | _, .conj p q => cpAnd_l (booleanToNor_l p) (booleanToNor_l q)
  | _, .disj p q => cpOr_l (booleanToNor_l p) (booleanToNor_l q)
  | _, .imp p q => cpImp_l (booleanToNor_l p) (booleanToNor_l q)
  | _, .iff p q => cpIff_l (booleanToNor_l p) (booleanToNor_l q)

theorem booleanToNor_shape_l {d} (p : Cp_test d) (hp : BooleanSource_d p) : NorSource_d (booleanToNor_l p) := by
  induction p with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem i j => exact .mem i j
  | eq i j => exact .eq i j
  | subset _ _ | all _ _ _ | any _ _ _ => exact hp.elim
  | neg _ ih => exact (ih hp).neg_l
  | conj _ _ ihp ihq => exact (ihp hp.1).conj_l (ihq hp.2)
  | disj _ _ ihp ihq => exact (ihp hp.1).disj_l (ihq hp.2)
  | imp _ _ ihp ihq => exact (ihp hp.1).imp_l (ihq hp.2)
  | iff _ _ ihp ihq => exact (ihp hp.1).iff_l (ihq hp.2)

theorem cpNot_sat_l {d} (ρ : Env M d) (p : Cp_test d) :
    Formula.satisfies ρ (cp_test_formula_l (cpNot_l p)) ↔ ¬ Formula.satisfies ρ (cp_test_formula_l p) := by
  simp only [cpNot_l,cpNor_l,cp_test_formula_l,Formula.satisfies_neg_iff,Formula.satisfies_disj_iff,or_self]

theorem cpOr_sat_l {d} (ρ : Env M d) (p q : Cp_test d) :
    Formula.satisfies ρ (cp_test_formula_l (cpOr_l p q)) ↔
      Formula.satisfies ρ (cp_test_formula_l p) ∨ Formula.satisfies ρ (cp_test_formula_l q) := by
  classical
  simp only [cpOr_l,cpNot_sat_l,cpNor_l,cp_test_formula_l,
    Formula.satisfies_neg_iff,Formula.satisfies_disj_iff,Classical.not_not]

theorem cpAnd_sat_l {d} (ρ : Env M d) (p q : Cp_test d) :
    Formula.satisfies ρ (cp_test_formula_l (cpAnd_l p q)) ↔
      Formula.satisfies ρ (cp_test_formula_l p) ∧ Formula.satisfies ρ (cp_test_formula_l q) := by
  classical
  simp only [cpAnd_l,cpNor_l,cp_test_formula_l,Formula.satisfies_neg_iff,
    Formula.satisfies_disj_iff,cpNot_sat_l,not_or,Classical.not_not]

theorem cpImp_sat_l {d} (ρ : Env M d) (p q : Cp_test d) :
    Formula.satisfies ρ (cp_test_formula_l (cpImp_l p q)) ↔
      (Formula.satisfies ρ (cp_test_formula_l p) → Formula.satisfies ρ (cp_test_formula_l q)) := by
  classical
  simp only [cpImp_l,cpOr_sat_l,cpNot_sat_l]
  constructor
  · rintro (hn | hq) hp
    · exact (hn hp).elim
    · exact hq
  · intro h
    by_cases hp : Formula.satisfies ρ (cp_test_formula_l p)
    · exact Or.inr (h hp)
    · exact Or.inl hp

theorem cpIff_sat_l {d} (ρ : Env M d) (p q : Cp_test d) :
    Formula.satisfies ρ (cp_test_formula_l (cpIff_l p q)) ↔
      (Formula.satisfies ρ (cp_test_formula_l p) ↔ Formula.satisfies ρ (cp_test_formula_l q)) := by
  simp only [cpIff_l,cpAnd_sat_l,cpImp_sat_l,iff_def]

/-- 正规化保持任意原模型、任意源环境中的语义。 -/
theorem booleanToNor_sat_l {d} (p : Cp_test d) (hp : BooleanSource_d p) (ρ : Env M d) :
    Formula.satisfies ρ (cp_test_formula_l (booleanToNor_l p)) ↔ Formula.satisfies ρ (cp_test_formula_l p) := by
  induction p with
  | falsum | truth | mem _ _ | eq _ _ => exact Iff.rfl
  | subset _ _ | all _ _ _ | any _ _ _ => exact hp.elim
  | neg _ ih =>
    simpa only [booleanToNor_l,cpNot_sat_l,cp_test_formula_l,Formula.satisfies_neg_iff] using not_congr (ih hp ρ)
  | conj _ _ ihp ihq =>
    simpa only [booleanToNor_l,cpAnd_sat_l,cp_test_formula_l,Formula.satisfies_conj_iff] using and_congr (ihp hp.1 ρ) (ihq hp.2 ρ)
  | disj _ _ ihp ihq =>
    simpa only [booleanToNor_l,cpOr_sat_l,cp_test_formula_l,Formula.satisfies_disj_iff] using or_congr (ihp hp.1 ρ) (ihq hp.2 ρ)
  | imp _ _ ihp ihq =>
    simpa only [booleanToNor_l,cpImp_sat_l,cp_test_formula_l,Formula.satisfies_imp_iff] using imp_congr (ihp hp.1 ρ) (ihq hp.2 ρ)
  | iff _ _ ihp ihq =>
    simpa only [booleanToNor_l,cpIff_sat_l,cp_test_formula_l,Formula.satisfies_iff_iff] using iff_congr (ihp hp.1 ρ) (ihq hp.2 ρ)

/-- 原解析成功后的源公式与 Cp_test 公式精确同义，使用上游实际集合程序比较。 -/
theorem parsedSource_sat_l (hKP : M.Models KP) {d} {φ : Formula 1 d} {p : Cp_test d}
    (hd : φ.IsDelta0) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p) (ρ : Env M d) :
    Formula.satisfies ρ (cp_test_formula_l p) ↔ Formula.satisfies ρ φ := by
  obtain ⟨q,hq,source⟩ := cp_parse_correct_l hd hc
  have eq : q = p := Option.some.inj (hq.symm.trans parsed)
  subst q
  obtain ⟨r,hr,target⟩ := cp_parse_correct_l (cp_test_delta_l p) (cp_test_closed_l p)
  have eq : r = p := Option.some.inj (hr.symm.trans (cp_parse_test_l p))
  subst r
  obtain ⟨Y,hY⟩ := cp_eval_total_l hKP (cp_test_code_l p) ρ
  obtain ⟨e,he⟩ := KP.exists_empty hKP
  have left := (target M hKP ρ Y hY e).trans (and_iff_right he)
  have right := (source M hKP ρ Y hY e).trans (and_iff_right he)
  exact left.symm.trans right

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
