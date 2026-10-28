import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.BoundedSeparation

/-! # 原隶属语言中的实际集合迹与 amenability

A 是背景模型内的集合编码，未要求 A∈C。此处不构造全公式真值谓词。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PredicateTrace_d (A X Y : M.Domain) : Prop :=
  ∀ z, M.mem z Y ↔ M.mem z X ∧ M.mem z A

def predicateTrace_m {d} (A X Y : Term d) : Formula 1 d :=
  .conj (Formula.subset Y X) <| Formula.forallMem X <|
    .iff (.mem .newest Y.weaken) (.mem .newest A.weaken)

@[simp] theorem predicateTrace_closed_l {d} (A X Y : Term d)
    (hA : A.freeSupport = []) (hX : X.freeSupport = []) (hY : Y.freeSupport = []) :
    (predicateTrace_m A X Y).FreeClosed := by
  simp -implicitDefEqProofs [predicateTrace_m,Definitional.Formula.FreeClosed,hA,hX,hY]

theorem predicateTrace_delta0_l {d} (A X Y : Term d) : (predicateTrace_m A X Y).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.mem _ _)))

theorem predicateTrace_sat_l {d} (ρ : Env M d) (A X Y : Term d) :
    Formula.satisfies ρ (predicateTrace_m A X Y) ↔ PredicateTrace_d (A.eval ρ) (X.eval ρ) (Y.eval ρ) := by
  simp only [predicateTrace_m,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨sub,eq⟩ z
    exact ⟨fun hz => ⟨sub z hz,(eq z (sub z hz)).mp hz⟩,
      fun ⟨hx,ha⟩ => (eq z hx).mpr ha⟩
  · intro trace
    exact ⟨fun z hz => ((trace z).mp hz).1,fun z hx =>
      ⟨fun hz => ((trace z).mp hz).2,fun ha => (trace z).mpr ⟨hx,ha⟩⟩⟩

def AmenableSet_d (C A : M.Domain) : Prop :=
  M.MemberSubset A C ∧ ∀ X, M.mem X C → ∃ Y, M.mem Y C ∧ PredicateTrace_d A X Y

def amenableSet_m {d} (C A : Term d) : Formula 1 d :=
  .conj (Formula.subset A C) <| Formula.forallMem C <| Formula.existsMem C.weaken <|
    predicateTrace_m A.weaken.weaken (.bound 1) .newest

@[simp] theorem amenableSet_closed_l {d} (C A : Term d) (hC : C.freeSupport = []) (hA : A.freeSupport = []) :
    (amenableSet_m C A).FreeClosed := by
  simp -implicitDefEqProofs [amenableSet_m,Definitional.Formula.FreeClosed,hC,hA]

theorem amenableSet_sat_l {d} (ρ : Env M d) (C A : Term d) :
    Formula.satisfies ρ (amenableSet_m C A) ↔ AmenableSet_d (C.eval ρ) (A.eval ρ) := by
  simp only [amenableSet_m,AmenableSet_d,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,predicateTrace_sat_l,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem PredicateTrace_d.unique_l (hE : Extensional M) {A X Y Z : M.Domain}
    (first : PredicateTrace_d A X Y) (second : PredicateTrace_d A X Z) : Y = Z :=
  hE.eq_of_same_members _ _ (fun z => (first z).trans (second z).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
