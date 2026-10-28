import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AmenabilitySyntax

/-! # 原 AST 中指定参数只作一元谓词的有界出现证书

证书分类已有公式；不增设语言、公式数据或推导关系。
指定槽 a 仅出现为 t∈a 的右项，不能作为量词界或集合参数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project

inductive PredicateDelta0 : {d : Nat} → Fin d → Formula 1 d → Prop where
  | falsum {d} (a : Fin d) : PredicateDelta0 a .falsum
  | truth {d} (a : Fin d) : PredicateDelta0 a .truth
  | mem {d} (a : Fin d) (t s : Term d) (ht : t ≠ .bound a) (hs : s ≠ .bound a) :
      PredicateDelta0 a (.mem t s)
  | predicate {d} (a : Fin d) (t : Term d) (ht : t ≠ .bound a) :
      PredicateDelta0 a (.mem t (.bound a))
  | atom {d} (a : Fin d) (symbol : CoreAtom) (stage : coreSignature.stage symbol < 1)
      (args : Definitional.TermVector (coreSignature.arity symbol) d)
      (ha : ∀ i, args i ≠ .bound a) : PredicateDelta0 a (.atom symbol stage args)
  | neg {d a} {φ : Formula 1 d} : PredicateDelta0 a φ → PredicateDelta0 a (.neg φ)
  | conj {d a} {φ ψ : Formula 1 d} : PredicateDelta0 a φ → PredicateDelta0 a ψ → PredicateDelta0 a (.conj φ ψ)
  | disj {d a} {φ ψ : Formula 1 d} : PredicateDelta0 a φ → PredicateDelta0 a ψ → PredicateDelta0 a (.disj φ ψ)
  | imp {d a} {φ ψ : Formula 1 d} : PredicateDelta0 a φ → PredicateDelta0 a ψ → PredicateDelta0 a (.imp φ ψ)
  | iff {d a} {φ ψ : Formula 1 d} : PredicateDelta0 a φ → PredicateDelta0 a ψ → PredicateDelta0 a (.iff φ ψ)
  | forallMem {d} (a : Fin d) (t : Term d) (ht : t ≠ .bound a) {φ : Formula 1 (d+1)} :
      PredicateDelta0 a.succ φ → PredicateDelta0 a (Formula.forallMem t φ)
  | existsMem {d} (a : Fin d) (t : Term d) (ht : t ≠ .bound a) {φ : Formula 1 (d+1)} :
      PredicateDelta0 a.succ φ → PredicateDelta0 a (Formula.existsMem t φ)

theorem PredicateDelta0.delta0_l {d a} {φ : Formula 1 d} (h : PredicateDelta0 a φ) : φ.IsDelta0 := by
  induction h with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem => exact .mem _ _
  | predicate => exact .mem _ _
  | atom => exact .atom _ _ _
  | neg _ ih => exact .neg ih
  | conj _ _ ih jh => exact .conj ih jh
  | disj _ _ ih jh => exact .disj ih jh
  | imp _ _ ih jh => exact .imp ih jh
  | iff _ _ ih jh => exact .iff ih jh
  | forallMem _ _ _ _ ih => exact .forallMem _ ih
  | existsMem _ _ _ _ ih => exact .existsMem _ ih

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
