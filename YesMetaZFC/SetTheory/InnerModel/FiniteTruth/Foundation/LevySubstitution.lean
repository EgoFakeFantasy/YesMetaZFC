import YesMetaZFC.SetTheory.KP.Sigma1
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Levy

/-! # 原生产 AST 的有限 Lévy 复杂度运输

直接分类原对象公式，不引入平行语言；替换不增加量词交替。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

theorem levy_bind_l {pol n d m} {φ : Formula 1 d} (h : φ.IsLevy pol n) (e : Fin d → Term m) :
    Formula.IsLevy pol n (φ.bind e) := by
  induction h generalizing m with
  | base h => exact .base (h.bind_l e)
  | lift h ih => exact .lift (ih e)
  | neg h ih => exact .neg (ih e)
  | conj h g ih jh => exact .conj (ih e) (jh e)
  | disj h g ih jh => exact .disj (ih e) (jh e)
  | existsE h ih => exact .existsE (ih (Term.liftSubstitution e))
  | forallE h ih => exact .forallE (ih (Term.liftSubstitution e))
  | existsMem t h ih =>
      have ht : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      simpa only [Formula.existsMem,Definitional.Formula.bind,ht] using!
        (Formula.IsLevy.existsMem (t.bind e) (ih (Term.liftSubstitution e)))
  | forallMem t h ih =>
      have ht : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      simpa only [Formula.forallMem,Definitional.Formula.bind,ht] using!
        (Formula.IsLevy.forallMem (t.bind e) (ih (Term.liftSubstitution e)))

theorem levy_rename_l {pol n d m} {φ : Formula 1 d} (h : φ.IsLevy pol n) (e : Fin d → Fin m) :
    Formula.IsLevy pol n (φ.rename e) := levy_bind_l h (fun i => .bound (e i))

theorem levy_weaken_l {pol n d} {φ : Formula 1 d} (h : φ.IsLevy pol n) : Formula.IsLevy pol n φ.weaken :=
  levy_rename_l h Fin.succ

theorem s1_binary_levy_l {p} (φ : S1_binary p) : φ.schema.body.IsSigma1 := by
  change Formula.IsLevy true 1 (.existsE φ.matrix.body)
  exact .existsE (.lift (.base φ.matrix.delta0))

theorem pred_levy_l {pol n p d} (φ : UnarySchema p) (h : φ.body.IsLevy pol n) (e : Fin p → Term d) (x : Term d) :
    (pred_m φ e x).IsLevy pol n := by
  unfold pred_m
  exact levy_bind_l h _

theorem binary_pred_levy_l {pol n p d} (φ : BinarySchema p) (h : φ.body.IsLevy pol n)
    (e : Fin p → Term d) (x y : Term d) : (binary_pred_m φ e x y).IsLevy pol n := by
  unfold binary_pred_m
  exact levy_bind_l h _


theorem levy_step_l {pol n d} {φ : Formula 1 d} (h : φ.IsLevy pol n) : φ.IsLevy pol (n+1) := by
  induction h with
  | base h => exact .lift (.base h)
  | lift h ih => exact .lift ih
  | neg h ih => exact .neg ih
  | conj h g ih jh => exact .conj ih jh
  | disj h g ih jh => exact .disj ih jh
  | existsE h ih => exact .existsE ih
  | forallE h ih => exact .forallE ih
  | existsMem t h ih => exact .existsMem t ih
  | forallMem t h ih => exact .forallMem t ih

theorem levy_mono_l {pol n m d} {φ : Formula 1 d} (h : φ.IsLevy pol n) (hnm : n ≤ m) : φ.IsLevy pol m := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact levy_step_l ih

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation
