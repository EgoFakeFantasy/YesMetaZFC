import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedPredicateWitness

/-! # 原索引函数增加只读参数槽后的准确语义

矩阵只重命名原有五个槽；新增普通前缀参数位于最后一槽。
原存在见证保持为同一个对象，不增加见证预算。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 槽位为 A、ω、普通参数前缀；当前函数仅保留前两个背景参数。 -/
def extendedIndexedWitness_env_l (ρ : Env M 3) : Env M 2 :=
  ρ.reindex Fin.castSucc

/-- 在原矩阵末尾增加一个未使用的参数槽，保留原输入、输出与见证槽。 -/
def extendedIndexedWitness_s : S1_binary 3 where
  matrix := {
    body := indexedPredicateWitness_s.matrix.body.rename Fin.castSucc
    freeClosed := by
      simpa only [Definitional.Formula.freeClosed_rename] using indexedPredicateWitness_s.matrix.freeClosed
    delta0 := indexedPredicateWitness_s.matrix.delta0.rename_l Fin.castSucc }

theorem extendedIndexedWitness_env_push_l (ρ : Env M 3) (x y w : M.Domain) :
    (((ρ.push x).push y).push w).reindex (Fin.castSucc : Fin 5 → Fin 6) =
      (((extendedIndexedWitness_env_l ρ).push x).push y).push w := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))),rfl⟩

theorem extendedIndexedWitness_matrix_l (ρ : Env M 3) (x y w : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push w) extendedIndexedWitness_s.matrix.body ↔
      Formula.satisfies ((((extendedIndexedWitness_env_l ρ).push x).push y).push w)
        indexedPredicateWitness_s.matrix.body := by
  change Formula.satisfies (((ρ.push x).push y).push w)
    (indexedPredicateWitness_s.matrix.body.rename Fin.castSucc) ↔ _
  rw [Formula.satisfies_rename,extendedIndexedWitness_env_push_l]

theorem extendedIndexedWitness_sat_l (ρ : Env M 3) (x y : M.Domain) :
    extendedIndexedWitness_s.schema.denote ρ x y ↔
      indexedPredicateWitness_s.schema.denote (extendedIndexedWitness_env_l ρ) x y := by
  simp only [S1_binary.sat_l,extendedIndexedWitness_matrix_l]

theorem extendedIndexedWitness_within_l (ρ : Env M 3) (x y C : M.Domain) :
    Within_d extendedIndexedWitness_s ρ x y C ↔
      Within_d indexedPredicateWitness_s (extendedIndexedWitness_env_l ρ) x y C := by
  unfold Within_d
  apply exists_congr
  intro w
  exact and_congr_right (fun _ => extendedIndexedWitness_matrix_l ρ x y w)

theorem extendedIndexedWitness_predicate_l :
    PredicateDelta0 (3 : Fin 6) extendedIndexedWitness_s.matrix.body := by
  change PredicateDelta0 (3 : Fin 6) (indexedPredicateWitness_s.matrix.body.rename Fin.castSucc)
  apply indexedPredicateWitness_predicate_l.bind_l (fun i : Fin 5 => .bound i.castSucc) rfl
  intro i ne eq
  apply ne
  apply Fin.ext
  have hi : i.castSucc = (3 : Fin 5).castSucc := Definitional.Term.bound.inj eq
  exact congrArg (fun j : Fin 6 => j.val) hi

theorem extendedIndexedWitness_sigma1_l : extendedIndexedWitness_s.schema.body.IsSigma1 :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.s1_binary_levy_l _

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
