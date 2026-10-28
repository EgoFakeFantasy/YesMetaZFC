import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentUpdate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.RegisterFrame

/-! # 每个有限源环境的实际赋值图

从实际常值函数出发，有限次更新互异寄存器。变量域可以是任意模型内集合，
不要求它外部有限或标准；这里只对固定源模板的外部变量向量归纳。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 任意界内互异寄存器，都能实际实现所有域内源值。 -/
theorem assignment_realize_l (hZF : M.Models ZF) {d} (v σ : Fin d → M.Domain)
    {n X default : M.Domain} (bound : ∀ i, M.mem (v i) n) (injective : Function.Injective v)
    (values : ∀ i, M.mem (σ i) X) (inhabited : M.mem default X) :
    ∃ f, Fn0_d n X f ∧ ∀ i, Rd_entry_d (v i) (σ i) f := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  induction d with
  | zero =>
    obtain ⟨f,hf,_⟩ := ZF.exists_constantFunction hZF I (source := n) inhabited
    exact ⟨f,fn0_of_function_l (ZF.modelsKP hZF) hf,fun i => Fin.elim0 i⟩
  | succ d ih =>
    have tailInjective : Function.Injective (fun i : Fin d => v i.succ) := by
      intro i j eq
      exact Fin.succ_inj.mp (injective eq)
    obtain ⟨f,hf,corr⟩ := ih (fun i => v i.succ) (fun i => σ i.succ)
      (fun i => bound i.succ) tailInjective (fun i => values i.succ)
    obtain ⟨g,update,hg⟩ := senv_update_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) hf) (bound 0) (values 0)
    refine ⟨g,fn0_of_function_l (ZF.modelsKP hZF) hg,fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (update.2 (v 0) (σ 0)).mpr (Or.inl ⟨rfl,rfl⟩)
    · have different : v i.succ ≠ v 0 := by
        intro eq
        have he := congrArg Fin.val (injective eq)
        change i.val+1 = 0 at he
        omega
      exact (update.2 (v i.succ) (σ i.succ)).mpr (Or.inr ⟨different,corr i⟩)

/-- 更新一个真正新鲜的槽，实现原 Project 环境的栈顶扩张。 -/
theorem assignment_push_correspond_l (hKP : M.Models KP) {d} {v : Fin d → M.Domain}
    {ρ : Env M d} {f g fresh x : M.Domain}
    (corr : ∀ i, Rd_entry_d (v i) (ρ.bound i) f) (unused : ∀ i, v i ≠ fresh)
    (update : Senv_update_d (kp_pair_l hKP) f fresh x g) :
    ∀ i : Fin (d+1), Rd_entry_d (Fin.cases fresh v i) ((ρ.push x).bound i) g :=
  Fin.cases ((update.2 fresh x).mpr (Or.inl ⟨rfl,rfl⟩))
    (fun i => (update.2 (v i) (ρ.bound i)).mpr (Or.inr ⟨unused i,corr i⟩))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
