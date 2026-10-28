import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateExistsAppend

/-! # 指定谓词槽不入赋值图的真实 binder 更新

原环境栈顶扩张把指定槽 a 移为 a.succ。只维护其余普通变量条目。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem assignment_predicate_push_l (hKP : M.Models KP) {d} {v : Fin d → M.Domain}
    {ρ : Env M d} {f g fresh x : M.Domain} (a : Fin d)
    (corr : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) (unused : ∀ i, v i ≠ fresh)
    (update : Senv_update_d (kp_pair_l hKP) f fresh x g) :
    ∀ i : Fin (d+1), i ≠ a.succ → Rd_entry_d (Fin.cases fresh v i) ((ρ.push x).bound i) g :=
  Fin.cases (fun _ => (update.2 fresh x).mpr (Or.inl ⟨rfl,rfl⟩))
    (fun i hi => (update.2 (v i) (ρ.bound i)).mpr
      (Or.inr ⟨unused i,corr i (fun eq => hi (congrArg Fin.succ eq))⟩))

theorem sourcePredicateExists_compile_l (hZF : M.Models ZF) (positive : Bool) {d}
    (v : Fin d → M.Domain) (ρ : Env M d) (φ : Formula 1 (d+1)) (a q : Fin d) (different : q ≠ a)
    {T ω n X F L G K c fresh k f : M.Domain} (hω : M.IsOmega ω) (hx : M.TransitiveSet X)
    (program : PExistsAppend_d T ω n F L G K c fresh (v q) k) (unused : ∀ i, v i ≠ fresh)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f)
    (body : ∀ x g, M.mem x X → M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) g n X →
      (∀ i, i ≠ a.succ → Rd_entry_d (Fin.cases fresh v i) ((ρ.push x).bound i) g) →
      (PFiniteTruth_d true T ((ρ.push x).bound a.succ) ω n X F L k g ↔ Formula.satisfies (ρ.push x) φ)) :
    PFiniteTruth_d positive T (ρ.bound a) ω n X G K L f ↔
      Formula.satisfies ρ (if positive then Formula.existsMem (.bound q) φ else .neg (Formula.existsMem (.bound q) φ)) := by
  let hKP := ZF.modelsKP hZF
  have valueX : M.mem (ρ.bound q) X := hf.output_mem_of_pairMember (corr q different)
  have step : PExistsStep_d T (ρ.bound a) ω n X F L fresh (v q) k f ↔
      ∃ x, M.mem x (ρ.bound q) ∧ Formula.satisfies (ρ.push x) φ := by
    constructor
    · rintro ⟨b,_,read,x,hxX,hxb,g,fn,update,answer⟩
      have eq := hf.1.2 (v q) b (ρ.bound q) read (corr q different)
      subst b
      have hg := fn0_function_l hKP fn
      have actual := (bupdate_correct_l hKP hf hg program.fresh_bound hxX).mp update
      have newCorr := assignment_predicate_push_l hKP a corr unused actual
      exact ⟨x,hxb,(body x g hxX hg newCorr).mp answer⟩
    · rintro ⟨x,hxb,truth⟩
      have hxX := hx (ρ.bound q) valueX x hxb
      obtain ⟨g,actual,hg⟩ := senv_update_exists_l (kp_pair_l hKP) hZF hf program.fresh_bound hxX
      have newCorr := assignment_predicate_push_l hKP a corr unused actual
      exact ⟨ρ.bound q,valueX,corr q different,x,hxX,hxb,g,fn0_of_function_l hKP hg,
        (bupdate_correct_l hKP hf hg program.fresh_bound hxX).mpr actual,(body x g hxX hg newCorr).mpr truth⟩
  have truth := (pexistsAppend_eval_l hZF true hω program hf).trans
    (step.trans (Formula.satisfies_existsMem_iff ρ (.bound q) φ).symm)
  cases positive
  · exact (pfiniteTruth_complement_l hZF hω program.valid hf).trans
      ((not_congr truth).trans (Formula.satisfies_neg_iff ρ (Formula.existsMem (.bound q) φ)).symm)
  · exact truth

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
