import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateAtomicCompiler

/-! # 原同一 Jensen 层中的谓词原子代码生成与实际局部语义 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_predicateAppend_l (hZF : M.Models ZF) {α C T ω n F L i : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) (hi : M.mem i n) :
    ∃ U G K c z, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ M.mem z C ∧ PredicateAppend_d U ω n F L G K c i z := by
  let hKP := ZF.modelsKP hZF
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα hC
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) hC
  have hLC := trans ω hωC L valid.finite
  have hnC := trans ω hωC n valid.variables
  obtain ⟨z,hz,hzω⟩ := hω.1.1
  have hzC := trans ω hωC z hzω
  obtain ⟨U,c,hUC,hu,sub,hcU,hiU,hzU,_,code⟩ := bop_in_rud_l hKP rud trans
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) hα hC) hω hωC hTC
    (trans n hnC i hi) hzC hzC 4
  have hcC := trans U hUC c hcU
  have old := valid.container_mono_l hKP sub
  obtain ⟨K,hKL,hKω⟩ := hω.1.2 L valid.finite
  have hKC := trans ω hωC K hKω
  have hKO := KP.successor_isOrdinal hKP old.ordinal hKL
  have node : Pnode_d U ω n L c := Or.inr ⟨i,hiU,z,hzU,z,hzU,code,hi,hzω,hzω⟩
  obtain ⟨G,hGC,snoc⟩ := rd_snoc_exists_l hKP rud hFC hLC hcC
  have extended := old.snoc_l hKP hcU node hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,z,hUC,hu,sub,hGC,hKC,hcC,hzC,old,extended,
    snoc_predicate_prefix_l hKP old snoc,hKL,root,code,hiU,hzU,hi,hzω⟩

/-- 代码先于源环境生成；指定谓词槽没有寄存器界或条目要求。 -/
theorem jh_sourcePredicateAppend_compile_l (hZF : M.Models ZF) {α C T ω n F L : M.Domain} {d}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F)
    (v : Fin d → M.Domain) (a q : Fin d) (different : q ≠ a) (bound : M.mem (v q) n) :
    ∃ U G K c z, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧ M.mem G C ∧
      M.mem K C ∧ M.mem c C ∧ M.mem z C ∧ PredicateAppend_d U ω n F L G K c (v q) z ∧
        ∀ (positive : Bool) (X f : M.Domain) (ρ : Env M d),
          M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X →
          (∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) →
          (PFiniteTruth_d positive U (ρ.bound a) ω n X G K L f ↔
            Formula.satisfies ρ (predicateAnswer_m positive (.bound a) (.bound q))) := by
  obtain ⟨U,G,K,c,z,hUC,hu,sub,hGC,hKC,hcC,hzC,program⟩ :=
    jh_predicateAppend_l hZF hα hC hω hωC hTC hFC valid bound
  exact ⟨U,G,K,c,z,hUC,hu,sub,hGC,hKC,hcC,hzC,program,
    fun positive X f ρ fn corr => sourcePredicateAppend_compile_l hZF positive v ρ a q different hω program fn corr⟩

/-- amenable 外部谓词的实际局部源也解释为同一个原谓词原子。 -/
theorem jh_sourcePredicateAppend_local_l (hZF : M.Models ZF) (positive : Bool)
    {α C T ω n X F L G K c z f : M.Domain} {d} (v : Fin d → M.Domain) (ρ : Env M d) (a q : Fin d)
    (different : q ≠ a) (hα : M.IsOrdinal α) (hC : Jh_value_d α C)
    (amenable : AmenableSet_d C (ρ.bound a)) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hXC : M.mem X C) (hGC : M.mem G C) (hKC : M.mem K C)
    (program : PredicateAppend_d T ω n F L G K c (v q) z)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) :
    Within_d (pfiniteTruth_s positive) (pfiniteTruth_env_l T (ρ.bound a) ω n X G K) L f C ↔
      Formula.satisfies ρ (predicateAnswer_m positive (.bound a) (.bound q)) := by
  have hnC := jh_value_transitive_l (ZF.models_kpi_l hZF) hC ω hωC n program.valid.variables
  let η := pfiniteTruth_env_l T (ρ.bound a) ω n X G K
  have hp : ∀ i : Fin 6, M.mem (η.bound i.succ) C :=
    Fin.cases hKC (Fin.cases hGC (Fin.cases hXC (Fin.cases hnC (Fin.cases hωC (fun _ => hTC)))))
  exact (jh_pfiniteTruth_within_l hZF positive hα hC η amenable hp hω program.valid L f).trans
    (sourcePredicateAppend_compile_l hZF positive v ρ a q different hω program fn corr)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
