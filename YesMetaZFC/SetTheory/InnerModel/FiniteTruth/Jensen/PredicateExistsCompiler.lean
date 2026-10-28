import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateExistsAppend
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNorCompiler

/-! # 同一原 J 层内实际生成有界存在指令 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pexistsAppend_l (hZF : M.Models ZF) {a C T ω n F L i j k : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F)
    (hi : M.mem i n) (hj : M.mem j n) (hk : M.mem k L) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ PExistsAppend_d U ω n F L G K c i j k := by
  let hKP := ZF.modelsKP hZF
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hnC := trans ω hωC n valid.variables
  have hLC := trans ω hωC L valid.finite
  obtain ⟨U,c,hUC,hu,sub,hcU,hiU,hjU,hkU,hop⟩ := bop_in_rud_l hKP hC trans
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) ha h) hω hωC hTC
    (trans n hnC i hi) (trans n hnC j hj) (trans L hLC k hk) 3
  have hcC := trans U hUC c hcU
  have old := valid.container_mono_l hKP sub
  obtain ⟨K,hKL,hKω⟩ := hω.1.2 L valid.finite
  have hKC := trans ω hωC K hKω
  have hKO := KP.successor_isOrdinal hKP old.ordinal hKL
  have node : Bnode_d U ω n L c :=
    Or.inr (Or.inr (Or.inr ⟨i,hiU,j,hjU,k,hkU,hop,hi,hj,hk⟩))
  obtain ⟨G,hGC,snoc⟩ := rd_snoc_exists_l hKP hC hFC hLC hcC
  have extended := old.snoc_l hKP hcU (Or.inl node) hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,old,extended,
    snoc_predicate_prefix_l hKP old snoc,hKL,root,hop,hiU,hjU,hkU,hi,hj,hk⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
