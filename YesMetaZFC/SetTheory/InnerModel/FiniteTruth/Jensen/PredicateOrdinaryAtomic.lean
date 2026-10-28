import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramExtension

/-! # 同一原 Jensen 层内的原子叶追加

保留任意已有内部程序，在旧长度处生成真实原子指令并追加实际函数图。
新容器、代码、程序和后继长度全部仍在同一层内。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_patomicAppend_l (hZF : M.Models ZF) (equal : Bool) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F)
    (hi : M.mem i n) (hj : M.mem j n) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ PAtomicAppend_d equal U ω n F L G K c i j := by
  let hKP := ZF.modelsKP hZF
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  have hc := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hLC := hc ω hωC L valid.finite
  have hnC := hc ω hωC n valid.variables
  obtain ⟨U,c,hUC,hu,sub,hcU,hiU,hjU,hLU,hop⟩ := bop_in_rud_l hKP hC hc
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) ha h) hω hωC hTC
    (hc n hnC i hi) (hc n hnC j hj) hLC (atomicTag equal)
  have hcC := hc U hUC c hcU
  have old := valid.container_mono_l hKP sub
  obtain ⟨K,hKL,hKω⟩ := hω.1.2 L valid.finite
  have hKC := hc ω hωC K hKω
  have hKO := KP.successor_isOrdinal hKP old.ordinal hKL
  have node : Bnode_d U ω n L c := by
    cases equal
    · exact Or.inl ⟨i,hiU,j,hjU,L,hLU,hop,hi,hj,valid.finite⟩
    · exact Or.inr (Or.inl ⟨i,hiU,j,hjU,L,hLU,hop,hi,hj,valid.finite⟩)
  obtain ⟨G,hGC,snoc⟩ := rd_snoc_exists_l hKP hC hFC hLC hcC
  have extended := old.snoc_l hKP hcU (Or.inl node) hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,old,extended,
    snoc_predicate_prefix_l hKP old snoc,hKL,root,hop,hiU,hjU,hLU,hi,hj⟩


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
