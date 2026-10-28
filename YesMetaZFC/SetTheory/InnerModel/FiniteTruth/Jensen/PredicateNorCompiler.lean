import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateOrdinaryAtomic

/-! # 原 Jensen 层中的真实或非追加

已有程序的两个子行在内部长度内时，用同层 rud 构造真实指令、扩张容器和
实际追加图。小层不预设 KP 或 Collection；此处不是完整源公式编译器。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_pnorAppend_l (hZF : M.Models ZF) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F)
    (hi : M.mem i L) (hj : M.mem j L) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ PNorAppend_d U ω n F L G K c i j := by
  let hKP := ZF.modelsKP hZF
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  have hc := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have hLC := hc ω hωC L valid.finite
  obtain ⟨U,c,hUC,hu,sub,hcU,hiU,hjU,hLU,hop⟩ := bop_in_rud_l hKP hC hc
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) ha h) hω hωC hTC
    (hc L hLC i hi) (hc L hLC j hj) hLC 2
  have hcC := hc U hUC c hcU
  have old := valid.container_mono_l hKP sub
  obtain ⟨K,hKL,hKω⟩ := hω.1.2 L valid.finite
  have hKC := hc ω hωC K hKω
  have hKO := KP.successor_isOrdinal hKP old.ordinal hKL
  have node : Bnode_d U ω n L c :=
    Or.inr (Or.inr (Or.inl ⟨i,hiU,j,hjU,L,hLU,hop,hi,hj,valid.finite⟩))
  obtain ⟨G,hGC,snoc⟩ := rd_snoc_exists_l hKP hC hFC hLC hcC
  have extended := old.snoc_l hKP hcU (Or.inl node) hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,old,extended,
    snoc_predicate_prefix_l hKP old snoc,hKL,root,hop,hiU,hjU,hLU,hi,hj⟩

/-- 一次生成的真实追加，对所有合法赋值都保留两个子查询的语义。 -/
theorem jh_pnorAppend_compile_l (hZF : M.Models ZF) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F)
    (hi : M.mem i L) (hj : M.mem j L) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ PNorAppend_d U ω n F L G K c i j ∧
        ∀ (A : M.Domain) (positive : Bool) (X f : M.Domain),
          M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X →
          (PFiniteTruth_d positive U A ω n X G K L f ↔
            NorAnswer_d positive (PFiniteTruth_d true T A ω n X F L i f) (PFiniteTruth_d true T A ω n X F L j f)) := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,program⟩ := jh_pnorAppend_l hZF ha h hω hωC hTC hFC valid hi hj
  refine ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,program,fun A positive X f hf => ?_⟩
  exact (pnorAppend_eval_l hZF positive hω program hf).trans
    (norAnswer_congr_l positive (pfiniteTruth_container_l (ZF.modelsKP hZF) true valid sub).symm
      (pfiniteTruth_container_l (ZF.modelsKP hZF) true valid sub).symm)


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
