import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NorCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.AtomicCompiler

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

theorem jh_norAppend_l (hZF : M.Models ZF) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hi : M.mem i L) (hj : M.mem j L) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ NorAppend_d U ω n F L G K c i j := by
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
  have extended := old.snoc_l hKP hcU node hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,old,extended,
    snoc_program_prefix_l hKP old snoc,hKL,root,hop,hiU,hjU,hLU,hi,hj⟩

/-- 一次生成的真实追加，对所有合法赋值都保留两个子查询的语义。 -/
theorem jh_norAppend_compile_l (hZF : M.Models ZF) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hi : M.mem i L) (hj : M.mem j L) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ NorAppend_d U ω n F L G K c i j ∧
        ∀ (positive : Bool) (X f : M.Domain),
          M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X →
          (FiniteTruth_d positive U ω n X G K L f ↔
            NorAnswer_d positive (FiniteTruth_d true T ω n X F L i f) (FiniteTruth_d true T ω n X F L j f)) := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,program⟩ := jh_norAppend_l hZF ha h hω hωC hTC hFC valid hi hj
  refine ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,program,fun positive X f hf => ?_⟩
  exact (norAppend_eval_l hZF positive hω program hf).trans
    (norAnswer_congr_l positive (finiteTruth_container_l (ZF.modelsKP hZF) true valid sub).symm
      (finiteTruth_container_l (ZF.modelsKP hZF) true valid sub).symm)

private def jensenNorAppendBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 8)) <| .imp (jh_value_m (.bound 8) (.bound 7)) <|
      .imp (Formula.isOmega (.bound 5)) <| .imp (.mem (.bound 5) (.bound 7)) <|
        .imp (.mem (.bound 6) (.bound 7)) <| .imp (.mem (.bound 3) (.bound 7)) <|
          .imp (boundedFormula_m (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3)) <|
            .imp (.mem (.bound 1) (.bound 2)) <| .imp (.mem .newest (.bound 2)) <|
              .existsE <| .existsE <| .existsE <| .existsE <|
                .conj (.mem (.bound 3) (.bound 11)) <| .conj (Formula.isTransitive (.bound 3)) <|
                  .conj (Formula.subset (.bound 10) (.bound 3)) <| .conj (.mem (.bound 2) (.bound 11)) <|
                    .conj (.mem (.bound 1) (.bound 11)) <| .conj (.mem .newest (.bound 11))
                      (norAppend_m (.bound 3) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
                        (.bound 2) (.bound 1) .newest (.bound 5) (.bound 4))

def jensenNorAppend : Sentence := .ofFormula jensenNorAppendBody
  (by simp -implicitDefEqProofs [jensenNorAppendBody,Definitional.Formula.FreeClosed])

theorem jensenNorAppend_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenNorAppend := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenNorAppendBody
  simp only [jensenNorAppendBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,boundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,Formula.satisfies_subset_iff,
    norAppend_sat_l (ZF.modelsKP hZF)]
  exact fun a C T ω n F L i j ha h hω hωC hTC hFC valid hi hj =>
    jh_norAppend_l hZF ha h hω hωC hTC hFC valid hi hj

theorem jensenNorAppend_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenNorAppend :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality jensenNorAppend_models

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
