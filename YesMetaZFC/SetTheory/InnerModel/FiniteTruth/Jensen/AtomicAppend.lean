import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AtomicAppend
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NorCompiler

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

theorem jh_atomicAppend_l (hZF : M.Models ZF) (equal : Bool) {a C T ω n F L i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : BoundedFormula_d T ω n L F)
    (hi : M.mem i n) (hj : M.mem j n) :
    ∃ U G K c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧
      M.mem G C ∧ M.mem K C ∧ M.mem c C ∧ AtomicAppend_d equal U ω n F L G K c i j := by
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
  have extended := old.snoc_l hKP hcU node hKω hKO hKL snoc
  have root := (((snoc_iff_entries_l (kp_pair_l hKP)
    (fn0_function_l hKP old.graph).1.1).mp snoc).2 L c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,hcC,old,extended,
    snoc_program_prefix_l hKP old snoc,hKL,root,hop,hiU,hjU,hLU,hi,hj⟩

private def jensenAtomicAppendBody (equal : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 8)) <| .imp (jh_value_m (.bound 8) (.bound 7)) <|
      .imp (Formula.isOmega (.bound 5)) <| .imp (.mem (.bound 5) (.bound 7)) <|
        .imp (.mem (.bound 6) (.bound 7)) <| .imp (.mem (.bound 3) (.bound 7)) <|
          .imp (boundedFormula_m (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 3)) <|
            .imp (.mem (.bound 1) (.bound 4)) <| .imp (.mem .newest (.bound 4)) <|
              .existsE <| .existsE <| .existsE <| .existsE <|
                .conj (.mem (.bound 3) (.bound 11)) <| .conj (Formula.isTransitive (.bound 3)) <|
                  .conj (Formula.subset (.bound 10) (.bound 3)) <| .conj (.mem (.bound 2) (.bound 11)) <|
                    .conj (.mem (.bound 1) (.bound 11)) <| .conj (.mem .newest (.bound 11))
                      (atomicAppend_m equal (.bound 3) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
                        (.bound 2) (.bound 1) .newest (.bound 5) (.bound 4))

def jensenAtomicAppend (equal : Bool) : Sentence := .ofFormula (jensenAtomicAppendBody equal)
  (by simp -implicitDefEqProofs [jensenAtomicAppendBody,Definitional.Formula.FreeClosed])

theorem jensenAtomicAppend_models (equal : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenAtomicAppend equal) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (jensenAtomicAppendBody equal)
  simp only [jensenAtomicAppendBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,boundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,Formula.satisfies_subset_iff,
    atomicAppend_sat_l (ZF.modelsKP hZF)]
  exact fun a C T ω n F L i j ha h hω hωC hTC hFC valid hi hj =>
    jh_atomicAppend_l hZF equal ha h hω hωC hTC hFC valid hi hj

theorem jensenAtomicAppend_derives (equal : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenAtomicAppend equal) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenAtomicAppend_models equal M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
