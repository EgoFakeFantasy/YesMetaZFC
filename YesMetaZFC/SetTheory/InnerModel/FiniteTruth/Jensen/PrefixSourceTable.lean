import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixSigma1Source
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.RestrictedTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixSourceTableQuery

/-! # 固定原源的实际参数前缀与真实受限编码真值集合 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 同一真实表先于全部查询输入存在；成员等价保留原源的完整局部见证。 -/
theorem IndexedSigma1Source_d.prefix_table_realize_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    {U : M.Domain} (sub : M.MemberSubset U C) (ρ : Env M (p+1))
    (amenable : AmenableSet_d C (ρ.bound 0)) (ordinary : ∀ i : Fin p, M.mem (ρ.bound i.succ) C) :
    ∃ l X P T, Num_d p l ∧ M.mem X C ∧ M.TransitiveSet X ∧ M.mem P C ∧ Fn0_d l X P ∧
      BoundedSourceParameter_d l (fun i : Fin p => ρ.bound i.succ) P ∧
      RestrictedTruthTable_d prefixIndexedWitness_s (prefixSource_env_l ρ ω P) ω U C T ∧
      ∀ x, M.mem x U → ∀ input, KPair_d M input c x →
        (M.mem input T ↔ RestrictedTruthDomain_d φ ρ C x) := by
  obtain ⟨l,X,P,hl,hXC,hx,hPC,pref,corr⟩ := jh_prefixSource_realize_l hZF hα h hω hωC ρ ordinary
  obtain ⟨_,T,_,table,_⟩ := restrictedTruthTable_exists_l hZF prefixIndexedWitness_s
    (prefixSource_env_l ρ ω P) ω U C
  refine ⟨l,X,P,T,hl,hXC,hx,hPC,pref,boundedSourceParameter_of_l hZF.1 hl corr,table,?_⟩
  intro x hxU input pair
  have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .opair c x c
    result.body.index_mem (sub x hxU) result.body.index_mem input (rd_opair_value_l hZF.1 pair)
  exact (table.pair_l result.body.index_natural hxU pair).trans
    (result.prefix_local_iff_l hZF hα h hω hωC ρ hPC hinC hl pref corr pair amenable)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
