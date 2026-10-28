import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Compiler

/-! # 任意给定通用表对原固定源的完整见证查询

代码先于源值选择。表不是随源公式重建，而是同一原索引函数的任意真实通用表。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem IndexedSigma1Source_d.universal_table_query_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {T x X params input : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0))
    (table : UniversalTruthTable_d (indexedSource_env_l ρ ω) C T)
    (hparamsC : M.mem params C) (hinC : M.mem input C) (fn : Fn0_d k X params)
    (corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params)
    (outer : KPair_d M input c params) :
    M.mem input T ↔ RestrictedTruthDomain_d φ ρ C x := by
  have entry := RestrictedTruthTable_d.pair_l table result.body.index_natural hparamsC outer
  constructor
  · intro hit
    obtain ⟨y,hyC,selected⟩ := entry.mp hit
    exact ⟨y,hyC,result.within_sound_l hZF hα hC hω hωC ρ corr outer selected⟩
  · intro source
    obtain ⟨y,hyC,selected,_,_⟩ := result.local_total_l hZF hα hC hω hωC ρ amenable hinC fn corr outer source
    exact entry.mpr ⟨y,hyC,selected⟩

theorem IndexedSigma1Source_d.universal_table_realizes_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {T x : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0))
    (ordinary : ∀ i : Fin p, M.mem (ρ.bound i.succ) C)
    (table : UniversalTruthTable_d (indexedSource_env_l ρ ω) C T) (hxC : M.mem x C) :
    ∃ X params input, M.mem X C ∧ M.TransitiveSet X ∧ M.mem params C ∧ M.mem input C ∧ Fn0_d k X params ∧
      BoundedSourceParameter_d k (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params ∧
      KPair_d M input c params ∧ (M.mem input T ↔ RestrictedTruthDomain_d φ ρ C x) := by
  obtain ⟨X,params,input,hXC,trans,hparamsC,hinC,fn,corr,outer,_⟩ := result.realizes_l hZF hα hC hω ρ hxC ordinary
  exact ⟨X,params,input,hXC,trans,hparamsC,hinC,fn,
    boundedSourceParameter_of_l hZF.1 result.body.normalized.count corr,outer,
    result.universal_table_query_l hZF hα hC hω hωC ρ amenable table hparamsC hinC fn corr outer⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
