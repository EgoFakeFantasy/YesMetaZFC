import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateDomain
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolemCompiler

/-! # 以单内部自然数索引的规范谓词源工厂 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure NicePredicateSource_d (hKP : M.Models KP) {d} (a : Fin d) (φ : Formula 1 (d+1))
    (C ω e k empty c : M.Domain) : Prop where
  normalized : PredicateParameterSkolemSource_d hKP a φ C ω e k empty
  pair : Oc_pair_d (kp_pair_l hKP) e k c
  index_natural : M.mem c ω
  index_mem : M.mem c C

theorem jh_nicePredicate_sourceCompile_l (hZF : M.Models ZF) {d} (a : Fin d) (reserve : Nat)
    (φ : Formula 1 (d+1)) (p : Cp_test (d+1)) (hp : PredicateDelta0 a.succ φ) (hc : φ.FreeClosed)
    (parsed : cp_parse_l φ = some p) {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ e k empty c, NicePredicateSource_d (ZF.modelsKP hZF) a φ C ω e k empty c := by
  obtain ⟨e,k,empty,base⟩ := jh_predicateParameterSkolem_sourceCompile_l hZF a reserve φ p hp hc parsed hα h hω hωC
  have hk := num_mem_l hZF.1 hω base.count
  obtain ⟨c,pair⟩ := oc_pair_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (hω.members_areOrdinals hZF e base.number_natural) (hω.members_areOrdinals hZF k hk)
  have hcω := oc_pair_natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω base.number_natural hk pair
  exact ⟨e,k,empty,c,base,pair,hcω,jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC c hcω⟩

theorem NicePredicateSource_d.sound_l (hZF : M.Models ZF) {d a φ C ω e k empty c}
    (result : NicePredicateSource_d (ZF.modelsKP hZF) (d := d) a φ C ω e k empty c)
    (hω : M.IsOmega ω) (σ : Env M d) {params input y : M.Domain}
    (corr : SourceParameter_d (fun j => if j = a then empty else σ.bound j) params)
    (outer : KPair_d M input c params)
    (selected : nicePredicateSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input y) :
    Formula.satisfies (σ.push y) φ := by
  obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total k params
  obtain ⟨packet,hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
  have inner : Rd_triple_d packet e k params := ⟨q,hq,hp⟩
  have choice := (nicePredicateSkolem_fixed_l hZF (predicateSkolem_env_l a ω σ) hω
    result.normalized.number_natural (num_mem_l hZF.1 hω result.normalized.count) outer result.pair inner).mp selected
  exact result.normalized.sound params packet y σ corr inner choice

theorem NicePredicateSource_d.local_total_l (hZF : M.Models ZF) {d a φ α C ω e k empty c}
    (result : NicePredicateSource_d (ZF.modelsKP hZF) (d := d) a φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (σ : Env M d) {X params input : M.Domain} (amenable : AmenableSet_d C (σ.bound a))
    (hinC : M.mem input C) (fn : Fn0_d k X params)
    (corr : SourceParameter_d (fun j => if j = a then empty else σ.bound j) params)
    (outer : KPair_d M input c params) (existsSource : ∃ y, M.mem y C ∧ Formula.satisfies (σ.push y) φ) :
    ∃ z, M.mem z C ∧ Within_d nicePredicateSkolem_s (predicateSkolem_env_l a ω σ) input z C ∧
      Formula.satisfies (σ.push z) φ ∧ ∀ t, nicePredicateSkolem_s.schema.denote (predicateSkolem_env_l a ω σ) input t → t = z := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  have hpC := (po_pair_bound_l trans hinC outer).2
  obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total k params
  obtain ⟨packet,hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
  have inner : Rd_triple_d packet e k params := ⟨q,hq,hp⟩
  have hpacketC := rud .triple e k params result.normalized.number_mem result.normalized.count_mem hpC packet (rd_triple_value_l hZF.1 inner)
  obtain ⟨z,hzC,chosen,source,unique⟩ := result.normalized.local_total X params packet σ amenable hpacketC fn corr inner existsSource
  let ρ := predicateSkolem_env_l a ω σ
  have graph := (indexPacket_fixed_l hZF ρ hω result.normalized.number_natural
    (num_mem_l hZF.1 hω result.normalized.count) outer result.pair).mpr inner
  have first := (jh_indexPacket_within_l hZF hα h ρ input packet hω hωC hinC).mpr
    ((indexPacket_sat_l hZF ρ input packet hω).mp graph)
  have hit := (within_comp_cover_l (ZF.modelsKP hZF) trans rud hωC indexPacket_s predicateParameterSkolem_s ρ input z).mpr
    ⟨packet,hpacketC,first,chosen⟩
  refine ⟨z,hzC,hit,source,?_⟩
  intro t selected
  exact unique t ((nicePredicateSkolem_fixed_l hZF ρ hω result.normalized.number_natural
    (num_mem_l hZF.1 hω result.normalized.count) outer result.pair inner).mp selected)

theorem NicePredicateSource_d.realizes_l (hZF : M.Models ZF) {d a φ α C ω e k empty c}
    (result : NicePredicateSource_d (ZF.modelsKP hZF) (d := d) a φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (σ : Env M d)
    (values : ∀ j, j ≠ a → M.mem (σ.bound j) C) :
    ∃ X params input, M.mem X C ∧ M.TransitiveSet X ∧ M.mem params C ∧ M.mem input C ∧
      Fn0_d k X params ∧ SourceParameter_d (fun j => if j = a then empty else σ.bound j) params ∧ KPair_d M input c params := by
  obtain ⟨X,params,_,hXC,hx,hpC,_,fn,corr,_⟩ := result.normalized.realizes σ values
  obtain ⟨input,outer⟩ := (kp_pair_l (ZF.modelsKP hZF)).total c params
  have hinC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .opair c params c
    result.index_mem hpC result.index_mem input (rd_opair_value_l hZF.1 outer)
  exact ⟨X,params,input,hXC,hx,hpC,hinC,fn,corr,outer⟩


theorem NicePredicateSource_d.input_standard_l (hZF : M.Models ZF) {d a φ C ω e k empty c X params input}
    (result : NicePredicateSource_d (ZF.modelsKP hZF) (d := d) a φ C ω e k empty c)
    (hω : M.IsOmega ω) (trans : M.TransitiveSet C) (hXC : M.mem X C)
    (fn : Fn0_d k X params) (outer : KPair_d M input c params) : NiceInput_d ω C input := by
  have sub : M.MemberSubset X C := fun x hx => trans X hXC x hx
  have fc := function_codomain_mono_l (kp_pair_l (ZF.modelsKP hZF)) sub (fn0_function_l (ZF.modelsKP hZF) fn)
  exact ⟨c,k,params,result.index_natural,num_mem_l hZF.1 hω result.normalized.count,
    fn0_of_function_l (ZF.modelsKP hZF) fc,outer⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
