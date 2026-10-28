import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Environment

/-! # 任意固定原保护槽 Σ₁ 源的同索引见证表示 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure IndexedSigma1Source_d (hKP : M.Models KP) {p} (φ : S1_binary (p+1)) (C ω e k empty c : M.Domain) : Prop where
  body : NicePredicateSource_d hKP (sigma1SourceSlot_l p) (pairedMatrix φ).body C ω e k empty c

theorem jh_indexedSigma1_sourceCompile_l (hZF : M.Models ZF) {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body)
    {α C ω : M.Domain} (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C) :
    ∃ e k empty c, IndexedSigma1Source_d (ZF.modelsKP hZF) φ C ω e k empty c := by
  obtain ⟨e,k,empty,c,result⟩ := jh_nicePredicate_sourceCompile_l hZF (sigma1SourceSlot_l p) 0 (pairedMatrix φ).body
    (parsedSourceTest_l (pairedMatrix φ).body (pairedMatrix φ).delta0 (pairedMatrix φ).freeClosed)
    (sigma1Source_predicate_l φ useCert) (pairedMatrix φ).freeClosed
    (parsedSourceTest_some_l (pairedMatrix φ).body (pairedMatrix φ).delta0 (pairedMatrix φ).freeClosed)
    hα h hω hωC
  exact ⟨e,k,empty,c,⟨result⟩⟩

theorem IndexedSigma1Source_d.paired_sound_l (hZF : M.Models ZF) {p φ C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hω : M.IsOmega ω) (ρ : Env M (p+1)) {x params input z : M.Domain}
    (corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params)
    (outer : KPair_d M input c params)
    (selected : nicePredicateSkolem_s.schema.denote (indexedSource_env_l ρ ω) input z) :
    Formula.satisfies ((ρ.push x).push z) (pairedMatrix φ).body := by
  have selected' := selected
  rw [← indexedSource_env_push_l ρ ω x] at selected'
  exact result.body.sound_l hZF hω (ρ.push x) corr outer selected'

theorem IndexedSigma1Source_d.sound_l (hZF : M.Models ZF) {p φ C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hω : M.IsOmega ω) (ρ : Env M (p+1)) {x params input y : M.Domain}
    (corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params)
    (outer : KPair_d M input c params)
    (selected : indexedPredicateWitness_s.schema.denote (indexedSource_env_l ρ ω) input y) : φ.schema.denote ρ x y := by
  obtain ⟨z,nice,w,pair⟩ := (indexedPredicateWitness_sat_l hZF (indexedSource_env_l ρ ω) input y).mp selected
  have body := result.paired_sound_l hZF hω ρ corr outer nice
  obtain ⟨v,q,other,matrix⟩ := (pairedSource_body_sat_l hZF.1 φ ρ x z).mp body
  obtain ⟨eqY,eqW⟩ := kpair_injective_l M other pair
  rw [eqY,eqW] at matrix
  exact (φ.sat_l ρ x y).mpr ⟨w,matrix⟩

theorem IndexedSigma1Source_d.within_sound_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {x params input y : M.Domain}
    (corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params)
    (outer : KPair_d M input c params)
    (selected : Within_d indexedPredicateWitness_s (indexedSource_env_l ρ ω) input y C) : Within_d φ ρ x y C := by
  obtain ⟨z,hzC,nice,w,pair⟩ := (jh_indexedPredicateWitness_within_l hZF hα h (indexedSource_env_l ρ ω) hωC).mp selected
  have body := result.paired_sound_l hZF hω ρ corr outer (within_toSchema_l _ _ nice)
  obtain ⟨v,q,other,matrix⟩ := (pairedSource_body_sat_l hZF.1 φ ρ x z).mp body
  obtain ⟨rfl,rfl⟩ := kpair_injective_l M other pair
  exact source_within_of_pair_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) φ ρ hzC pair matrix

theorem IndexedSigma1Source_d.local_total_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {x X params input : M.Domain} (amenable : AmenableSet_d C (ρ.bound 0))
    (hinC : M.mem input C) (fn : Fn0_d k X params)
    (corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params)
    (outer : KPair_d M input c params) (existsSource : ∃ y, M.mem y C ∧ Within_d φ ρ x y C) :
    ∃ y, M.mem y C ∧ Within_d indexedPredicateWitness_s (indexedSource_env_l ρ ω) input y C ∧
      Within_d φ ρ x y C ∧ ∀ t, indexedPredicateWitness_s.schema.denote (indexedSource_env_l ρ ω) input t → t = y := by
  have pairedExists : ∃ z, M.mem z C ∧ Formula.satisfies ((ρ.push x).push z) (pairedMatrix φ).body := by
    obtain ⟨y,hyC,source⟩ := existsSource
    exact jh_pairedSource_exists_l hZF hα h φ ρ x hyC source
  obtain ⟨z,hzC,nice,body,_⟩ := result.body.local_total_l hZF hα h hω hωC (ρ.push x) amenable hinC fn corr outer pairedExists
  rw [indexedSource_env_push_l ρ ω x] at nice
  obtain ⟨y,w,pair,matrix⟩ := (pairedSource_body_sat_l hZF.1 φ ρ x z).mp body
  have coords := po_pair_bound_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hzC pair
  have selected := (jh_indexedPredicateWitness_within_l hZF hα h (indexedSource_env_l ρ ω) hωC).mpr ⟨z,hzC,nice,w,pair⟩
  exact ⟨y,coords.1,selected,⟨w,coords.2,matrix⟩,fun t ht => indexedPredicateWitness_unique_l hZF
    (indexedSource_env_l ρ ω) hω ht (within_toSchema_l _ _ selected)⟩

theorem IndexedSigma1Source_d.realizes_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (ρ : Env M (p+1)) {x : M.Domain}
    (hxC : M.mem x C) (ordinary : ∀ i : Fin p, M.mem (ρ.bound i.succ) C) :
    ∃ X params input, M.mem X C ∧ M.TransitiveSet X ∧ M.mem params C ∧ M.mem input C ∧ Fn0_d k X params ∧
      SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params ∧
      KPair_d M input c params ∧ NiceInput_d ω C input := by
  obtain ⟨X,params,input,hXC,hx,hpC,hinC,fn,corr,outer⟩ := result.body.realizes_l hZF hα h (ρ.push x)
    (indexedSource_ordinary_l ρ hxC ordinary)
  exact ⟨X,params,input,hXC,hx,hpC,hinC,fn,corr,outer,
    result.body.input_standard_l hZF hω (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hXC fn outer⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
