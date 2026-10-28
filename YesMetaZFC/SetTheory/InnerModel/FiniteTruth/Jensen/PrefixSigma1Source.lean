import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixIndexedWitness
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Compiler

/-! # 固定原 Σ₁ 源与实际普通参数前缀的准确接线 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def prefixSource_env_l {p} (ρ : Env M (p+1)) (ω P : M.Domain) : Env M 3 :=
  ⟨Fin.cases (ρ.bound 0) (Fin.cases ω (fun _ => P)),ρ.free⟩

theorem prefixSource_env_projection_l {p} (ρ : Env M (p+1)) (ω P : M.Domain) :
    extendedIndexedWitness_env_l (prefixSource_env_l ρ ω P) = indexedSource_env_l ρ ω := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))),rfl⟩

theorem prefixSource_values_l {p} (ρ : Env M (p+1)) (x z : M.Domain) :
    (fun j => if j = sigma1SourceSlot_l p then z else (ρ.push x).bound j) =
      Fin.cases x (Fin.cases z (fun i : Fin p => ρ.bound i.succ)) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · have ne : (0 : Fin (p+2)) ≠ sigma1SourceSlot_l p := by
      intro eq
      have vals := congrArg Fin.val eq
      change (0 : Nat) = 1 at vals
      omega
    exact if_neg ne
  · exact if_pos rfl
  · have ne : i.succ.succ ≠ sigma1SourceSlot_l p := by
      intro eq
      have vals := congrArg Fin.val eq
      change i.val+1+1 = 1 at vals
      omega
    exact if_neg ne

theorem IndexedSigma1Source_d.prefix_correspondence_l (hZF : M.Models ZF) {p φ C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hω : M.IsOmega ω) (ρ : Env M (p+1)) {P x l X l' s k' Y z f g params : M.Domain}
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (cert : PrefixParameters_d ω P x l' s k' Y z f g params) :
    k' = k ∧ z = empty ∧
      SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params := by
  have eql := (fn0_function_l (ZF.modelsKP hZF) cert.first.parameters).2.1.eq hZF.1
    (fn0_function_l (ZF.modelsKP hZF) pref).2.1
  subst l'
  have eqk := num_unique_l hZF.1 (cert.count_l hl) result.body.normalized.count
  have eqz := num_unique_l hZF.1 cert.first.zero result.body.normalized.zero
  have expanded := cert.source_l hZF hω hl corr
  rw [eqz] at expanded
  rw [← prefixSource_values_l ρ x empty] at expanded
  exact ⟨eqk,eqz,expanded⟩

theorem IndexedSigma1Source_d.prefix_input_l (hZF : M.Models ZF) {p φ C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hω : M.IsOmega ω) (ρ : Env M (p+1)) {P x l X input packet : M.Domain}
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (outer : KPair_d M input c x) (normal : PrefixInput_d ω P input packet) :
    ∃ Y params, Fn0_d k Y params ∧
      SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (ρ.push x).bound j) params ∧
      KPair_d M packet c params := by
  obtain ⟨l',s,k',Y,z,f,g,params,c',x',_,raw,inner,cert⟩ := normal
  obtain ⟨eqc,eqx⟩ := kpair_injective_l M raw outer
  subst c'; subst x'
  obtain ⟨eqk,_,expanded⟩ := result.prefix_correspondence_l hZF hω ρ hl pref corr cert
  have fn := cert.full
  rw [eqk] at fn
  exact ⟨Y,params,fn,expanded,inner⟩

theorem IndexedSigma1Source_d.prefix_sound_l (hZF : M.Models ZF) {p φ C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hω : M.IsOmega ω) (ρ : Env M (p+1)) {P x l X input y : M.Domain}
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (outer : KPair_d M input c x)
    (selected : prefixIndexedWitness_s.schema.denote (prefixSource_env_l ρ ω P) input y) :
    φ.schema.denote ρ x y := by
  obtain ⟨packet,normal,chosen⟩ := (prefixIndexedWitness_sat_l hZF (prefixSource_env_l ρ ω P) input y).mp selected
  obtain ⟨Y,params,_,expanded,inner⟩ := result.prefix_input_l hZF hω ρ hl pref corr outer normal
  rw [prefixSource_env_projection_l] at chosen
  exact result.sound_l hZF hω ρ expanded inner chosen

theorem IndexedSigma1Source_d.prefix_within_sound_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {P x l X input y : M.Domain} (hPC : M.mem P C) (hinC : M.mem input C)
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (outer : KPair_d M input c x)
    (selected : Within_d prefixIndexedWitness_s (prefixSource_env_l ρ ω P) input y C) : Within_d φ ρ x y C := by
  obtain ⟨packet,_,normal,chosen⟩ := (jh_prefixIndexedWitness_within_l hZF hα h
    (prefixSource_env_l ρ ω P) hω hωC hPC hinC).mp selected
  obtain ⟨Y,params,_,expanded,inner⟩ := result.prefix_input_l hZF hω ρ hl pref corr outer normal
  rw [prefixSource_env_projection_l] at chosen
  exact result.within_sound_l hZF hα h hω hωC ρ expanded inner chosen

theorem IndexedSigma1Source_d.prefix_local_total_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {P x l X input : M.Domain} (hPC : M.mem P C) (hinC : M.mem input C)
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (outer : KPair_d M input c x) (amenable : AmenableSet_d C (ρ.bound 0))
    (source : ∃ y, M.mem y C ∧ Within_d φ ρ x y C) :
    ∃ y, M.mem y C ∧ Within_d prefixIndexedWitness_s (prefixSource_env_l ρ ω P) input y C ∧
      Within_d φ ρ x y C ∧
      ∀ t, prefixIndexedWitness_s.schema.denote (prefixSource_env_l ρ ω P) input t → t = y := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have coords := po_pair_bound_l trans hinC outer
  obtain ⟨Y,s,k',f,g,params,_,_,_,_,hparamsC,cert⟩ :=
    jh_prefixParameters_l hZF hα h hω hωC hPC coords.2 (num_mem_l hZF.1 hω hl)
      result.body.normalized.zero pref
  obtain ⟨eqk,_,expanded⟩ := result.prefix_correspondence_l hZF hω ρ hl pref corr cert
  have fn := cert.full
  rw [eqk] at fn
  obtain ⟨packet,inner⟩ := (kp_pair_l (ZF.modelsKP hZF)).total c params
  have hpacketC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .opair c params c
    coords.1 hparamsC coords.1 packet (rd_opair_value_l hZF.1 inner)
  obtain ⟨y,hyC,indexed,original,_⟩ := result.local_total_l hZF hα h hω hωC ρ amenable
    hpacketC fn expanded inner source
  have normal : PrefixInput_d ω P input packet :=
    ⟨l,s,k',Y,empty,f,g,params,c,x,result.body.index_natural,outer,inner,cert⟩
  have selected : Within_d prefixIndexedWitness_s (prefixSource_env_l ρ ω P) input y C := by
    apply (jh_prefixIndexedWitness_within_l hZF hα h (prefixSource_env_l ρ ω P) hω hωC hPC hinC).mpr
    refine ⟨packet,hpacketC,normal,?_⟩
    rw [prefixSource_env_projection_l]
    exact indexed
  exact ⟨y,hyC,selected,original,fun t ht => prefixIndexedWitness_unique_l hZF
    (prefixSource_env_l ρ ω P) hω ht (within_toSchema_l _ _ selected)⟩

theorem IndexedSigma1Source_d.prefix_local_iff_l (hZF : M.Models ZF) {p φ α C ω e k empty c}
    (result : IndexedSigma1Source_d (ZF.modelsKP hZF) (p := p) φ C ω e k empty c)
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) {P x l X input : M.Domain} (hPC : M.mem P C) (hinC : M.mem input C)
    (hl : Num_d p l) (pref : Fn0_d l X P)
    (corr : SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P)
    (outer : KPair_d M input c x) (amenable : AmenableSet_d C (ρ.bound 0)) :
    (∃ y, M.mem y C ∧ Within_d prefixIndexedWitness_s (prefixSource_env_l ρ ω P) input y C) ↔
      ∃ y, M.mem y C ∧ Within_d φ ρ x y C := by
  constructor
  · rintro ⟨y,hyC,selected⟩
    exact ⟨y,hyC,result.prefix_within_sound_l hZF hα h hω hωC ρ hPC hinC hl pref corr outer selected⟩
  · intro source
    obtain ⟨y,hyC,selected,_,_⟩ := result.prefix_local_total_l hZF hα h hω hωC ρ hPC hinC hl pref corr outer amenable source
    exact ⟨y,hyC,selected⟩

theorem jh_prefixSource_realize_l (hZF : M.Models ZF) {p α C ω}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (ρ : Env M (p+1)) (ordinary : ∀ i : Fin p, M.mem (ρ.bound i.succ) C) :
    ∃ l X P, Num_d p l ∧ M.mem X C ∧ M.TransitiveSet X ∧ M.mem P C ∧ Fn0_d l X P ∧
      SourceParameter_d (fun i : Fin p => ρ.bound i.succ) P := by
  obtain ⟨l,hl⟩ := num_exists_l (ZF.modelsKP hZF) p
  obtain ⟨X,P,hXC,hx,hPC,pref,corr⟩ := jh_sourceParameter_realize_l hZF hα h hω hωC hl
    (fun i : Fin p => ρ.bound i.succ) ordinary
  exact ⟨l,X,P,hl,hXC,hx,hPC,pref,corr⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
