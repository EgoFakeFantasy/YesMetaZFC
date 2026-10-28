import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateSkolem
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateUniformization

/-! # 实际局部图的标准自然数乘内部有限列定义域 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def NiceInput_d (ω C input : M.Domain) : Prop :=
  ∃ c k params, M.mem c ω ∧ M.mem k ω ∧ Fn0_d k C params ∧ KPair_d M input c params

def niceInput_m {d} (ω C input : Term d) : Formula 1 d :=
  Formula.existsMem ω <| Formula.existsMem ω.weaken <| .existsE <|
    .conj (fn0_m (.bound 1) C.weaken.weaken.weaken .newest)
      (kpair0_m input.weaken.weaken.weaken (.bound 2) .newest)
derive_free_closed niceInput_m

theorem niceInput_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω C input : Term d) :
    Formula.satisfies ρ (niceInput_m ω C input) ↔ NiceInput_d (ω.eval ρ) (C.eval ρ) (input.eval ρ) := by
  simp only [niceInput_m,NiceInput_d,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,fn0_sat_l hE,kpair0_sat_l hE,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨c,hc,k,hk,params,fn,outer⟩
    exact ⟨c,k,params,hc,hk,fn,outer⟩
  · rintro ⟨c,k,params,hc,hk,fn,outer⟩
    exact ⟨c,hc,k,hk,params,fn,outer⟩

theorem jh_nicePredicateSkolem_domain_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (hit : Within_d nicePredicateSkolem_s ρ input y C) :
    NiceInput_d (ρ.bound 1) C input ∧ M.mem input C ∧ M.mem y C := by
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  obtain ⟨packet,_,first,second⟩ := (within_comp_cover_l (ZF.modelsKP hZF) trans rud hωC
    indexPacket_s predicateParameterSkolem_s ρ input y).mp hit
  obtain ⟨normal,_,normalized,chosen⟩ := (within_comp_cover_l (ZF.modelsKP hZF) trans rud hωC
    pnormalizedInput_s predicateNumericSkolem_s ρ packet y).mp second
  have hyC := (jh_canonicalPick_within_sound_l (ZF.models_kpi_l hZF) hα h pwitnessFiber_s ρ chosen).1
  obtain ⟨w,hwC,body⟩ := first
  obtain ⟨e,hew,k,hkw,c,hcw,params,hpw,P,_,cert⟩ := (indexPacket_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mp body
  obtain ⟨v,hvC,bodyN⟩ := normalized
  obtain ⟨T,_,n,_,L,_,F,_,r,_,X,hXv,e',_,k',_,params',_,z,_,f,_,P',_,certN⟩ :=
    (pnormalizedInput_matrix_sat_l (ZF.modelsKP hZF) ρ packet normal v).mp bodyN
  obtain ⟨ee,kk,aa⟩ := pc_triple_inj_l certN.1 cert.2.2.2.1
  subst e'; subst k'; subst params'
  have pair := pairWitness_sound_l hZF cert.2.2.2.2
  have hcω := oc_pair_natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω cert.1 cert.2.1 pair
  have hXC := trans v hvC X hXv
  have sub : M.MemberSubset X C := fun x hx => trans X hXC x hx
  have fn := function_codomain_mono_l (kp_pair_l (ZF.modelsKP hZF)) sub
    (fn0_function_l (ZF.modelsKP hZF) certN.2.2.1.parameters)
  have hcC := trans w hwC c hcw
  have hpC := trans w hwC params hpw
  have hinC := rud .opair c params c hcC hpC hcC input (rd_opair_value_l hZF.1 cert.2.2.1)
  exact ⟨⟨c,k,params,hcω,cert.2.1,fn0_of_function_l (ZF.modelsKP hZF) fn,cert.2.2.1⟩,hinC,hyC⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
