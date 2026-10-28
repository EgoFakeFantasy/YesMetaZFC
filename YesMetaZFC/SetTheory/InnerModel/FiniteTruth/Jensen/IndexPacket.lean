import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.IndexPacketSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NaturalPair
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNormalizedInput

/-! # 同一原 J 层内的完整标准索引解包证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_indexPacketCheck_l (hZF : M.Models ZF) {α C ω input packet : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hinC : M.mem input C) (graph : IndexPacket_d (kp_pair_l (ZF.modelsKP hZF)) ω input packet) :
    M.mem packet C ∧ ∃ e k c params P, M.mem e C ∧ M.mem k C ∧ M.mem c C ∧ M.mem params C ∧ M.mem P C ∧
      IndexPacketCheck_d ω input packet e k c params P := by
  obtain ⟨e,k,c,params,he,hk,outer,inner,pair⟩ := graph
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have coords := po_pair_bound_l trans hinC outer
  have heC := trans ω hωC e he
  have hkC := trans ω hωC k hk
  have hpC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .triple e k params heC hkC coords.2 packet (rd_triple_value_l hZF.1 inner)
  let η : Env M 2 := ⟨Fin.cases k (fun _ => ω),fun _ => ω⟩
  obtain ⟨P,hPC,body⟩ := (jh_naturalPair_within_l hZF hα h η e c hω hωC he hk).mpr pair
  have cert : PairWitness_d ω e k c P := (naturalPair_matrix_sat_l (ZF.modelsKP hZF) η e c P).mp body
  exact ⟨hpC,e,k,c,params,P,heC,hkC,coords.1,coords.2,hPC,he,hk,outer,inner,cert⟩

theorem jh_indexPacket_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) (input packet : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C) :
    Within_d indexPacket_s ρ input packet C ↔ IndexPacket_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) input packet := by
  constructor
  · rintro ⟨w,_,body⟩
    obtain ⟨e,_,k,_,c,_,params,_,P,_,cert⟩ := (indexPacket_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mp body
    exact indexPacketCheck_sound_l hZF cert
  · intro graph
    obtain ⟨_,e,k,c,params,P,heC,hkC,hcC,hpC,hPC,cert⟩ := jh_indexPacketCheck_l hZF hα h hω hωC hinC graph
    have all : ∀ v, v ∈ [e,k,c,params,P] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [e,k,c,params,P] all
    exact ⟨w,hwC,(indexPacket_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mpr
      ⟨e,hw e (by simp),k,hw k (by simp),c,hw c (by simp),params,hw params (by simp),P,hw P (by simp),cert⟩⟩

theorem jh_indexPacket_output_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (graph : indexPacket_s.schema.denote ρ input packet) : M.mem packet C :=
  (jh_indexPacketCheck_l hZF hα h hω hωC hinC ((indexPacket_sat_l hZF ρ input packet hω).mp graph)).1

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
