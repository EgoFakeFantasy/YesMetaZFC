import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.IndexPacketCertificate

/-! # 仅以内部 ω 参与求值的原标准索引解包 Σ₁ 源 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def indexPacket_s : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
        indexPacketCheck_m (.bound 9) (.bound 7) (.bound 6) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (indexPacketCheck_delta_l ..))))) }

theorem indexPacket_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 2) (input packet w : M.Domain) :
    Formula.satisfies (((ρ.push input).push packet).push w) indexPacket_s.matrix.body ↔
      ∃ e, M.mem e w ∧ ∃ k, M.mem k w ∧ ∃ c, M.mem c w ∧ ∃ params, M.mem params w ∧
        ∃ P, M.mem P w ∧ IndexPacketCheck_d (ρ.bound 1) input packet e k c params P := by
  simp only [indexPacket_s,Formula.satisfies_existsMem_iff,indexPacketCheck_sat_l hKP]
  rfl

theorem indexPacket_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (input packet : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) :
    indexPacket_s.schema.denote ρ input packet ↔ IndexPacket_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) input packet := by
  rw [S1_binary.sat_l]
  simp only [indexPacket_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,e,_,k,_,c,_,params,_,P,_,cert⟩
    exact indexPacketCheck_sound_l hZF cert
  · rintro ⟨e,k,c,params,he,hk,outer,inner,pair⟩
    obtain ⟨P,cert⟩ := indexPacketCheck_for_l hZF hω he hk outer inner pair
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [e,k,c,params,P]
    exact ⟨w,e,hw e (by simp),k,hw k (by simp),c,hw c (by simp),params,hw params (by simp),P,hw P (by simp),cert⟩

theorem indexPacket_fixed_l (hZF : M.Models ZF) (ρ : Env M 2) {e k c params input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (he : M.mem e (ρ.bound 1)) (hk : M.mem k (ρ.bound 1))
    (outer : KPair_d M input c params) (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) e k c) :
    indexPacket_s.schema.denote ρ input packet ↔ Rd_triple_d packet e k params := by
  rw [indexPacket_sat_l hZF ρ input packet hω]
  constructor
  · rintro ⟨a,b,d,other,_,_,otherPair,inner,code⟩
    obtain ⟨rfl,rfl⟩ := kpair_injective_l M otherPair outer
    obtain ⟨rfl,rfl⟩ := oc_pair_injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF code pair
    exact inner
  · exact fun inner => ⟨e,k,c,params,he,hk,outer,inner,pair⟩

theorem indexPacket_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input packet other : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (left : indexPacket_s.schema.denote ρ input packet)
    (right : indexPacket_s.schema.denote ρ input other) : packet = other := by
  obtain ⟨e,k,c,params,he,hk,outer,inner,pair⟩ := (indexPacket_sat_l hZF ρ input packet hω).mp left
  have inner' := (indexPacket_fixed_l hZF ρ hω he hk outer pair).mp right
  exact normalizedTriple_unique_l hZF.1 inner inner'

theorem indexPacket_build_l (hZF : M.Models ZF) (ρ : Env M 2) (e k params : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (he : M.mem e (ρ.bound 1)) (hk : M.mem k (ρ.bound 1)) :
    ∃ c input packet, M.mem c (ρ.bound 1) ∧ KPair_d M input c params ∧ Rd_triple_d packet e k params ∧
      Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) e k c ∧ indexPacket_s.schema.denote ρ input packet := by
  obtain ⟨c,pair⟩ := oc_pair_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (hω.members_areOrdinals hZF e he) (hω.members_areOrdinals hZF k hk)
  obtain ⟨input,outer⟩ := (kp_pair_l (ZF.modelsKP hZF)).total c params
  obtain ⟨q,hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total k params
  obtain ⟨packet,hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total e q
  have inner : Rd_triple_d packet e k params := ⟨q,hq,hp⟩
  exact ⟨c,input,packet,oc_pair_natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω he hk pair,outer,inner,pair,
    (indexPacket_sat_l hZF ρ input packet hω).mpr ⟨e,k,c,params,he,hk,outer,inner,pair⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
