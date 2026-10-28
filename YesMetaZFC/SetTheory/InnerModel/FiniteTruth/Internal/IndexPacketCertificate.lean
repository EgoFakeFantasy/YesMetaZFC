import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNormalizedInputSigma1

/-! # 单自然数索引输入到原三元输入的完整配对证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def IndexPacket_d (I : kpair_convention_l.Interpretation M) (ω input packet : M.Domain) : Prop :=
  ∃ e k c params, M.mem e ω ∧ M.mem k ω ∧ KPair_d M input c params ∧
    Rd_triple_d packet e k params ∧ Oc_pair_d I e k c

def IndexPacketCheck_d (ω input packet e k c params P : M.Domain) : Prop :=
  M.mem e ω ∧ M.mem k ω ∧ KPair_d M input c params ∧ Rd_triple_d packet e k params ∧ PairWitness_d ω e k c P

def indexPacketCheck_m {d} (ω input packet e k c params P : Term d) : Formula 1 d :=
  .conj (.mem e ω) <| .conj (.mem k ω) <| .conj (kpair0_m input c params) <|
    .conj (rd_triple0_m packet e k params) (pairWitness_m ω e k c P)
derive_free_closed indexPacketCheck_m

theorem indexPacketCheck_delta_l {d} (ω input packet e k c params P : Term d) :
    (indexPacketCheck_m ω input packet e k c params P).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (kpair0_delta_l ..) (.conj (rd_triple0_delta_l ..) (pairWitness_delta_l ..))))

theorem indexPacketCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω input packet e k c params P : Term d) :
    Formula.satisfies ρ (indexPacketCheck_m ω input packet e k c params P) ↔
      IndexPacketCheck_d (ω.eval ρ) (input.eval ρ) (packet.eval ρ) (e.eval ρ) (k.eval ρ) (c.eval ρ) (params.eval ρ) (P.eval ρ) := by
  simp only [indexPacketCheck_m,IndexPacketCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    kpair0_sat_l hKP.1,rd_triple0_sat_l hKP.1,pairWitness_sat_l hKP]

theorem indexPacketCheck_sound_l (hZF : M.Models ZF) {ω input packet e k c params P : M.Domain}
    (cert : IndexPacketCheck_d ω input packet e k c params P) :
    IndexPacket_d (kp_pair_l (ZF.modelsKP hZF)) ω input packet :=
  ⟨e,k,c,params,cert.1,cert.2.1,cert.2.2.1,cert.2.2.2.1,pairWitness_sound_l hZF cert.2.2.2.2⟩

theorem indexPacketCheck_for_l (hZF : M.Models ZF) {ω input packet e k c params : M.Domain}
    (hω : M.IsOmega ω) (he : M.mem e ω) (hk : M.mem k ω) (outer : KPair_d M input c params)
    (inner : Rd_triple_d packet e k params) (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) e k c) :
    ∃ P, IndexPacketCheck_d ω input packet e k c params P := by
  obtain ⟨P,cert⟩ := pairWitness_exists_l hZF hω he hk pair
  exact ⟨P,he,hk,outer,inner,cert⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
