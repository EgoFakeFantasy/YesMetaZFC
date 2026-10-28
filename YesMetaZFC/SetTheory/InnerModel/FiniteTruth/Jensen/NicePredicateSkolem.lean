import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexPacket
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateParameterSkolem

/-! # 单内部自然数与有限普通参数列上的实际谓词函数 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def nicePredicateSkolem_s : S1_binary 2 := indexPacket_s.comp predicateParameterSkolem_s

theorem nicePredicateSkolem_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (input y : M.Domain) :
    nicePredicateSkolem_s.schema.denote ρ input y ↔ ∃ packet, indexPacket_s.schema.denote ρ input packet ∧
      predicateParameterSkolem_s.schema.denote ρ packet y :=
  S1_binary.comp_sat_l (ZF.modelsKP hZF) indexPacket_s predicateParameterSkolem_s ρ input y

theorem nicePredicateSkolem_sound_l (hZF : M.Models ZF) (ρ : Env M 2) {input y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (selected : nicePredicateSkolem_s.schema.denote ρ input y) :
    ∃ packet, IndexPacket_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 1) input packet ∧
      predicateParameterSkolem_s.schema.denote ρ packet y := by
  obtain ⟨packet,graph,choice⟩ := (nicePredicateSkolem_sat_l hZF ρ input y).mp selected
  exact ⟨packet,(indexPacket_sat_l hZF ρ input packet hω).mp graph,choice⟩

theorem nicePredicateSkolem_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {input y z : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hy : nicePredicateSkolem_s.schema.denote ρ input y)
    (hz : nicePredicateSkolem_s.schema.denote ρ input z) : y = z := by
  obtain ⟨p,hp,sy⟩ := (nicePredicateSkolem_sat_l hZF ρ input y).mp hy
  obtain ⟨q,hq,sz⟩ := (nicePredicateSkolem_sat_l hZF ρ input z).mp hz
  have eq := indexPacket_unique_l hZF ρ hω hp hq
  subst q
  exact predicateParameterSkolem_unique_l hZF ρ hω sy sz

theorem nicePredicateSkolem_fixed_l (hZF : M.Models ZF) (ρ : Env M 2) {e k c params input packet y : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (he : M.mem e (ρ.bound 1)) (hk : M.mem k (ρ.bound 1))
    (outer : KPair_d M input c params) (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) e k c)
    (inner : Rd_triple_d packet e k params) :
    nicePredicateSkolem_s.schema.denote ρ input y ↔ predicateParameterSkolem_s.schema.denote ρ packet y := by
  have graph := (indexPacket_fixed_l hZF ρ hω he hk outer pair).mpr inner
  rw [nicePredicateSkolem_sat_l hZF]
  constructor
  · rintro ⟨other,hother,selected⟩
    have eq := indexPacket_unique_l hZF ρ hω hother graph
    subst other
    exact selected
  · exact fun selected => ⟨packet,graph,selected⟩

theorem jh_nicePredicateSkolem_function_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1))
    (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet y, M.mem y C ∧ indexPacket_s.schema.denote ρ input packet ∧
      predicateParameterSkolem_s.schema.denote ρ packet y) :
    ∃ y, M.mem y C ∧ Within_d nicePredicateSkolem_s ρ input y C ∧ nicePredicateSkolem_s.schema.denote ρ input y ∧
      ∀ z, nicePredicateSkolem_s.schema.denote ρ input z → z = y := by
  obtain ⟨packet,y,hyC,graph,choice⟩ := existsWitness
  have hpC := jh_indexPacket_output_l hZF hα h ρ hω hωC hinC graph
  have first := (jh_indexPacket_within_l hZF hα h ρ input packet hω hωC hinC).mpr
    ((indexPacket_sat_l hZF ρ input packet hω).mp graph)
  obtain ⟨normal,hnormal,fiber⟩ := predicateParameterSkolem_sound_l hZF ρ hω choice
  have existsOld : ∃ normal y, M.mem y C ∧ pnormalizedInput_s.schema.denote ρ packet normal ∧
      PWitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 1) normal y := ⟨normal,y,hyC,(pnormalizedInput_sat_l hZF ρ packet normal hω).mpr hnormal,fiber⟩
  have second := (jh_predicateParameterSkolem_capture_l hZF hα h ρ amenable hω hωC hpC existsOld choice).2
  have hit := (within_comp_cover_l (ZF.modelsKP hZF) (jh_value_transitive_l (ZF.models_kpi_l hZF) h)
    (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC indexPacket_s predicateParameterSkolem_s ρ input y).mpr
      ⟨packet,hpC,first,second⟩
  have selected := (nicePredicateSkolem_sat_l hZF ρ input y).mpr ⟨packet,graph,choice⟩
  exact ⟨y,hyC,hit,selected,fun z hz => nicePredicateSkolem_unique_l hZF ρ hω hz selected⟩

theorem jh_nicePredicateSkolem_capture_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2) {input y : M.Domain}
    (amenable : AmenableSet_d C (ρ.bound 0)) (hω : M.IsOmega (ρ.bound 1))
    (hωC : M.mem (ρ.bound 1) C) (hinC : M.mem input C)
    (existsWitness : ∃ packet z, M.mem z C ∧ indexPacket_s.schema.denote ρ input packet ∧
      predicateParameterSkolem_s.schema.denote ρ packet z)
    (selected : nicePredicateSkolem_s.schema.denote ρ input y) : M.mem y C ∧ Within_d nicePredicateSkolem_s ρ input y C := by
  obtain ⟨z,hzC,hz,_,unique⟩ := jh_nicePredicateSkolem_function_l hZF hα h ρ amenable hω hωC hinC existsWitness
  have eq := unique y selected
  subst y
  exact ⟨hzC,hz⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
