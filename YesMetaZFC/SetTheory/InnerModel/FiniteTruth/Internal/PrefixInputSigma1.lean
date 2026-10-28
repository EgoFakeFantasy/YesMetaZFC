import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PrefixParametersSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateNormalizedInputSigma1

/-! # 固定实际普通参数前缀的原输入工厂 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def PrefixInputCheck_d (ω P input packet l s k X z f g params c x : M.Domain) : Prop :=
  M.mem c ω ∧ KPair_d M input c x ∧ KPair_d M packet c params ∧
    PrefixParameters_d ω P x l s k X z f g params

def prefixInputCheck_m {d} (ω P input packet l s k X z f g params c x : Term d) : Formula 1 d :=
  .conj (.mem c ω) <| .conj (kpair0_m input c x) <| .conj (kpair0_m packet c params)
    (prefixParameters_m ω P x l s k X z f g params)
derive_free_closed prefixInputCheck_m

theorem prefixInputCheck_delta_l {d} (ω P input packet l s k X z f g params c x : Term d) :
    (prefixInputCheck_m ω P input packet l s k X z f g params c x).IsDelta0 :=
  .conj (.mem _ _) (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (prefixParameters_delta_l ..)))

theorem prefixInputCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω P input packet l s k X z f g params c x : Term d) :
    Formula.satisfies ρ (prefixInputCheck_m ω P input packet l s k X z f g params c x) ↔
      PrefixInputCheck_d (ω.eval ρ) (P.eval ρ) (input.eval ρ) (packet.eval ρ) (l.eval ρ) (s.eval ρ)
        (k.eval ρ) (X.eval ρ) (z.eval ρ) (f.eval ρ) (g.eval ρ) (params.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [prefixInputCheck_m,PrefixInputCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    kpair0_sat_l hKP.1,prefixParameters_sat_l hKP]

def PrefixInput_d (ω P input packet : M.Domain) : Prop :=
  ∃ l s k X z f g params c x, PrefixInputCheck_d ω P input packet l s k X z f g params c x

def prefixInput_s : S1_binary 3 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <|
          Formula.existsMem (.bound 9) <|
            prefixInputCheck_m (.bound 14) (.bound 15) (.bound 12) (.bound 11)
              (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (prefixInputCheck_delta_l ..)))))))))) }

theorem prefixInput_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 3) (input packet w : M.Domain) :
    Formula.satisfies (((ρ.push input).push packet).push w) prefixInput_s.matrix.body ↔
      ∃ l, M.mem l w ∧ ∃ s, M.mem s w ∧ ∃ k, M.mem k w ∧ ∃ X, M.mem X w ∧
        ∃ z, M.mem z w ∧ ∃ f, M.mem f w ∧ ∃ g, M.mem g w ∧ ∃ params, M.mem params w ∧
          ∃ c, M.mem c w ∧ ∃ x, M.mem x w ∧
            PrefixInputCheck_d (ρ.bound 1) (ρ.bound 2) input packet l s k X z f g params c x := by
  simp only [prefixInput_s,Formula.satisfies_existsMem_iff,prefixInputCheck_sat_l hKP]
  rfl

theorem prefixInput_sat_l (hKP : M.Models KP) (ρ : Env M 3) (input packet : M.Domain) :
    prefixInput_s.schema.denote ρ input packet ↔ PrefixInput_d (ρ.bound 1) (ρ.bound 2) input packet := by
  rw [S1_binary.sat_l]
  simp only [prefixInput_matrix_sat_l hKP]
  constructor
  · rintro ⟨w,l,_,s,_,k,_,X,_,z,_,f,_,g,_,params,_,c,_,x,_,cert⟩
    exact ⟨l,s,k,X,z,f,g,params,c,x,cert⟩
  · rintro ⟨l,s,k,X,z,f,g,params,c,x,cert⟩
    obtain ⟨w,hw⟩ := finiteTruth_cover_l hKP [l,s,k,X,z,f,g,params,c,x]
    exact ⟨w,l,hw l (by simp),s,hw s (by simp),k,hw k (by simp),X,hw X (by simp),z,hw z (by simp),
      f,hw f (by simp),g,hw g (by simp),params,hw params (by simp),c,hw c (by simp),x,hw x (by simp),cert⟩

theorem prefixInput_unique_l (hZF : M.Models ZF) (ρ : Env M 3) {input packet other : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (left : prefixInput_s.schema.denote ρ input packet)
    (right : prefixInput_s.schema.denote ρ input other) : packet = other := by
  obtain ⟨l,s,k,X,z,f,g,params,c,x,hc,outer,inner,cert⟩ := (prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mp left
  obtain ⟨l',s',k',Y,z',f',g',params',c',x',_,outer',inner',cert'⟩ := (prefixInput_sat_l (ZF.modelsKP hZF) ρ input other).mp right
  obtain ⟨eqc,eqx⟩ := kpair_injective_l M outer' outer
  subst c'; subst x'
  have eq := cert.unique_l hZF hω cert'
  subst params'
  exact (kp_pair_l (ZF.modelsKP hZF)).unique inner inner'

theorem prefixInput_build_l (hZF : M.Models ZF) (ρ : Env M 3) {input c x l X z : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hc : M.mem c (ρ.bound 1)) (outer : KPair_d M input c x)
    (hl : M.mem l (ρ.bound 1)) (zero : Num_d 0 z) (hz : M.mem z X) (hx : M.mem x X)
    (pref : Fn0_d l X (ρ.bound 2)) : ∃ packet, prefixInput_s.schema.denote ρ input packet := by
  obtain ⟨s,k,f,g,params,cert⟩ := prefixParameters_exists_l hZF hω hl zero hz hx pref
  obtain ⟨packet,inner⟩ := (kp_pair_l (ZF.modelsKP hZF)).total c params
  exact ⟨packet,(prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mpr ⟨l,s,k,X,z,f,g,params,c,x,hc,outer,inner,cert⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
