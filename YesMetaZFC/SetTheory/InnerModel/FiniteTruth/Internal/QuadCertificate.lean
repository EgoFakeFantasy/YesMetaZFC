import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldCertificate

/-! # 原四字段指令数码的完整有界证书

保留 c=(t,(i,(j,k))) 和原三次规范配对；所有字段及中间数值明确为内部自然数。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def NaturalQuad_d (ω c : M.Domain) : Prop := ∃ t v i p j k,
  M.mem t ω ∧ M.mem i ω ∧ M.mem j ω ∧ M.mem k ω ∧ KPair_d M c t v ∧ KPair_d M v i p ∧ KPair_d M p j k

def naturalQuad_m {d} (ω c : Term d) : Formula 1 d :=
  Formula.existsMem ω <| .existsE <| Formula.existsMem ω.weaken.weaken <| .existsE <|
    Formula.existsMem ω.weaken.weaken.weaken.weaken <| Formula.existsMem ω.weaken.weaken.weaken.weaken.weaken <|
      .conj (kpair0_m c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4)) <|
        .conj (kpair0_m (.bound 4) (.bound 3) (.bound 2)) (kpair0_m (.bound 2) (.bound 1) .newest)
derive_free_closed naturalQuad_m

theorem naturalQuad_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c : Term d) :
    Formula.satisfies ρ (naturalQuad_m ω c) ↔ NaturalQuad_d (ω.eval ρ) (c.eval ρ) := by
  simp only [naturalQuad_m,NaturalQuad_d,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,kpair0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  constructor
  · rintro ⟨t,ht,v,i,hi,p,j,hj,k,hk,hc,hv,hp⟩
    exact ⟨t,v,i,p,j,k,ht,hi,hj,hk,hc,hv,hp⟩
  · rintro ⟨t,v,i,p,j,k,ht,hi,hj,hk,hc,hv,hp⟩
    exact ⟨t,ht,v,i,hi,p,j,hj,k,hk,hc,hv,hp⟩

theorem naturalQuad_decompose_l (hZF : M.Models ZF) {ω c z : M.Domain} (hω : M.IsOmega ω)
    (input : NaturalQuad_d ω c) (code : QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z) :
    ∃ t v i p j k a b, M.mem t ω ∧ M.mem i ω ∧ M.mem j ω ∧ M.mem k ω ∧ M.mem a ω ∧ M.mem b ω ∧
      KPair_d M c t v ∧ KPair_d M v i p ∧ KPair_d M p j k ∧
      Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) j k a ∧ Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) i a b ∧
      Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) t b z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨t,v,i,p,j,k,ht,hi,hj,hk,hc,hv,hp⟩ := input
  obtain ⟨t',v',i',p',j',k',a,b,hc',hv',hp',ha,hb,hz⟩ := code
  obtain ⟨rfl,rfl⟩ := I.injective hc hc'
  obtain ⟨rfl,rfl⟩ := I.injective hv hv'
  obtain ⟨rfl,rfl⟩ := I.injective hp hp'
  have haω := oc_pair_natural_l I hZF hω hj hk ha
  have hbω := oc_pair_natural_l I hZF hω hi haω hb
  exact ⟨t,v,i,p,j,k,a,b,ht,hi,hj,hk,haω,hbω,hc,hv,hp,ha,hb,hz⟩

def QuadCore_d (ω c z t v i p j k a b u x y : M.Domain) : Prop :=
  KPair_d M c t v ∧ KPair_d M v i p ∧ KPair_d M p j k ∧
    PairWitness_d ω j k a u ∧ PairWitness_d ω i a b x ∧ PairWitness_d ω t b z y

def quadCore_m {d} (ω c z t v i p j k a b u x y : Term d) : Formula 1 d :=
  .conj (kpair0_m c t v) <| .conj (kpair0_m v i p) <| .conj (kpair0_m p j k) <|
    .conj (pairWitness_m ω j k a u) <| .conj (pairWitness_m ω i a b x) (pairWitness_m ω t b z y)
derive_free_closed quadCore_m

theorem quadCore_delta_l {d} (ω c z t v i p j k a b u x y : Term d) :
    (quadCore_m ω c z t v i p j k a b u x y).IsDelta0 :=
  .conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (pairWitness_delta_l ..) (.conj (pairWitness_delta_l ..) (pairWitness_delta_l ..)))))

theorem quadCore_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c z t v i p j k a b u x y : Term d) :
    Formula.satisfies ρ (quadCore_m ω c z t v i p j k a b u x y) ↔
      QuadCore_d (ω.eval ρ) (c.eval ρ) (z.eval ρ) (t.eval ρ) (v.eval ρ) (i.eval ρ) (p.eval ρ)
        (j.eval ρ) (k.eval ρ) (a.eval ρ) (b.eval ρ) (u.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [quadCore_m,QuadCore_d,Formula.satisfies_conj_iff,kpair0_sat_l hKP.1,pairWitness_sat_l hKP]

def QuadCheck_d (ω c z W : M.Domain) : Prop :=
  ∃ t, M.mem t ω ∧ ∃ v, M.mem v W ∧ ∃ i, M.mem i ω ∧ ∃ p, M.mem p W ∧
    ∃ j, M.mem j ω ∧ ∃ k, M.mem k ω ∧ ∃ a, M.mem a ω ∧ ∃ b, M.mem b ω ∧
      ∃ u, M.mem u W ∧ ∃ x, M.mem x W ∧ ∃ y, M.mem y W ∧ QuadCore_d ω c z t v i p j k a b u x y

def quadCheck_m {d} (ω c z W : Term d) : Formula 1 d :=
  Formula.existsMem ω <| Formula.existsMem W.weaken <| Formula.existsMem ω.weaken.weaken <|
    Formula.existsMem W.weaken.weaken.weaken <| Formula.existsMem ω.weaken.weaken.weaken.weaken <|
      Formula.existsMem ω.weaken.weaken.weaken.weaken.weaken <|
        Formula.existsMem ω.weaken.weaken.weaken.weaken.weaken.weaken <|
          Formula.existsMem ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken <|
            Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken <|
              Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken <|
                Formula.existsMem W.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken <|
                  quadCore_m ω.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    c.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    z.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
                    (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed quadCheck_m

theorem quadCheck_delta_l {d} (ω c z W : Term d) : (quadCheck_m ω c z W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (quadCore_delta_l ..)))))))))))

theorem quadCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω c z W : Term d) :
    Formula.satisfies ρ (quadCheck_m ω c z W) ↔ QuadCheck_d (ω.eval ρ) (c.eval ρ) (z.eval ρ) (W.eval ρ) := by
  simp only [quadCheck_m,QuadCheck_d,Formula.satisfies_existsMem_iff,quadCore_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem quadCheck_sound_l (hZF : M.Models ZF) {ω c z W : M.Domain} (cert : QuadCheck_d ω c z W) :
    NaturalQuad_d ω c ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
  obtain ⟨t,ht,v,_,i,hi,p,_,j,hj,k,hk,a,_,b,_,u,_,x,_,y,_,hc,hv,hp,ha,hb,hz⟩ := cert
  exact ⟨⟨t,v,i,p,j,k,ht,hi,hj,hk,hc,hv,hp⟩,t,v,i,p,j,k,a,b,hc,hv,hp,
    pairWitness_sound_l hZF ha,pairWitness_sound_l hZF hb,pairWitness_sound_l hZF hz⟩

theorem quadCheck_exists_l (hZF : M.Models ZF) {ω c z : M.Domain}
    (hω : M.IsOmega ω) (input : NaturalQuad_d ω c)
    (code : QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z) : ∃ W, QuadCheck_d ω c z W := by
  obtain ⟨t,v,i,p,j,k,a,b,ht,hi,hj,hk,ha,hb,hc,hv,hp,p1,p2,p3⟩ := naturalQuad_decompose_l hZF hω input code
  obtain ⟨u,hu⟩ := pairWitness_exists_l hZF hω hj hk p1
  obtain ⟨x,hx⟩ := pairWitness_exists_l hZF hω hi ha p2
  obtain ⟨y,hy⟩ := pairWitness_exists_l hZF hω ht hb p3
  obtain ⟨W,all⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [v,p,u,x,y]
  exact ⟨W,t,ht,v,all v (by simp),i,hi,p,all p (by simp),j,hj,k,hk,a,ha,b,hb,
    u,all u (by simp),x,all x (by simp),y,all y (by simp),hc,hv,hp,hu,hx,hy⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
