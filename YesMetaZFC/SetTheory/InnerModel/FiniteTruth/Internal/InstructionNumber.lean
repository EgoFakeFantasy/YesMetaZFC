import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedFormulaCode
import YesMetaZFC.SetTheory.Ord.Code.Sequence

/-! # 原四字段指令的规范自然数编号

保留实际代码 c = (t,(i,(j,k)))，用三次原规范序数配对编号。
此关系的原公式尚未给出有界证书或小层绝对性，不能直接充当局部 Σ₁ 解码器。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}
variable (I : 𝒞.Interpretation M)

def QuadNumber_d (c z : M.Domain) : Prop := ∃ t v i p j k a b,
  I.Codes c t v ∧ I.Codes v i p ∧ I.Codes p j k ∧
    Oc_pair_d I j k a ∧ Oc_pair_d I i a b ∧ Oc_pair_d I t b z

def quadNumber_m {d} (c z : Term d) : Formula 1 d :=
  .existsE <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (𝒞.code c.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 7) (.bound 6)) <|
      .conj (𝒞.code (.bound 6) (.bound 5) (.bound 4)) <|
        .conj (𝒞.code (.bound 4) (.bound 3) (.bound 2)) <|
          .conj (oc_pair_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1)) <|
            .conj (oc_pair_m (𝒞 := 𝒞) (.bound 5) (.bound 1) .newest)
              (oc_pair_m (𝒞 := 𝒞) (.bound 7) .newest z.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
derive_free_closed quadNumber_m

theorem quadNumber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (c z : Term d) :
    Formula.satisfies ρ (quadNumber_m (𝒞 := 𝒞) c z) ↔ QuadNumber_d I (c.eval ρ) (z.eval ρ) := by
  simp only [quadNumber_m,QuadNumber_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    I.satisfies_code_iff,oc_pair_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

theorem quadNumber_unique_l (hZF : M.Models ZF) {c z w : M.Domain}
    (h : QuadNumber_d I c z) (g : QuadNumber_d I c w) : z = w := by
  obtain ⟨t,v,i,p,j,k,a,b,hc,hv,hp,ha,hb,hz⟩ := h
  obtain ⟨s,v',i',p',j',k',a',b',hc',hv',hp',ha',hb',hw⟩ := g
  obtain ⟨rfl,rfl⟩ := I.injective hc hc'
  obtain ⟨rfl,rfl⟩ := I.injective hv hv'
  obtain ⟨rfl,rfl⟩ := I.injective hp hp'
  have eq := oc_pair_unique_l I hZF ha ha'; subst a'
  have eq := oc_pair_unique_l I hZF hb hb'; subst b'
  exact oc_pair_unique_l I hZF hz hw

theorem quadNumber_injective_l (hZF : M.Models ZF) {c d z : M.Domain}
    (h : QuadNumber_d I c z) (g : QuadNumber_d I d z) : c = d := by
  obtain ⟨t,v,i,p,j,k,a,b,hc,hv,hp,ha,hb,hz⟩ := h
  obtain ⟨s,v',i',p',j',k',a',b',hd,hv',hp',ha',hb',hw⟩ := g
  obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF hz hw
  obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF hb hb'
  obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF ha ha'
  have eq := I.unique hp hp'; subst p'
  have eq := I.unique hv hv'; subst v'
  exact I.unique hc hd

theorem quadNumber_exists_l (hZF : M.Models ZF) {ω c t v i p j k : M.Domain}
    (hω : M.IsOmega ω) (hc : I.Codes c t v) (hv : I.Codes v i p) (hp : I.Codes p j k)
    (ht : M.mem t ω) (hi : M.mem i ω) (hj : M.mem j ω) (hk : M.mem k ω) :
    ∃ z, M.mem z ω ∧ QuadNumber_d I c z := by
  obtain ⟨a,ha⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF j hj) (hω.members_areOrdinals hZF k hk)
  have haω := oc_pair_natural_l I hZF hω hj hk ha
  obtain ⟨b,hb⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF i hi) (hω.members_areOrdinals hZF a haω)
  have hbω := oc_pair_natural_l I hZF hω hi haω hb
  obtain ⟨z,hz⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF t ht) (hω.members_areOrdinals hZF b hbω)
  exact ⟨z,oc_pair_natural_l I hZF hω ht hbω hz,t,v,i,p,j,k,a,b,hc,hv,hp,ha,hb,hz⟩

/-- 合法四类指令的全部字段都在内部 ω 中，故其编号仍是内部自然数。 -/
theorem bnode_number_exists_l (hZF : M.Models ZF) {T ω n r c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hr : M.mem r ω) (h : Bnode_d T ω n r c) :
    ∃ z, M.mem z ω ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
  have one (tag : Nat) {A B D : M.Domain} (aω : M.MemberSubset A ω)
      (bω : M.MemberSubset B ω) (dω : M.MemberSubset D ω) (hc : Bcase_d T tag c A B D) :
      ∃ z, M.mem z ω ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
    obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,⟨p,hp,hv⟩,hc⟩,hi,hj,hk⟩ := hc
    exact quadNumber_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω hc hv hp
      (num_mem_l hZF.1 hω ht) (aω i hi) (bω j hj) (dω k hk)
  have nω := hω.transitive hZF n hn
  have rω := hω.transitive hZF r hr
  rcases h with h | h | h | h
  · exact one 0 nω nω (fun _ h => h) h
  · exact one 1 nω nω (fun _ h => h) h
  · exact one 2 rω rω (fun _ h => h) h
  · exact one 3 nω nω rω h

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
