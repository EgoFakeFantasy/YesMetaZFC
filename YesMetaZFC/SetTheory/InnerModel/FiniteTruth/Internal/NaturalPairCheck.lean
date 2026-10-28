import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteCodingBounds
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruth

/-! # 规范自然数配对的完整 Δ₀ 证书

保存有限方块、完整规范关系和整张真实塌缩图，不以截断真值替代序型。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
universe u
variable {M : SetTheory.Structure.{u}}

def NaturalPairCheck_d (ω a b c n X R Y F p : M.Domain) : Prop :=
  M.mem n ω ∧ M.mem a n ∧ M.mem b n ∧ M.mem Y ω ∧ M.IsOrdinal n ∧
    CanonicalOrderCheck_d n X R ∧ KPair_d M p a b ∧ M.mem p X ∧
      CollapseCheck_d X R Y F ∧ Rd_entry_d p c F

def naturalPairCheck_m {d} (ω a b c n X R Y F p : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (.mem a n) <| .conj (.mem b n) <| .conj (.mem Y ω) <|
    .conj (KP.ord0_m n) <| .conj (canonicalOrderCheck_m n X R) <|
      .conj (kpair0_m p a b) <| .conj (.mem p X) <|
        .conj (collapseCheck_m X R Y F) (rd_entry0_m p c F)
derive_free_closed naturalPairCheck_m

theorem naturalPairCheck_delta_l {d} (ω a b c n X R Y F p : Term d) :
    (naturalPairCheck_m ω a b c n X R Y F p).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _)
    (.conj (KP.ord0_delta_l _) (.conj (canonicalOrderCheck_delta_l ..) (.conj (kpair0_delta_l ..)
      (.conj (.mem _ _) (.conj (collapseCheck_delta_l ..) (rd_entry0_delta_l ..)))))))))

theorem naturalPairCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω a b c n X R Y F p : Term d) :
    Formula.satisfies ρ (naturalPairCheck_m ω a b c n X R Y F p) ↔
      NaturalPairCheck_d (ω.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (n.eval ρ)
        (X.eval ρ) (R.eval ρ) (Y.eval ρ) (F.eval ρ) (p.eval ρ) := by
  simp only [naturalPairCheck_m,NaturalPairCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    KP.ord0_sat_l hKP,canonicalOrderCheck_sat_l hKP.1,kpair0_sat_l hKP.1,collapseCheck_sat_l hKP.1,rd_entry0_sat_l hKP.1]

/-- 从实际完整核验恢复原规范配对，背景不要求模型外部良基。 -/
theorem naturalPairCheck_sound_l (hZF : M.Models ZF) {ω a b c n X R Y F p : M.Domain}
    (cert : NaturalPairCheck_d ω a b c n X R Y F p) :
    Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨_,_,_,_,hn,order,hp,hpX,collapse,entry⟩ := cert
  have horder := (canonicalOrderCheck_correct_l hKP).mp order
  obtain ⟨fn,wc,_,_⟩ := collapseCheck_correct_l.mp collapse
  have func := fn0_function_l hKP fn
  have full : M.IsWellOrderCollapseFunction I F R X X := by
    refine ⟨func.1,func.2.1,⟨fun _ hx => hx,fun _ _ _ hx _ => hx⟩,?_⟩
    intro q _ y hqy
    exact (wc.2 q y hqy).2.2
  exact ⟨n,p,hp,hn,X,R,horder,hpX,
    full.collapseValue_of_pairMember hZF I (horder.isSetCodedWellOrder hZF hn) hpX entry⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
