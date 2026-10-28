import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.InstructionNumber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless.CollapseCertificate

/-! # 规范序数对次序的完整有界核验

同时检查方块的全部成员与全部输入对，以及关系的全部条目和全部比较。
所有坐标及最大值有界于给定方块边长，供规范配对的局部证书使用。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def ProductCheck_d (X A B : M.Domain) : Prop :=
  (∀ p, M.mem p X → ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ KPair_d M p a b) ∧
  ∀ a, M.mem a A → ∀ b, M.mem b B → ∃ p, M.mem p X ∧ KPair_d M p a b

def productCheck_m {d} (X A B : Term d) : Formula 1 d :=
  .conj (Formula.forallMem X <| Formula.existsMem A.weaken <| Formula.existsMem B.weaken.weaken <|
    kpair0_m (.bound 2) (.bound 1) .newest) <|
    Formula.forallMem A <| Formula.forallMem B.weaken <| Formula.existsMem X.weaken.weaken <|
      kpair0_m .newest (.bound 2) (.bound 1)
derive_free_closed productCheck_m

theorem productCheck_delta_l {d} (X A B : Term d) : (productCheck_m X A B).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.existsMem _ (kpair0_delta_l ..))))

theorem productCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X A B : Term d) :
    Formula.satisfies ρ (productCheck_m X A B) ↔ ProductCheck_d (X.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [productCheck_m,ProductCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,kpair0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem productCheck_correct_l (hKP : M.Models KP) {X A B : M.Domain} :
    ProductCheck_d X A B ↔ M.IsCartesianProduct (kp_pair_l hKP) X A B := by
  let I := kp_pair_l hKP
  constructor
  · intro h p
    constructor
    · exact h.1 p
    · rintro ⟨a,ha,b,hb,hp⟩
      obtain ⟨q,hq,hpair⟩ := h.2 a ha b hb
      exact (I.unique hp hpair).symm ▸ hq
  · intro h
    refine ⟨fun p hp => (h p).mp hp,fun a ha b hb => ?_⟩
    obtain ⟨p,hp⟩ := I.total a b
    exact ⟨p,(h p).mpr ⟨a,ha,b,hb,hp⟩,hp⟩

def PairLessCheck_d (n p q : M.Domain) : Prop :=
  ∃ a, M.mem a n ∧ ∃ b, M.mem b n ∧ ∃ c, M.mem c n ∧ ∃ d, M.mem d n ∧
    ∃ s, M.mem s n ∧ ∃ t, M.mem t n ∧ KPair_d M p a b ∧ KPair_d M q c d ∧
      M.IsOrdinalMaximum a b s ∧ M.IsOrdinalMaximum c d t ∧
        (M.mem s t ∨ (s = t ∧ (M.mem a c ∨ (a = c ∧ M.mem b d))))

def pairLessCheck_m {d} (n p q : Term d) : Formula 1 d :=
  Formula.existsMem n <| Formula.existsMem n.weaken <| Formula.existsMem n.weaken.weaken <|
    Formula.existsMem n.weaken.weaken.weaken <| Formula.existsMem n.weaken.weaken.weaken.weaken <|
      Formula.existsMem n.weaken.weaken.weaken.weaken.weaken <|
        .conj (kpair0_m p.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4)) <|
          .conj (kpair0_m q.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 2)) <|
            .conj (Formula.isOrdinalMaximum (.bound 5) (.bound 4) (.bound 1)) <|
              .conj (Formula.isOrdinalMaximum (.bound 3) (.bound 2) .newest) <|
                .disj (.mem (.bound 1) .newest) <| .conj (Formula.extensionalEq (.bound 1) .newest) <|
                  .disj (.mem (.bound 5) (.bound 3)) <|
                    .conj (Formula.extensionalEq (.bound 5) (.bound 3)) (.mem (.bound 4) (.bound 2))
derive_free_closed pairLessCheck_m

private theorem maximum_delta_l {d} (a b c : Term d) : (Formula.isOrdinalMaximum a b c).IsDelta0 :=
  .disj (.conj (.atom _ _ _) (.disj (.atom _ _ _) (.mem _ _))) (.conj (.atom _ _ _) (.mem _ _))

theorem pairLessCheck_delta_l {d} (n p q : Term d) : (pairLessCheck_m n p q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (maximum_delta_l ..)
      (.conj (maximum_delta_l ..) (.disj (.mem _ _) (.conj (.atom _ _ _)
        (.disj (.mem _ _) (.conj (.atom _ _ _) (.mem _ _))))))))))))))

theorem pairLessCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n p q : Term d) :
    Formula.satisfies ρ (pairLessCheck_m n p q) ↔ PairLessCheck_d (n.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [pairLessCheck_m,PairLessCheck_d,Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff,kpair0_sat_l hE,Formula.satisfies_isOrdinalMaximum_iff hE,
    Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem pairLessCheck_correct_l (hKP : M.Models KP) {n X p q : M.Domain}
    (prod : ProductCheck_d X n n) (hp : M.mem p X) (hq : M.mem q X) :
    PairLessCheck_d n p q ↔ M.CanonicalOrdinalPairLess (kp_pair_l hKP) p q := by
  constructor
  · rintro ⟨a,_,b,_,c,_,d,_,s,_,t,_,hp,hq,hs,ht,less⟩
    exact ⟨a,b,c,d,s,t,hp,hq,hs,ht,less⟩
  · rintro ⟨a,b,c,d,s,t,hpair,hpair',hs,ht,less⟩
    obtain ⟨a',ha,b',hb,hp'⟩ := prod.1 p hp
    obtain ⟨c',hc,d',hd,hq'⟩ := prod.1 q hq
    obtain ⟨rfl,rfl⟩ := (kp_pair_l hKP).injective hpair hp'
    obtain ⟨rfl,rfl⟩ := (kp_pair_l hKP).injective hpair' hq'
    exact ⟨a,ha,b,hb,c,hc,d,hd,s,hs.mem ha hb,t,ht.mem hc hd,hpair,hpair',hs,ht,less⟩

def RelationBound_d (X R : M.Domain) : Prop :=
  ∀ p, M.mem p R → ∃ a, M.mem a X ∧ ∃ b, M.mem b X ∧ KPair_d M p a b

def relationBound_m {d} (X R : Term d) : Formula 1 d :=
  Formula.forallMem R <| Formula.existsMem X.weaken <| Formula.existsMem X.weaken.weaken <|
    kpair0_m (.bound 2) (.bound 1) .newest
derive_free_closed relationBound_m

theorem relationBound_delta_l {d} (X R : Term d) : (relationBound_m X R).IsDelta0 :=
  .forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))

theorem relationBound_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R : Term d) :
    Formula.satisfies ρ (relationBound_m X R) ↔ RelationBound_d (X.eval ρ) (R.eval ρ) := by
  simp only [relationBound_m,RelationBound_d,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,
    kpair0_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem RelationBound_d.at_l (hKP : M.Models KP) {X R a b : M.Domain}
    (h : RelationBound_d X R) (hab : Rd_entry_d a b R) : M.mem a X ∧ M.mem b X := by
  obtain ⟨p,hpair,hp⟩ := hab
  obtain ⟨c,hc,d,hd,hp'⟩ := h p hp
  obtain ⟨rfl,rfl⟩ := (kp_pair_l hKP).injective hpair hp'
  exact ⟨hc,hd⟩

def CanonicalOrderCheck_d (n X R : M.Domain) : Prop := ProductCheck_d X n n ∧ RelationBound_d X R ∧
  ∀ p, M.mem p X → ∀ q, M.mem q X → (Rd_entry_d p q R ↔ PairLessCheck_d n p q)

def canonicalOrderCheck_m {d} (n X R : Term d) : Formula 1 d :=
  .conj (productCheck_m X n n) <| .conj (relationBound_m X R) <|
    Formula.forallMem X <| Formula.forallMem X.weaken <|
      .iff (rd_entry0_m (.bound 1) .newest R.weaken.weaken)
        (pairLessCheck_m n.weaken.weaken (.bound 1) .newest)
derive_free_closed canonicalOrderCheck_m

theorem canonicalOrderCheck_delta_l {d} (n X R : Term d) : (canonicalOrderCheck_m n X R).IsDelta0 :=
  .conj (productCheck_delta_l ..) (.conj (relationBound_delta_l ..)
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (pairLessCheck_delta_l ..)))))

theorem canonicalOrderCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n X R : Term d) :
    Formula.satisfies ρ (canonicalOrderCheck_m n X R) ↔ CanonicalOrderCheck_d (n.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [canonicalOrderCheck_m,CanonicalOrderCheck_d,Formula.satisfies_conj_iff,
    productCheck_sat_l hE,relationBound_sat_l hE,Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hE,pairLessCheck_sat_l hE,Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  rfl

theorem canonicalOrderCheck_correct_l (hKP : M.Models KP) {n X R : M.Domain} :
    CanonicalOrderCheck_d n X R ↔ M.IsCanonicalOrdinalPairOrder (kp_pair_l hKP) R X n := by
  let I := kp_pair_l hKP
  constructor
  · intro h
    have bound {a b} (hab : Rd_entry_d a b R) : M.mem a X ∧ M.mem b X := h.2.1.at_l hKP hab
    refine ⟨productCheck_correct_l hKP |>.mp h.1,⟨?_,fun _ _ hab => bound hab⟩,fun p q => ?_⟩
    · intro t ht
      obtain ⟨a,_,b,_,hp⟩ := h.2.1 t ht
      exact ⟨a,b,hp⟩
    · constructor
      · intro hab
        have b := bound hab
        exact ⟨b.1,b.2,(pairLessCheck_correct_l hKP h.1 b.1 b.2).mp ((h.2.2 p b.1 q b.2).mp hab)⟩
      · rintro ⟨hp,hq,less⟩
        exact (h.2.2 p hp q hq).mpr ((pairLessCheck_correct_l hKP h.1 hp hq).mpr less)
  · intro h
    have prod := (productCheck_correct_l hKP).mpr h.1
    refine ⟨prod,?_,fun p hp q hq => ?_⟩
    · intro t ht
      obtain ⟨p,q,hpair⟩ := h.2.1.1 t ht
      have bounds := h.2.1.2 p q ⟨t,hpair,ht⟩
      exact ⟨p,bounds.1,q,bounds.2,hpair⟩
    · constructor
      · intro hab
        exact (pairLessCheck_correct_l hKP prod hp hq).mpr ((h.2.2 p q).mp hab).2.2
      · intro less
        exact (h.2.2 p q).mpr ⟨hp,hq,(pairLessCheck_correct_l hKP prod hp hq).mp less⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
