import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldRunExistence

/-! # 完整折叠历史和全部配对见证的实际 Δ₀ 核验

覆盖集合可有多余见证，但每个内部步骤都必须找到实际核验通过的见证。
历史图的完整定义域、零值和根值同时核验，避免空前提或截断历史。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def PairWitness_d (ω a b c w : M.Domain) : Prop :=
  ∃ n, M.mem n w ∧ ∃ X, M.mem X w ∧ ∃ R, M.mem R w ∧ ∃ Y, M.mem Y w ∧
    ∃ F, M.mem F w ∧ ∃ p, M.mem p w ∧ NaturalPairCheck_d ω a b c n X R Y F p

def pairWitness_m {d} (ω a b c w : Term d) : Formula 1 d :=
  Formula.existsMem w <| Formula.existsMem w.weaken <| Formula.existsMem w.weaken.weaken <|
    Formula.existsMem w.weaken.weaken.weaken <| Formula.existsMem w.weaken.weaken.weaken.weaken <|
      Formula.existsMem w.weaken.weaken.weaken.weaken.weaken <|
        naturalPairCheck_m ω.weaken.weaken.weaken.weaken.weaken.weaken
          a.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken
          c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
derive_free_closed pairWitness_m

theorem pairWitness_delta_l {d} (ω a b c w : Term d) : (pairWitness_m ω a b c w).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (naturalPairCheck_delta_l ..))))))

theorem pairWitness_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω a b c w : Term d) :
    Formula.satisfies ρ (pairWitness_m ω a b c w) ↔
      PairWitness_d (ω.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) (w.eval ρ) := by
  simp only [pairWitness_m,PairWitness_d,Formula.satisfies_existsMem_iff,naturalPairCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem pairWitness_sound_l (hZF : M.Models ZF) {ω a b c w : M.Domain}
    (h : PairWitness_d ω a b c w) : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,cert⟩ := h
  exact naturalPairCheck_sound_l hZF cert

theorem pairWitness_exists_l (hZF : M.Models ZF) {ω a b c : M.Domain}
    (hω : M.IsOmega ω) (ha : M.mem a ω) (hb : M.mem b ω)
    (pair : Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a b c) : ∃ w, PairWitness_d ω a b c w := by
  obtain ⟨n,X,R,Y,F,p,cert⟩ := naturalPairCheck_exists_l hZF hω ha hb pair
  obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [n,X,R,Y,F,p]
  exact ⟨w,n,hw n (by simp),X,hw X (by simp),R,hw R (by simp),Y,hw Y (by simp),
    F,hw F (by simp),p,hw p (by simp),cert⟩

def FoldRow_d (ω F H s r w : M.Domain) : Prop :=
  ∃ a, M.mem a ω ∧ ∃ b, M.mem b ω ∧ ∃ t, M.mem t s ∧ ∃ d, M.mem d ω ∧
    Rd_entry_d r a F ∧ Rd_entry_d r b H ∧ M.SuccessorOf t r ∧ Rd_entry_d t d H ∧ PairWitness_d ω b a d w

def foldRow_m {d} (ω F H s r w : Term d) : Formula 1 d :=
  Formula.existsMem ω <| Formula.existsMem ω.weaken <| Formula.existsMem s.weaken.weaken <|
    Formula.existsMem ω.weaken.weaken.weaken <|
      .conj (rd_entry0_m r.weaken.weaken.weaken.weaken (.bound 3) F.weaken.weaken.weaken.weaken) <|
        .conj (rd_entry0_m r.weaken.weaken.weaken.weaken (.bound 2) H.weaken.weaken.weaken.weaken) <|
          .conj (KP.succ0_m (.bound 1) r.weaken.weaken.weaken.weaken) <|
            .conj (rd_entry0_m (.bound 1) .newest H.weaken.weaken.weaken.weaken)
              (pairWitness_m ω.weaken.weaken.weaken.weaken (.bound 2) (.bound 3) .newest w.weaken.weaken.weaken.weaken)
derive_free_closed foldRow_m

theorem foldRow_delta_l {d} (ω F H s r w : Term d) : (foldRow_m ω F H s r w).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
    (.conj (rd_entry0_delta_l ..) (.conj (KP.succ0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (pairWitness_delta_l ..))))))))

theorem foldRow_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω F H s r w : Term d) :
    Formula.satisfies ρ (foldRow_m ω F H s r w) ↔
      FoldRow_d (ω.eval ρ) (F.eval ρ) (H.eval ρ) (s.eval ρ) (r.eval ρ) (w.eval ρ) := by
  simp only [foldRow_m,FoldRow_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hKP.1,KP.succ0_sat_l hKP.1,pairWitness_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def foldRow_s : BinarySchema 4 := {
  body := foldRow_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
def foldRow_env_l (ω F H s : M.Domain) : Env M 4 :=
  ⟨Fin.cases s (Fin.cases H (Fin.cases F (fun _ => ω))),fun _ => ω⟩

theorem foldRow_schema_sat_l (hKP : M.Models KP) (ω F H s r w : M.Domain) :
    foldRow_s.denote (foldRow_env_l ω F H s) r w ↔ FoldRow_d ω F H s r w := by
  simp only [foldRow_s,BinarySchema.denote,foldRow_sat_l hKP]
  rfl

def FoldCheck_d (ω F n c e s H V : M.Domain) : Prop :=
  M.mem n ω ∧ M.mem s ω ∧ M.SuccessorOf s n ∧ Fn0_d n ω F ∧ Fn0_d s ω H ∧
    Num_d 0 e ∧ Rd_entry_d e e H ∧ Rd_entry_d n c H ∧
      ∀ r, M.mem r n → ∃ w, M.mem w V ∧ FoldRow_d ω F H s r w

def foldCheck_m {d} (ω F n c e s H V : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (.mem s ω) <| .conj (KP.succ0_m s n) <|
    .conj (fn0_m n ω F) <| .conj (fn0_m s ω H) <| .conj (pc_num_m 0 e) <|
      .conj (rd_entry0_m e e H) <| .conj (rd_entry0_m n c H) <|
        Formula.forallMem n <| Formula.existsMem V.weaken <|
          foldRow_m ω.weaken.weaken F.weaken.weaken H.weaken.weaken s.weaken.weaken (.bound 1) .newest
derive_free_closed foldCheck_m

theorem foldCheck_delta_l {d} (ω F n c e s H V : Term d) : (foldCheck_m ω F n c e s H V).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (KP.succ0_delta_l ..) (.conj (fn0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (pc_num_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.forallMem _ (.existsMem _ (foldRow_delta_l ..))))))))))

theorem foldCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω F n c e s H V : Term d) :
    Formula.satisfies ρ (foldCheck_m ω F n c e s H V) ↔
      FoldCheck_d (ω.eval ρ) (F.eval ρ) (n.eval ρ) (c.eval ρ) (e.eval ρ) (s.eval ρ) (H.eval ρ) (V.eval ρ) := by
  simp only [foldCheck_m,FoldCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    KP.succ0_sat_l hKP.1,fn0_sat_l hKP.1,pc_num_sat_l hKP.1,rd_entry0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,foldRow_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem FoldCheck_d.run_l (hZF : M.Models ZF) {ω F n c e s H V : M.Domain}
    (cert : FoldCheck_d ω F n c e s H V) : FoldRun_d (kp_pair_l (ZF.modelsKP hZF)) ω F n c e s H := by
  obtain ⟨hn,hsω,hs,fn,fh,zero,initial,final,rows⟩ := cert
  refine ⟨hn,hsω,hs,fn,fh,zero,initial,final,fun r hr => ?_⟩
  obtain ⟨w,_,a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,pair⟩ := rows r hr
  exact ⟨a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,pairWitness_sound_l hZF pair⟩

theorem foldCheck_sound_l (hZF : M.Models ZF) {ω F n c e s H V : M.Domain}
    (hω : M.IsOmega ω) (cert : FoldCheck_d ω F n c e s H V) :
    Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n c := (cert.run_l hZF).sound_l hZF hω

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
