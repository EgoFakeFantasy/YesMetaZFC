import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NaturalPairExistence

/-! # 原规范自然数配对的实际 Σ₁ 图

参数槽为 b、ω；输入 a，输出 c。唯一见证集合有界装配完整六对象证书。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def naturalPair_s : S1_binary 2 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <|
        Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
          naturalPairCheck_m (.bound 10) (.bound 8) (.bound 9) (.bound 7)
            (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (naturalPairCheck_delta_l ..)))))) }

theorem naturalPair_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 2) (a c w : M.Domain) :
    Formula.satisfies (((ρ.push a).push c).push w) naturalPair_s.matrix.body ↔
      ∃ n, M.mem n w ∧ ∃ X, M.mem X w ∧ ∃ R, M.mem R w ∧ ∃ Y, M.mem Y w ∧
        ∃ F, M.mem F w ∧ ∃ p, M.mem p w ∧ NaturalPairCheck_d (ρ.bound 1) a (ρ.bound 0) c n X R Y F p := by
  simp only [naturalPair_s,Formula.satisfies_existsMem_iff,naturalPairCheck_sat_l hKP]
  rfl

theorem naturalPair_sat_l (hZF : M.Models ZF) (ρ : Env M 2) (a c : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (ha : M.mem a (ρ.bound 1)) (hb : M.mem (ρ.bound 0) (ρ.bound 1)) :
    naturalPair_s.schema.denote ρ a c ↔ Oc_pair_d (kp_pair_l (ZF.modelsKP hZF)) a (ρ.bound 0) c := by
  rw [S1_binary.sat_l]
  simp only [naturalPair_matrix_sat_l (ZF.modelsKP hZF)]
  constructor
  · rintro ⟨w,n,_,X,_,R,_,Y,_,F,_,p,_,cert⟩
    exact naturalPairCheck_sound_l hZF cert
  · intro pair
    obtain ⟨n,X,R,Y,F,p,cert⟩ := naturalPairCheck_exists_l hZF hω ha hb pair
    obtain ⟨w,hw⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [n,X,R,Y,F,p]
    exact ⟨w,n,hw n (by simp),X,hw X (by simp),R,hw R (by simp),Y,hw Y (by simp),
      F,hw F (by simp),p,hw p (by simp),cert⟩

/-- 图本身核验三个数值的内部自然数类型。 -/
theorem naturalPair_types_l (hZF : M.Models ZF) (ρ : Env M 2) {a c : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (graph : naturalPair_s.schema.denote ρ a c) :
    M.mem a (ρ.bound 1) ∧ M.mem (ρ.bound 0) (ρ.bound 1) ∧ M.mem c (ρ.bound 1) := by
  rw [S1_binary.sat_l] at graph
  obtain ⟨w,hw⟩ := graph
  obtain ⟨n,_,X,_,R,_,Y,_,F,_,p,_,cert⟩ := (naturalPair_matrix_sat_l (ZF.modelsKP hZF) ρ a c w).mp hw
  obtain ⟨hn,ha,hb,hy,_,_,_,_,collapse,entry⟩ := cert
  exact ⟨hω.transitive hZF n hn a ha,hω.transitive hZF n hn (ρ.bound 0) hb,
    hω.transitive hZF Y hy c (collapse.1.bound_l entry).2⟩

theorem naturalPair_total_l (hZF : M.Models ZF) (ρ : Env M 2) (a : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (ha : M.mem a (ρ.bound 1)) (hb : M.mem (ρ.bound 0) (ρ.bound 1)) :
    ∃ c, M.mem c (ρ.bound 1) ∧ naturalPair_s.schema.denote ρ a c := by
  obtain ⟨c,pair⟩ := oc_pair_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (hω.members_areOrdinals hZF a ha) (hω.members_areOrdinals hZF (ρ.bound 0) hb)
  exact ⟨c,oc_pair_natural_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω ha hb pair,
    (naturalPair_sat_l hZF ρ a c hω ha hb).mpr pair⟩

theorem naturalPair_unique_l (hZF : M.Models ZF) (ρ : Env M 2) {a c d : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hc : naturalPair_s.schema.denote ρ a c)
    (hd : naturalPair_s.schema.denote ρ a d) : c = d := by
  have types := naturalPair_types_l hZF ρ hω hc
  exact oc_pair_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    ((naturalPair_sat_l hZF ρ a c hω types.1 types.2.1).mp hc)
    ((naturalPair_sat_l hZF ρ a d hω types.1 types.2.1).mp hd)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
