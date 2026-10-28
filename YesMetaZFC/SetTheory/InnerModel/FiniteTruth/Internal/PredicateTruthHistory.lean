import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthSyntax

/-! # 统一内部谓词程序的完整背景历史与同一迹历史 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem ptruthStep_exists_l (hZF : M.Models ZF) (T A n X E F H : M.Domain) :
    ∃ Y, PtruthStep_d T A n X E F H Y := by
  let ρ := (ptruth_env_l T A n X E F).push H
  let φ : UnarySchema 7 := {
    body := ptruthAt_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Y,sep⟩ := ZF.separation_exists_d hZF φ ρ E
  exact ⟨Y,fun f => (sep f).trans (and_congr_right fun _ => ptruthAt_sat_l hZF.1 (ρ.push f) _ _ _ _ _ _ _ _)⟩

theorem ptruthStep_unique_l (hE : Extensional M) {T A n X E F H Y Z : M.Domain}
    (first : PtruthStep_d T A n X E F H Y) (second : PtruthStep_d T A n X E F H Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun f => (first f).trans (second f).symm)

theorem ptruth_class_l (hZF : M.Models ZF) (T A n X E F : M.Domain) :
    M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF)) (PtruthStep_d T A n X E F) := by
  intro H _
  obtain ⟨Y,step⟩ := ptruthStep_exists_l hZF T A n X E F H
  exact ⟨Y,step,fun Z other => ptruthStep_unique_l hZF.1 other step⟩

theorem ptruthEval_exists_l (hZF : M.Models ZF) (T A n X E F : M.Domain) {length : M.Domain}
    (ordinal : M.IsOrdinal length) :
    ∃ H, PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F length H := by
  have op : ptruth_s.denote (ptruth_env_l T A n X E F) = PtruthStep_d T A n X E F :=
    ptruth_op_l hZF.1 (ptruth_env_l T A n X E F)
  have functional : M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF))
      (ptruth_s.denote (ptruth_env_l T A n X E F)) := by
    rw [op]
    exact ptruth_class_l hZF T A n X E F
  obtain ⟨H,history⟩ := ZF.recursiveSequence_exists hZF (kp_pair_l (ZF.modelsKP hZF))
    (ptruth_env_l T A n X E F) ptruth_s functional ordinal
  exact ⟨H,by simpa only [op,PtruthEval_d] using history⟩

theorem ptruthEval_unique_l (hZF : M.Models ZF) {T A n X E F length H J : M.Domain}
    (first : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F length H)
    (second : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F length J) : H = J := by
  have op : ptruth_s.denote (ptruth_env_l T A n X E F) = PtruthStep_d T A n X E F :=
    ptruth_op_l hZF.1 (ptruth_env_l T A n X E F)
  have functional : M.IsClassFunctionOnTransfiniteSequences (kp_pair_l (ZF.modelsKP hZF))
      (ptruth_s.denote (ptruth_env_l T A n X E F)) := by
    rw [op]
    exact ptruth_class_l hZF T A n X E F
  exact ZF.recursiveSequence_unique hZF (kp_pair_l (ZF.modelsKP hZF))
    (ptruth_env_l T A n X E F) ptruth_s functional
    (by simpa only [op,PtruthEval_d] using first) (by simpa only [op,PtruthEval_d] using second)

theorem ptruthEval_unfold_l (hKP : M.Models KP) {T A n X E F length H r c Y : M.Domain}
    (program : M.IsSetFunction (kp_pair_l hKP) F)
    (history : PtruthEval_d (kp_pair_l hKP) T A n X E F length H)
    (code : Rd_entry_d r c F) (value : Rd_entry_d r Y H) :
    ∃ P, M.IsRestrictionOf (kp_pair_l hKP) P H r ∧ Bdomain_d r P ∧
      ∀ f, M.mem f Y ↔ M.mem f E ∧ PtruthNode_d T A n X E P c f := by
  have hr := (history.1.2.2 r).mpr ⟨Y,value⟩
  obtain ⟨P,pref,step⟩ := history.2 r hr Y value
  have domain := (history.restriction hr pref).1.2.2
  refine ⟨P,pref,domain,fun f => (step f).trans (and_congr_right fun _ => ?_)⟩
  constructor
  · rintro ⟨k,d,hk,entry,node⟩
    have eq := (show M.IsDomainOf (kp_pair_l hKP) k P from hk).eq hKP.1 domain
    subst k
    have eq := program.2 r d c entry code
    subst d
    exact node
  · exact fun node => ⟨r,c,domain,code,node⟩

theorem ptruthEval_range_l (hKP : M.Models KP) {T A n X E F length H r Y : M.Domain}
    (history : PtruthEval_d (kp_pair_l hKP) T A n X E F length H) (value : Rd_entry_d r Y H) : M.MemberSubset Y E := by
  have hr := (history.1.2.2 r).mpr ⟨Y,value⟩
  obtain ⟨_,_,step⟩ := history.2 r hr Y value
  exact fun f hf => ((step f).mp hf).1

theorem ptruthEval_row_l (hKP : M.Models KP) {T A ω n X E F length H r c Y : M.Domain}
    (program : M.IsSetFunction (kp_pair_l hKP) F)
    (history : PtruthEval_d (kp_pair_l hKP) T A n X E F length H)
    (code : Rd_entry_d r c F) (value : Rd_entry_d r Y H) (valid : Pnode_d T ω n r c) :
    ∀ f, M.mem f Y ↔ M.mem f E ∧ PtruthNode_d T A n X E H c f := by
  obtain ⟨P,pref,_,step⟩ := ptruthEval_unfold_l hKP program history code value
  exact fun f => (step f).trans (and_congr_right fun _ => ptruthNode_restriction_l hKP pref valid)

theorem ptruthAt_trace_l {T A B n X E F H f : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PtruthAt_d T A n X E F H f ↔ PtruthAt_d T B n X E F H f := by
  simp only [PtruthAt_d,ptruthNode_trace_l trace]

theorem ptruthStep_trace_l {T A B n X E F H Y : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PtruthStep_d T A n X E F H Y ↔ PtruthStep_d T B n X E F H Y := by
  simp only [PtruthStep_d,ptruthAt_trace_l trace]

theorem ptruthEval_trace_l (I : kpair_convention_l.Interpretation M) {T A B n X E F length H : M.Domain}
    (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PtruthEval_d I T A n X E F length H ↔ PtruthEval_d I T B n X E F length H := by
  have op : PtruthStep_d T A n X E F = PtruthStep_d T B n X E F := by
    funext P Y
    exact propext (ptruthStep_trace_l trace)
  unfold PtruthEval_d
  rw [op]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
