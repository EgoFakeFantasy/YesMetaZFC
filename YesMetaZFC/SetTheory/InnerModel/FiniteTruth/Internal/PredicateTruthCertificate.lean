import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthHistory

/-! # 全部内部行的实际有界谓词历史核验 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PtruthCheck_d (T A n X E F length Z H : M.Domain) : Prop :=
  Fn0_d length Z H ∧ ∀ r, M.mem r length → ∀ c, M.mem c T → Rd_entry_d r c F →
    ∀ Y, M.mem Y Z → Rd_entry_d r Y H → M.MemberSubset Y E ∧
      ∀ f, M.mem f E → (M.mem f Y ↔ PtruthNode_d T A n X E H c f)

def ptruthCheck_m {d} (T A n X E F length Z H : Term d) : Formula 1 d :=
  .conj (fn0_m length Z H) <| Formula.forallMem length <| Formula.forallMem T.weaken <|
    .imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken) <| Formula.forallMem Z.weaken.weaken <|
      .imp (rd_entry0_m (.bound 2) .newest H.weaken.weaken.weaken) <|
        .conj (Formula.subset .newest E.weaken.weaken.weaken) <| Formula.forallMem E.weaken.weaken.weaken <|
          .iff (.mem .newest (.bound 1))
            (ptruthNode_m T.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
              n.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken
              H.weaken.weaken.weaken.weaken (.bound 2) .newest)

@[simp] theorem ptruthCheck_closed_l {d} (T A n X E F length Z H : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hl : length.freeSupport = [])
    (hZ : Z.freeSupport = []) (hH : H.freeSupport = []) : (ptruthCheck_m T A n X E F length Z H).FreeClosed := by
  simp -implicitDefEqProofs [ptruthCheck_m,Definitional.Formula.FreeClosed,hT,hA,hn,hX,hE,hF,hl,hZ,hH]

theorem ptruthCheck_delta_l {d} (T A n X E F length Z H : Term d) : (ptruthCheck_m T A n X E F length Z H).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.forallMem _ (.imp (rd_entry0_delta_l ..) (.conj (.atom _ _ _)
      (.forallMem _ (.iff (.mem _ _) (ptruthNode_delta_l ..)))))))))

theorem ptruthCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A n X E F length Z H : Term d) :
    Formula.satisfies ρ (ptruthCheck_m T A n X E F length Z H) ↔
      PtruthCheck_d (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ)
        (F.eval ρ) (length.eval ρ) (Z.eval ρ) (H.eval ρ) := by
  simp only [ptruthCheck_m,PtruthCheck_d,Formula.satisfies_conj_iff,fn0_sat_l hE,
    Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,ptruthNode_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem ptruthCheck_of_eval_l (hKP : M.Models KP) {T A ω n X E F length Z H : M.Domain}
    (valid : PBoundedFormula_d T ω n length F)
    (history : PtruthEval_d (kp_pair_l hKP) T A n X E F length H) (fn : Fn0_d length Z H) :
    PtruthCheck_d T A n X E F length Z H := by
  refine ⟨fn,fun r hr c hc code Y _ value => ⟨ptruthEval_range_l hKP history value,?_⟩⟩
  have row := ptruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 history code value (valid.row r hr c hc code)
  exact fun f hf => (row f).trans (and_iff_right hf)

theorem ptruthEval_of_check_l (hZF : M.Models ZF) {T A ω n X E F length Z H : M.Domain}
    (valid : PBoundedFormula_d T ω n length F) (check : PtruthCheck_d T A n X E F length Z H) :
    PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F length H := by
  let hKP := ZF.modelsKP hZF
  have fn := fn0_function_l hKP check.1
  have seq : M.IsSequenceOfLength (kp_pair_l hKP) H length := ⟨valid.ordinal,fn.1,fn.2.1⟩
  refine ⟨seq,fun r hr Y value => ?_⟩
  obtain ⟨c,hc,code⟩ := valid.graph.2.1 r hr
  obtain ⟨P,pref⟩ := ZF.exists_restriction hZF (kp_pair_l hKP) H r
  have domain := (seq.restriction hr pref).2.2
  obtain ⟨bound,row⟩ := check.2 r hr c hc code Y (check.1.bound_l value).2 value
  have atRow (f : M.Domain) : PtruthAt_d T A n X E F P f ↔ PtruthNode_d T A n X E P c f := by
    constructor
    · rintro ⟨k,d,hk,entry,node⟩
      have eq := (show M.IsDomainOf (kp_pair_l hKP) k P from hk).eq hZF.1 domain
      subst k
      have eq := (fn0_function_l hKP valid.graph).1.2 r d c entry code
      subst d
      exact node
    · exact fun node => ⟨r,c,domain,code,node⟩
  refine ⟨P,pref,fun f => ?_⟩
  have step : M.mem f Y ↔ M.mem f E ∧ PtruthNode_d T A n X E H c f :=
    ⟨fun hf => ⟨bound f hf,(row f (bound f hf)).mp hf⟩,fun ⟨hf,node⟩ => (row f hf).mpr node⟩
  exact step.trans (and_congr_right fun _ =>
    (ptruthNode_restriction_l hKP pref (valid.row r hr c hc code)).symm.trans (atRow f).symm)

theorem ptruthCheck_correct_l (hZF : M.Models ZF) {T A ω n X E F length Z H : M.Domain}
    (valid : PBoundedFormula_d T ω n length F) :
    PtruthCheck_d T A n X E F length Z H ↔ Fn0_d length Z H ∧
      PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F length H :=
  ⟨fun check => ⟨check.1,ptruthEval_of_check_l hZF valid check⟩,
    fun ⟨fn,history⟩ => ptruthCheck_of_eval_l (ZF.modelsKP hZF) valid history fn⟩

theorem ptruthCertificate_exists_l (hZF : M.Models ZF) {T A ω n X E F length : M.Domain}
    (valid : PBoundedFormula_d T ω n length F) : ∃ Z H, PtruthCheck_d T A n X E F length Z H := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨H,history⟩ := ptruthEval_exists_l hZF T A n X E F valid.ordinal
  obtain ⟨Z,range⟩ := rd_fun_exists_l hKP .range H H H
  have fn : Fn0_d length Z H := fn0_of_function_l hKP ⟨history.1.2.1,history.1.2.2,fun r hr => by
    obtain ⟨Y,value⟩ := (history.1.2.2 r).mp hr
    exact ⟨Y,(range Y).mpr ⟨r,value⟩,value⟩⟩
  exact ⟨Z,H,ptruthCheck_of_eval_l hKP valid history fn⟩

theorem ptruthCertificate_unique_l (hZF : M.Models ZF) {T A ω n X E F length Z H W J : M.Domain}
    (valid : PBoundedFormula_d T ω n length F)
    (first : PtruthCheck_d T A n X E F length Z H) (second : PtruthCheck_d T A n X E F length W J) : H = J :=
  ptruthEval_unique_l hZF (ptruthEval_of_check_l hZF valid first) (ptruthEval_of_check_l hZF valid second)

theorem ptruthCheck_trace_l {T A B n X E F length Z H : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PtruthCheck_d T A n X E F length Z H ↔ PtruthCheck_d T B n X E F length Z H := by
  simp only [PtruthCheck_d,ptruthNode_trace_l trace]

theorem ptruthCheck_legacy_l (hKP : M.Models KP) {T A ω n X E F length Z H : M.Domain}
    (valid : BoundedFormula_d T ω n length F) :
    PtruthCheck_d T A n X E F length Z H ↔ BtruthCheck_d T n X E F length Z H := by
  constructor
  · rintro ⟨fn,rows⟩
    refine ⟨fn,fun r hr c hc code Y hYZ value => ?_⟩
    obtain ⟨bound,row⟩ := rows r hr c hc code Y hYZ value
    exact ⟨bound,fun f hf => (row f hf).trans (ptruthNode_legacy_l hKP (valid.row r hr c hc code))⟩
  · rintro ⟨fn,rows⟩
    refine ⟨fn,fun r hr c hc code Y hYZ value => ?_⟩
    obtain ⟨bound,row⟩ := rows r hr c hc code Y hYZ value
    exact ⟨bound,fun f hf => (row f hf).trans (ptruthNode_legacy_l hKP (valid.row r hr c hc code)).symm⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
