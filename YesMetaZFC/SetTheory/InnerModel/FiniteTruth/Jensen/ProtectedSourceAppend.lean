import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateExistsCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateBinder
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateAtomicCompiler

/-! # 原指定谓词槽的同层源编译组合

正确性只维护 i≠a 的普通条目；谓词参数取原 ρ.bound a，量词下取 a.succ。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure PSourceAppend_d (hKP : M.Models KP) {d} (a : Fin d) (v : Fin d → M.Domain) (φ : Formula 1 d)
    (C T ω n F L U G K r : M.Domain) : Prop where
  extension : PProgramExtension_d T ω n F L U G K
  container_mem : M.mem U C
  container_transitive : M.TransitiveSet U
  program_mem : M.mem G C
  length_mem : M.mem K C
  root_bound : M.mem r K
  correct : ∀ (X f : M.Domain) (ρ : Env M d), M.TransitiveSet X →
    M.IsSetFunctionFromTo (kp_pair_l hKP) f n X → (∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) →
      (PFiniteTruth_d true U (ρ.bound a) ω n X G K r f ↔ Formula.satisfies ρ φ)

theorem PSourceAppend_d.congr_l {hKP : M.Models KP} {d a} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : PSourceAppend_d hKP a v φ C T ω n F L U G K r)
    (same : ∀ ρ : Env M d, Formula.satisfies ρ φ ↔ Formula.satisfies ρ ψ) :
    PSourceAppend_d hKP a v ψ C T ω n F L U G K r :=
  ⟨compiled.extension,compiled.container_mem,compiled.container_transitive,compiled.program_mem,compiled.length_mem,
    compiled.root_bound,fun X f ρ hx fn corr => (compiled.correct X f ρ hx fn corr).trans (same ρ)⟩

theorem PSourceAppend_d.stay_l {hKP : M.Models KP} {d a} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : PSourceAppend_d hKP a v φ C T ω n F L U G K r) :
    PSourceAppend_d hKP a v φ C U ω n G K U G K r :=
  ⟨PProgramExtension_d.refl_l hKP compiled.extension.valid,compiled.container_mem,compiled.container_transitive,
    compiled.program_mem,compiled.length_mem,compiled.root_bound,compiled.correct⟩

theorem PSourceAppend_d.correct_polarity_l (hZF : M.Models ZF) (positive : Bool) {d a}
    {v : Fin d → M.Domain} {φ : Formula 1 d} {C T ω n F L U G K r : M.Domain}
    (compiled : PSourceAppend_d (ZF.modelsKP hZF) a v φ C T ω n F L U G K r)
    (hω : M.IsOmega ω) (X f : M.Domain) (ρ : Env M d) (hx : M.TransitiveSet X)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) :
    PFiniteTruth_d positive U (ρ.bound a) ω n X G K r f ↔ Formula.satisfies ρ (if positive then φ else .neg φ) := by
  cases positive
  · exact (pfiniteTruth_complement_l hZF hω compiled.extension.valid fn).trans
      ((not_congr (compiled.correct X f ρ hx fn corr)).trans (Formula.satisfies_neg_iff ρ φ).symm)
  · exact compiled.correct X f ρ hx fn corr

theorem jh_psourceAtomic_l (hZF : M.Models ZF) (equal : Bool) {d} (a : Fin d) (v : Fin d → M.Domain)
    (i j : Fin d) (hi : i ≠ a) (hj : j ≠ a) {α C T ω n F L : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) (bound : ∀ i, M.mem (v i) n) :
    ∃ U G K, PSourceAppend_d (ZF.modelsKP hZF) a v (atomicRelation_m equal (.bound i) (.bound j))
      C T ω n F L U G K L := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,_,program⟩ :=
    jh_patomicAppend_l hZF equal hα hC hω hωC hTC hFC valid (bound i) (bound j)
  refine ⟨U,G,K,program.extension_l valid sub,hUC,hu,hGC,hKC,program.length.predecessor_mem,fun X f ρ _ fn corr => ?_⟩
  exact (patomicAppend_eval_l hZF true equal hω program fn (corr i hi) (corr j hj)).trans
    (atomicRelation_sat_l hZF.1 equal ρ (.bound i) (.bound j)).symm

theorem jh_psourcePredicate_l (hZF : M.Models ZF) {d} (a : Fin d) (v : Fin d → M.Domain)
    (i : Fin d) (hi : i ≠ a) {α C T ω n F L : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hTC : M.mem T C) (hFC : M.mem F C) (valid : PBoundedFormula_d T ω n L F) (bound : ∀ i, M.mem (v i) n) :
    ∃ U G K, PSourceAppend_d (ZF.modelsKP hZF) a v (.mem (.bound i) (.bound a)) C T ω n F L U G K L := by
  obtain ⟨U,G,K,c,z,hUC,hu,sub,hGC,hKC,_,_,program⟩ :=
    jh_predicateAppend_l hZF hα hC hω hωC hTC hFC valid (bound i)
  refine ⟨U,G,K,program.extension_l valid sub,hUC,hu,hGC,hKC,program.length.predecessor_mem,fun X f ρ _ fn corr => ?_⟩
  exact (predicateAppend_eval_l hZF true hω program fn (corr i hi)).trans
    (Formula.satisfies_mem_iff ρ (.bound i) (.bound a)).symm

theorem jh_psourceTruth_l (hZF : M.Models ZF) {d} (a : Fin d) (v : Fin d → M.Domain)
    {α C T ω n F L dummy : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hFC : M.mem F C)
    (valid : PBoundedFormula_d T ω n L F) (hdummy : M.mem dummy n) :
    ∃ U G K, PSourceAppend_d (ZF.modelsKP hZF) a v .truth C T ω n F L U G K L := by
  obtain ⟨U,G,K,c,hUC,hu,sub,hGC,hKC,_,program⟩ :=
    jh_patomicAppend_l hZF true hα hC hω hωC hTC hFC valid hdummy hdummy
  refine ⟨U,G,K,program.extension_l valid sub,hUC,hu,hGC,hKC,program.length.predecessor_mem,fun X f ρ _ fn _ => ?_⟩
  obtain ⟨x,read⟩ := (fn.2.1 dummy).mp hdummy
  have result := patomicAppend_eval_l hZF true true (A := ρ.bound a) hω program fn read read
  simpa only [AtomicAnswer_d,AtomicRelation_d,↓reduceIte,Formula.satisfies_truth_iff,eq_self_iff_true] using result

theorem jh_psourceNor_l (hZF : M.Models ZF) {d a} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {α C T ω n F L U G K r V H J s : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (left : PSourceAppend_d (ZF.modelsKP hZF) a v φ C T ω n F L U G K r)
    (right : PSourceAppend_d (ZF.modelsKP hZF) a v ψ C U ω n G K V H J s) :
    ∃ W N O, PSourceAppend_d (ZF.modelsKP hZF) a v (norAnswer_m true φ ψ) C T ω n F L W N O J := by
  obtain ⟨W,N,O,c,hWC,hw,sub,hNC,hOC,_,program,correct⟩ := jh_pnorAppend_compile_l hZF hα hC hω hωC
    right.container_mem right.program_mem right.extension.valid (right.extension.lengths r left.root_bound) right.root_bound
  refine ⟨W,N,O,(left.extension.trans_l (ZF.modelsKP hZF) right.extension).trans_l (ZF.modelsKP hZF)
    (program.extension_l right.extension.valid sub),hWC,hw,hNC,hOC,program.length.predecessor_mem,fun X f ρ hx fn corr => ?_⟩
  have oldLeft := (right.extension.query_l hZF true hω left.root_bound).symm.trans (left.correct X f ρ hx fn corr)
  exact (correct (ρ.bound a) true X f fn).trans
    ((norAnswer_congr_l true oldLeft (right.correct X f ρ hx fn corr)).trans (norAnswer_sat_l true ρ φ ψ).symm)

theorem jh_psourceNeg_l (hZF : M.Models ZF) {d a} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {α C T ω n F L U G K r : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (compiled : PSourceAppend_d (ZF.modelsKP hZF) a v φ C T ω n F L U G K r) :
    ∃ W N O s, PSourceAppend_d (ZF.modelsKP hZF) a v (.neg φ) C T ω n F L W N O s := by
  obtain ⟨W,N,O,result⟩ := jh_psourceNor_l hZF hα hC hω hωC compiled compiled.stay_l
  refine ⟨W,N,O,K,result.congr_l ?_⟩
  intro ρ
  simp only [norAnswer_m,↓reduceIte,Formula.satisfies_neg_iff,Formula.satisfies_disj_iff,or_self]

theorem jh_psourceFalsum_l (hZF : M.Models ZF) {d} (a : Fin d) (v : Fin d → M.Domain)
    {α C T ω n F L dummy : M.Domain} (hα : M.IsOrdinal α) (hC : Jh_value_d α C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C) (hFC : M.mem F C)
    (valid : PBoundedFormula_d T ω n L F) (hdummy : M.mem dummy n) :
    ∃ U G K r, PSourceAppend_d (ZF.modelsKP hZF) a v .falsum C T ω n F L U G K r := by
  obtain ⟨U,G,K,truth⟩ := jh_psourceTruth_l hZF a v hα hC hω hωC hTC hFC valid hdummy
  obtain ⟨W,N,O,r,result⟩ := jh_psourceNeg_l hZF hα hC hω hωC truth
  refine ⟨W,N,O,r,result.congr_l ?_⟩
  intro ρ
  simp only [Formula.satisfies_neg_iff,Formula.satisfies_truth_iff,Formula.satisfies_falsum_iff,not_true_eq_false]

theorem jh_psourceExists_l (hZF : M.Models ZF) {d} (a q : Fin d) (different : q ≠ a)
    {v : Fin d → M.Domain} {φ : Formula 1 (d+1)} {α C T ω n F L V H J k fresh : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (body : PSourceAppend_d (ZF.modelsKP hZF) a.succ (Fin.cases fresh v) φ C T ω n F L V H J k)
    (freshBound : M.mem fresh n) (setBound : M.mem (v q) n) (unused : ∀ i, v i ≠ fresh) :
    ∃ W N O, PSourceAppend_d (ZF.modelsKP hZF) a v (Formula.existsMem (.bound q) φ) C T ω n F L W N O J := by
  obtain ⟨W,N,O,c,hWC,hw,sub,hNC,hOC,_,program⟩ := jh_pexistsAppend_l hZF hα hC hω hωC
    body.container_mem body.program_mem body.extension.valid freshBound setBound body.root_bound
  refine ⟨W,N,O,body.extension.trans_l (ZF.modelsKP hZF) (program.extension_l body.extension.valid sub),
    hWC,hw,hNC,hOC,program.length.predecessor_mem,fun X f ρ hx fn corr => ?_⟩
  exact sourcePredicateExists_compile_l hZF true v ρ φ a q different hω hx program unused fn corr
    (fun x g _ hg newCorr => (pfiniteTruth_container_l (ZF.modelsKP hZF) true body.extension.valid sub).symm.trans
      (body.correct X g (ρ.push x) hx hg newCorr))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
