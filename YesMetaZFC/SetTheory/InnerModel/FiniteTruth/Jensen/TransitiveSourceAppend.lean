import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.SourceAppend
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ExistsCompiler

/-! # 传递求值域上的完整源编译接口

布尔结果可直接提升。量词组合显式携带传递域前提；旧的任意域布尔接口
保持原规格。所有源寄存器与赋值仍通过实际条目对应连接。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure TransSourceAppend_d (hKP : M.Models KP) {d} (v : Fin d → M.Domain) (φ : Formula 1 d)
    (C T ω n F L U G K r : M.Domain) : Prop where
  extension : ProgramExtension_d T ω n F L U G K
  container_mem : M.mem U C
  container_transitive : M.TransitiveSet U
  program_mem : M.mem G C
  length_mem : M.mem K C
  root_bound : M.mem r K
  correct : ∀ (X f : M.Domain) (ρ : Env M d), M.TransitiveSet X →
    M.IsSetFunctionFromTo (kp_pair_l hKP) f n X → (∀ i, Rd_entry_d (v i) (ρ.bound i) f) →
      (FiniteTruth_d true U ω n X G K r f ↔ Formula.satisfies ρ φ)

theorem SourceAppend_d.transitive_l {hKP : M.Models KP} {d} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : SourceAppend_d hKP v φ C T ω n F L U G K r) :
    TransSourceAppend_d hKP v φ C T ω n F L U G K r :=
  ⟨compiled.extension,compiled.container_mem,compiled.container_transitive,compiled.program_mem,compiled.length_mem,
    compiled.root_bound,fun X f ρ _ hf corr => compiled.correct X f ρ hf corr⟩

theorem TransSourceAppend_d.congr_l {hKP : M.Models KP} {d} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : TransSourceAppend_d hKP v φ C T ω n F L U G K r)
    (same : ∀ ρ : Env M d, Formula.satisfies ρ φ ↔ Formula.satisfies ρ ψ) :
    TransSourceAppend_d hKP v ψ C T ω n F L U G K r :=
  ⟨compiled.extension,compiled.container_mem,compiled.container_transitive,compiled.program_mem,compiled.length_mem,
    compiled.root_bound,fun X f ρ hx hf corr => (compiled.correct X f ρ hx hf corr).trans (same ρ)⟩

theorem TransSourceAppend_d.stay_l {hKP : M.Models KP} {d} {v : Fin d → M.Domain} {φ : Formula 1 d}
    {C T ω n F L U G K r : M.Domain} (compiled : TransSourceAppend_d hKP v φ C T ω n F L U G K r) :
    TransSourceAppend_d hKP v φ C U ω n G K U G K r :=
  ⟨ProgramExtension_d.refl_l hKP compiled.extension.valid,compiled.container_mem,compiled.container_transitive,
    compiled.program_mem,compiled.length_mem,compiled.root_bound,compiled.correct⟩

theorem TransSourceAppend_d.correct_polarity_l (hZF : M.Models ZF) (positive : Bool) {d}
    {v : Fin d → M.Domain} {φ : Formula 1 d} {C T ω n F L U G K r : M.Domain}
    (compiled : TransSourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r)
    (hω : M.IsOmega ω) (X f : M.Domain) (ρ : Env M d) (hx : M.TransitiveSet X)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) (corr : ∀ i, Rd_entry_d (v i) (ρ.bound i) f) :
    FiniteTruth_d positive U ω n X G K r f ↔ Formula.satisfies ρ (if positive then φ else .neg φ) := by
  cases positive
  · exact (finiteTruth_complement_l hZF hω compiled.extension.valid hf).trans
      ((not_congr (compiled.correct X f ρ hx hf corr)).trans (Formula.satisfies_neg_iff ρ φ).symm)
  · exact compiled.correct X f ρ hx hf corr

theorem jh_transNorAppend_l (hZF : M.Models ZF) {d} {v : Fin d → M.Domain} {φ ψ : Formula 1 d}
    {a C T ω n F L U G K r V H J s : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (left : TransSourceAppend_d (ZF.modelsKP hZF) v φ C T ω n F L U G K r)
    (right : TransSourceAppend_d (ZF.modelsKP hZF) v ψ C U ω n G K V H J s) :
    ∃ W N O, TransSourceAppend_d (ZF.modelsKP hZF) v (norAnswer_m true φ ψ) C T ω n F L W N O J := by
  obtain ⟨W,N,O,c,hWC,hw,sub,hNC,hOC,_,program,correct⟩ := jh_norAppend_compile_l hZF ha h hω hωC
    right.container_mem right.program_mem right.extension.valid
    (right.extension.lengths r left.root_bound) right.root_bound
  refine ⟨W,N,O,(left.extension.trans_l (ZF.modelsKP hZF) right.extension).trans_l (ZF.modelsKP hZF)
    (program.extension_l right.extension.valid sub),hWC,hw,hNC,hOC,program.length.predecessor_mem,fun X f ρ hx hf corr => ?_⟩
  have l := (right.extension.query_l hZF true hω left.root_bound).symm.trans (left.correct X f ρ hx hf corr)
  exact (correct true X f hf).trans ((norAnswer_congr_l true l (right.correct X f ρ hx hf corr)).trans
    (norAnswer_sat_l true ρ φ ψ).symm)

theorem jh_transExistsAppend_l (hZF : M.Models ZF) {d} {v : Fin d → M.Domain} {φ : Formula 1 (d+1)} (q : Fin d)
    {a C T ω n F L V H J k fresh : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (body : TransSourceAppend_d (ZF.modelsKP hZF) (Fin.cases fresh v) φ C T ω n F L V H J k)
    (freshBound : M.mem fresh n) (setBound : M.mem (v q) n) (unused : ∀ i, v i ≠ fresh) :
    ∃ W N O, TransSourceAppend_d (ZF.modelsKP hZF) v (Formula.existsMem (.bound q) φ) C T ω n F L W N O J := by
  obtain ⟨W,N,O,c,hWC,hw,sub,hNC,hOC,_,program⟩ := jh_existsAppend_l hZF ha h hω hωC
    body.container_mem body.program_mem body.extension.valid freshBound setBound body.root_bound
  refine ⟨W,N,O,body.extension.trans_l (ZF.modelsKP hZF) (program.extension_l body.extension.valid sub),
    hWC,hw,hNC,hOC,program.length.predecessor_mem,fun X f ρ hx hf corr => ?_⟩
  exact sourceExistsAppend_compile_l hZF true v ρ φ q hω hx program unused hf corr
    (fun x g _ hg newCorr => (finiteTruth_container_l (ZF.modelsKP hZF) true body.extension.valid sub).symm.trans
      (body.correct X g (ρ.push x) hx hg newCorr))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
