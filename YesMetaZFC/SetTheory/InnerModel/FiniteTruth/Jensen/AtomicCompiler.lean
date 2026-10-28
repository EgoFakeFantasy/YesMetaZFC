import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AtomicCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruth

/-! # 原 Jensen 层中的实际原子叶代码生成

从空内部程序出发，用同层数码、rud 三元组和配对生成真实指令，再追加实际
函数图。变量编号由模型内 n 界住；不以宿主 Nat 代替模型内变量域。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 隶属或相等原子叶的完整程序、根及代码都在原同一 J 层内。 -/
theorem jh_atomicProgram_l (hZF : M.Models ZF) (equal : Bool) {a C ω n i j : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hn : M.mem n ω) (hi : M.mem i n) (hj : M.mem j n) :
    ∃ T F L r c, M.mem T C ∧ M.TransitiveSet T ∧ M.mem F C ∧ M.mem L C ∧ M.mem r C ∧ M.mem c C ∧
      AtomicProgram_d equal T ω n F L r c i j := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  have hc := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have nC := hc ω hωC n hn
  obtain ⟨r,hr,hrω⟩ := hω.1.1
  have hrC := hc ω hωC r hrω
  obtain ⟨T,c,hTC,ht,_,hcT,hiT,hjT,hrT,hop⟩ := bop_in_rud_l hKP hC hc
    (jh_local_enclosure_l (ZF.models_kpi_l hZF) ha h) hω hωC hωC
    (hc n nC i hi) (hc n nC j hj) hrC (atomicTag equal)
  have hcC := hc T hTC c hcT
  obtain ⟨L,hLr,hLω⟩ := hω.1.2 r hrω
  have hLC := hc ω hωC L hLω
  have empty : BoundedFormula_d T ω n r r := boundedFormula_empty_l hn hrω hr
  have node : Bnode_d T ω n r c := by
    cases equal
    · exact Or.inl ⟨i,hiT,j,hjT,r,hrT,hop,hi,hj,hrω⟩
    · exact Or.inr (Or.inl ⟨i,hiT,j,hjT,r,hrT,hop,hi,hj,hrω⟩)
  obtain ⟨F,hFC,snoc⟩ := rd_snoc_exists_l hKP hC hrC hrC hcC
  have hLO := KP.successor_isOrdinal hKP empty.ordinal hLr
  have valid := empty.snoc_l hKP hcT node hLω hLO hLr snoc
  obtain ⟨_,entries⟩ := (snoc_iff_entries_l I (fn0_function_l hKP empty.graph).1.1).mp snoc
  have root := (entries r c).mpr (Or.inr ⟨rfl,rfl⟩)
  exact ⟨T,F,L,r,c,hTC,ht,hFC,hLC,hrC,hcC,valid,root,hop,hiT,hjT,hrT,hr,hLr⟩

/-- 给定原变量到模型寄存器的界内映射，实际生成两个原子叶并保留全部赋值语义。 -/
theorem jh_sourceAtomic_compile_l (hZF : M.Models ZF) (equal : Bool) {a C ω n : M.Domain} {d}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hn : M.mem n ω) (v : Fin d → M.Domain) (hv : ∀ i, M.mem (v i) n) (p q : Fin d) :
    ∃ T F L r c, M.mem T C ∧ M.TransitiveSet T ∧ M.mem F C ∧ M.mem L C ∧ M.mem r C ∧ M.mem c C ∧
      AtomicProgram_d equal T ω n F L r c (v p) (v q) ∧
        ∀ (positive : Bool) (X f : M.Domain) (ρ : Env M d),
          M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X →
          (∀ i, Rd_entry_d (v i) (ρ.bound i) f) →
          (FiniteTruth_d positive T ω n X F L r f ↔
            Formula.satisfies ρ (atomicAnswer_m positive equal (.bound p) (.bound q))) := by
  obtain ⟨T,F,L,r,c,hTC,ht,hFC,hLC,hrC,hcC,program⟩ := jh_atomicProgram_l hZF equal ha h hω hωC hn (hv p) (hv q)
  exact ⟨T,F,L,r,c,hTC,ht,hFC,hLC,hrC,hcC,program,
    fun positive X f ρ hf corresponds => sourceAtomic_compile_l hZF positive equal v ρ p q hω program hf corresponds⟩

private def jensenAtomicProgramBody (equal : Bool) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 5)) <| .imp (jh_value_m (.bound 5) (.bound 4)) <|
      .imp (Formula.isOmega (.bound 3)) <| .imp (.mem (.bound 3) (.bound 4)) <|
        .imp (.mem (.bound 2) (.bound 3)) <| .imp (.mem (.bound 1) (.bound 2)) <|
          .imp (.mem .newest (.bound 2)) <| .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
            .conj (.mem (.bound 4) (.bound 9)) <| .conj (Formula.isTransitive (.bound 4)) <|
              .conj (.mem (.bound 3) (.bound 9)) <| .conj (.mem (.bound 2) (.bound 9)) <|
                .conj (.mem (.bound 1) (.bound 9)) <| .conj (.mem .newest (.bound 9))
                  (atomicProgram_m equal (.bound 4) (.bound 8) (.bound 7) (.bound 3) (.bound 2) (.bound 1) .newest (.bound 6) (.bound 5))

def jensenAtomicProgram (equal : Bool) : Sentence := .ofFormula (jensenAtomicProgramBody equal)
  (by simp -implicitDefEqProofs [jensenAtomicProgramBody,Definitional.Formula.FreeClosed])

theorem jensenAtomicProgram_models (equal : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenAtomicProgram equal) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (jensenAtomicProgramBody equal)
  simp only [jensenAtomicProgramBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_isTransitive_iff,atomicProgram_sat_l (ZF.modelsKP hZF)]
  exact fun a C ω n i j ha h hω hωC hn hi hj => jh_atomicProgram_l hZF equal ha h hω hωC hn hi hj

theorem jensenAtomicProgram_derives (equal : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenAtomicProgram equal) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenAtomicProgram_models equal M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
