import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedCodeContainer
import YesMetaZFC.SetTheory.InnerModel.Computation.Delta0

/-! # 隶属与相等原子叶的内部编译语义

寄存器编号是模型对象，源变量位置是原 AST 的 Fin 索引；明确的条目对应连接
二者。这里仅完成两个原子叶，不声称全部联结与有界量词已经编译。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def atomicTag (equal : Bool) : Nat := if equal then 1 else 0

def AtomicRelation_d (equal : Bool) (a b : M.Domain) : Prop := if equal then a = b else M.mem a b

def atomicRelation_m (equal : Bool) {d} (a b : Term d) : Formula 1 d :=
  if equal then Formula.extensionalEq a b else .mem a b

@[simp] theorem atomicRelation_closed_l (equal : Bool) {d} (a b : Term d)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) : (atomicRelation_m equal a b).FreeClosed := by
  cases equal <;> simp [atomicRelation_m,Definitional.Formula.FreeClosed,ha,hb]

theorem atomicRelation_delta_l (equal : Bool) {d} (a b : Term d) : (atomicRelation_m equal a b).IsDelta0 := by
  cases equal
  · exact .mem _ _
  · exact .atom _ _ _

theorem atomicRelation_sat_l (hE : Extensional M) (equal : Bool) {d} (ρ : Env M d) (a b : Term d) :
    Formula.satisfies ρ (atomicRelation_m equal a b) ↔ AtomicRelation_d equal (a.eval ρ) (b.eval ρ) := by
  cases equal <;> simp only [atomicRelation_m,AtomicRelation_d,Bool.false_eq_true,↓reduceIte,
    Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hE]

def AtomicAnswer_d (positive equal : Bool) (a b : M.Domain) : Prop :=
  if positive then AtomicRelation_d equal a b else ¬ AtomicRelation_d equal a b

def atomicAnswer_m (positive equal : Bool) {d} (a b : Term d) : Formula 1 d :=
  if positive then atomicRelation_m equal a b else .neg (atomicRelation_m equal a b)

@[simp] theorem atomicAnswer_closed_l (positive equal : Bool) {d} (a b : Term d)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) : (atomicAnswer_m positive equal a b).FreeClosed := by
  cases positive <;> simp [atomicAnswer_m,Definitional.Formula.FreeClosed,ha,hb]

theorem atomicAnswer_delta_l (positive equal : Bool) {d} (a b : Term d) : (atomicAnswer_m positive equal a b).IsDelta0 := by
  cases positive
  · exact .neg (atomicRelation_delta_l equal a b)
  · exact atomicRelation_delta_l equal a b

theorem atomicAnswer_sat_l (hE : Extensional M) (positive equal : Bool) {d} (ρ : Env M d) (a b : Term d) :
    Formula.satisfies ρ (atomicAnswer_m positive equal a b) ↔ AtomicAnswer_d positive equal (a.eval ρ) (b.eval ρ) := by
  cases positive <;> simp only [atomicAnswer_m,AtomicAnswer_d,Bool.false_eq_true,↓reduceIte,
    Formula.satisfies_neg_iff,atomicRelation_sat_l hE]

structure AtomicProgram_d (equal : Bool) (T ω n F L r c i j : M.Domain) : Prop where
  valid : BoundedFormula_d T ω n L F
  root : Rd_entry_d r c F
  instruction : Bop_d T (atomicTag equal) c i j r
  left_mem : M.mem i T
  right_mem : M.mem j T
  zero_mem : M.mem r T
  zero : Num_d 0 r
  length : M.SuccessorOf L r

def atomicProgram_m (equal : Bool) {d} (T ω n F L r c i j : Term d) : Formula 1 d :=
  .conj (boundedFormula_m T ω n L F) <| .conj (rd_entry0_m r c F) <|
    .conj (bop_m T (atomicTag equal) c i j r) <| .conj (.mem i T) <| .conj (.mem j T) <|
      .conj (.mem r T) <| .conj (pc_num_m 0 r) (KP.succ0_m L r)
derive_free_closed atomicProgram_m

theorem atomicProgram_delta_l (equal : Bool) {d} (T ω n F L r c i j : Term d) :
    (atomicProgram_m equal T ω n F L r c i j).IsDelta0 :=
  .conj (boundedFormula_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (pc_num_delta_l 0 _) ((KP.succ0_delta_l ..))))))))

theorem atomicProgram_sat_l (hKP : M.Models KP) (equal : Bool) {d} (ρ : Env M d) (T ω n F L r c i j : Term d) :
    Formula.satisfies ρ (atomicProgram_m equal T ω n F L r c i j) ↔
      AtomicProgram_d equal (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (r.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [atomicProgram_m,Formula.satisfies_conj_iff,boundedFormula_sat_l hKP,rd_entry0_sat_l hKP.1,
    bop_sat_l hKP.1,Formula.satisfies_mem_iff,pc_num_sat_l hKP.1,KP.succ0_sat_l hKP.1]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h⟩ => ⟨a,b,c,d,e,f,g,h⟩,
    fun h => ⟨h.valid,h.root,h.instruction,h.left_mem,h.right_mem,h.zero_mem,h.zero,h.length⟩⟩

theorem atomicNode_l (hKP : M.Models KP) (equal : Bool) {T n X E H c i j k f a b : M.Domain}
    (hi : M.mem i T) (hj : M.mem j T) (hk : M.mem k T) (hop : Bop_d T (atomicTag equal) c i j k)
    (hf : M.IsSetFunctionFromTo (kp_pair_l hKP) f n X) (hia : Rd_entry_d i a f) (hjb : Rd_entry_d j b f) :
    BtruthNode_d T n X E H c f ↔ AtomicRelation_d equal a b := by
  cases equal with
  | false =>
    change BtruthNode_d T n X E H c f ↔ M.mem a b
    rw [btruthNode_decode_l hKP ⟨0,by decide⟩ hi hj hk hop]
    constructor
    · rintro ⟨x,_,y,_,hix,hjy,hxy⟩
      have ex := hf.1.2 i x a hix hia
      have ey := hf.1.2 j y b hjy hjb
      subst x
      subst y
      exact hxy
    · exact fun hab => ⟨a,hf.output_mem_of_pairMember hia,b,hf.output_mem_of_pairMember hjb,hia,hjb,hab⟩
  | true =>
    change BtruthNode_d T n X E H c f ↔ a = b
    rw [btruthNode_decode_l hKP ⟨1,by decide⟩ hi hj hk hop]
    constructor
    · rintro ⟨x,_,hix,hjx⟩
      exact (hf.1.2 i x a hix hia).symm.trans (hf.1.2 j x b hjx hjb)
    · intro eq
      subst b
      exact ⟨a,hf.output_mem_of_pairMember hia,hia,hjb⟩

/-- 真实原子指令的正负查询准确对应源隶属或相等，不局限于标准赋值。 -/
theorem atomicProgram_eval_l (hZF : M.Models ZF) (positive equal : Bool)
    {T ω n X F L r c i j f a b : M.Domain} (hω : M.IsOmega ω)
    (program : AtomicProgram_d equal T ω n F L r c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (hia : Rd_entry_d i a f) (hjb : Rd_entry_d j b f) :
    FiniteTruth_d positive T ω n X F L r f ↔ AtomicAnswer_d positive equal a b := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  have hfE := (full f).mpr hf
  obtain ⟨V,H,truth⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) program.valid
  have eval := btruthEval_of_check_l hZF program.valid truth
  obtain ⟨Y,hY⟩ := (eval.1.2.2 r).mp (program.valid.at_l program.root).1
  have row := btruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans (((row f).trans (and_iff_right hfE)).trans
    (atomicNode_l hKP equal program.left_mem program.right_mem program.zero_mem program.instruction hf hia hjb))
  have answer : BtruthAnswer_d positive H r f ↔ AtomicAnswer_d positive equal a b := by
    cases positive <;> simp only [BtruthAnswer_d,AtomicAnswer_d,Bool.false_eq_true,↓reduceIte,hit]
  exact (finiteTruth_space_l hZF positive hω program.valid.variables full).trans
    ((and_congr_right fun _ => (certifiedTruth_value_l hZF positive program.valid truth).trans answer).trans (and_iff_right hfE))

/-- 原 AST 原子叶经过上游解析器保持相同的原子种类与变量索引。 -/
theorem atomic_parse_l (equal : Bool) {d} (p q : Fin d) :
    cp_parse_l (atomicRelation_m equal (.bound p) (.bound q)) =
      some (if equal then Cp_test.eq p q else Cp_test.mem p q) := by
  cases equal <;> rfl

/-- 显式寄存器条目对应把原 Project 原子公式连接到实际内部程序。 -/
theorem sourceAtomic_compile_l (hZF : M.Models ZF) (positive equal : Bool)
    {T ω n X F L r c f : M.Domain} {d} (v : Fin d → M.Domain) (ρ : Env M d) (p q : Fin d)
    (hω : M.IsOmega ω) (program : AtomicProgram_d equal T ω n F L r c (v p) (v q))
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corresponds : ∀ i, Rd_entry_d (v i) (ρ.bound i) f) :
    FiniteTruth_d positive T ω n X F L r f ↔
      Formula.satisfies ρ (atomicAnswer_m positive equal (.bound p) (.bound q)) :=
  (atomicProgram_eval_l hZF positive equal hω program hf (corresponds p) (corresponds q)).trans
    (atomicAnswer_sat_l hZF.1 positive equal ρ (.bound p) (.bound q)).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
