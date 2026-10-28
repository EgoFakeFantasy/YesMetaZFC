import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthPrefix
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFiniteTruthSourceCertificate

/-! # 原谓词原子到只读指令的实际追加编译

查询 A 的参数独立于普通赋值。旧程序可含任意合法的五类内部指令。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PredicateAnswer_d (positive : Bool) (A x : M.Domain) : Prop := if positive then M.mem x A else ¬ M.mem x A

def predicateAnswer_m (positive : Bool) {d} (A x : Term d) : Formula 1 d :=
  if positive then .mem x A else .neg (.mem x A)

@[simp] theorem predicateAnswer_closed_l (positive : Bool) {d} (A x : Term d)
    (hA : A.freeSupport = []) (hx : x.freeSupport = []) : (predicateAnswer_m positive A x).FreeClosed := by
  cases positive <;> simp [predicateAnswer_m,Definitional.Formula.FreeClosed,hA,hx]

theorem predicateAnswer_delta_l (positive : Bool) {d} (A x : Term d) :
    (predicateAnswer_m positive A x).IsDelta0 := by
  cases positive
  · exact .neg (.mem _ _)
  · exact .mem _ _

theorem predicateAnswer_sat_l (positive : Bool) {d} (ρ : Env M d) (A x : Term d) :
    Formula.satisfies ρ (predicateAnswer_m positive A x) ↔ PredicateAnswer_d positive (A.eval ρ) (x.eval ρ) := by
  cases positive <;> simp only [predicateAnswer_m,PredicateAnswer_d,Bool.false_eq_true,↓reduceIte,
    Formula.satisfies_neg_iff,Formula.satisfies_mem_iff]

structure PredicateAppend_d (T ω n F L G K c i z : M.Domain) : Prop where
  old : PBoundedFormula_d T ω n L F
  valid : PBoundedFormula_d T ω n K G
  restriction : Res0_d F G L T
  length : M.SuccessorOf K L
  root : Rd_entry_d L c G
  instruction : Bop_d T 4 c i z z
  input_mem : M.mem i T
  dummy_mem : M.mem z T
  input_bound : M.mem i n
  dummy_bound : M.mem z ω

def predicateAppend_m {d} (T ω n F L G K c i z : Term d) : Formula 1 d :=
  .conj (pboundedFormula_m T ω n L F) <| .conj (pboundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T 4 c i z z) <| .conj (.mem i T) <| .conj (.mem z T) <|
        .conj (.mem i n) (.mem z ω)
derive_free_closed predicateAppend_m

theorem predicateAppend_delta_l {d} (T ω n F L G K c i z : Term d) :
    (predicateAppend_m T ω n F L G K c i z).IsDelta0 :=
  .conj (pboundedFormula_delta_l ..) (.conj (pboundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _)))))))))

theorem predicateAppend_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n F L G K c i z : Term d) :
    Formula.satisfies ρ (predicateAppend_m T ω n F L G K c i z) ↔
      PredicateAppend_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (z.eval ρ) := by
  simp only [predicateAppend_m,Formula.satisfies_conj_iff,pboundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j⟩ => ⟨a,b,c,d,e,f,g,h,i,j⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,h.input_mem,h.dummy_mem,h.input_bound,h.dummy_bound⟩⟩

theorem predicateNode_eval_l (hKP : M.Models KP) {T A n X E H c i j k f x : M.Domain}
    (hi : M.mem i T) (hj : M.mem j T) (hk : M.mem k T) (code : Bop_d T 4 c i j k)
    (fn : M.IsSetFunctionFromTo (kp_pair_l hKP) f n X) (read : Rd_entry_d i x f) :
    PtruthNode_d T A n X E H c f ↔ M.mem x A := by
  rw [ptruthNode_predicate_l hKP hi hj hk code]
  constructor
  · rintro ⟨y,_,other,hit⟩
    exact (fn.1.2 i y x other read) ▸ hit
  · exact fun hit => ⟨x,fn.output_mem_of_pairMember read,read,hit⟩

theorem predicateAppend_eval_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L G K c i z f x : M.Domain} (hω : M.IsOmega ω)
    (program : PredicateAppend_d T ω n F L G K c i z)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) (read : Rd_entry_d i x f) :
    PFiniteTruth_d positive T A ω n X G K L f ↔ PredicateAnswer_d positive A x := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  have hfE := (full f).mpr fn
  obtain ⟨V,H,check⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) program.valid
  have history := ptruthEval_of_check_l hZF program.valid check
  obtain ⟨Y,value⟩ := (history.1.2.2 L).mp program.length.predecessor_mem
  have row := ptruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 history program.root value
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l history.1.2.1.2 value).trans (((row f).trans (and_iff_right hfE)).trans
    (predicateNode_eval_l hKP program.input_mem program.dummy_mem program.dummy_mem program.instruction fn read))
  have answer : BtruthAnswer_d positive H L f ↔ PredicateAnswer_d positive A x := by
    cases positive <;> simp only [BtruthAnswer_d,PredicateAnswer_d,Bool.false_eq_true,↓reduceIte,hit]
  exact (pfiniteTruth_value_l hZF positive hω program.valid full check hfE).trans answer

/-- 指定谓词槽不须有赋值条目；只读取不同的普通源变量。 -/
theorem sourcePredicateAppend_compile_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L G K c z f : M.Domain} {d} (v : Fin d → M.Domain) (ρ : Env M d) (a q : Fin d)
    (different : q ≠ a) (hω : M.IsOmega ω)
    (program : PredicateAppend_d T ω n F L G K c (v q) z)
    (fn : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corresponds : ∀ i, i ≠ a → Rd_entry_d (v i) (ρ.bound i) f) :
    PFiniteTruth_d positive T (ρ.bound a) ω n X G K L f ↔
      Formula.satisfies ρ (predicateAnswer_m positive (.bound a) (.bound q)) :=
  (predicateAppend_eval_l hZF positive hω program fn (corresponds q different)).trans
    (predicateAnswer_sat_l positive ρ (.bound a) (.bound q)).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
