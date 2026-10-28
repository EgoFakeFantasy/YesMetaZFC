import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthPrefix

/-! # 实际或非指令的追加与组合语义

追加记录保留旧程序的实际限制证书。新行只读旧行，正负统一查询准确对应
旧查询的或非及其否定；变量域、程序长度和赋值仍为模型内部对象。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

structure NorAppend_d (T ω n F L G K c i j : M.Domain) : Prop where
  old : BoundedFormula_d T ω n L F
  valid : BoundedFormula_d T ω n K G
  restriction : Res0_d F G L T
  length : M.SuccessorOf K L
  root : Rd_entry_d L c G
  instruction : Bop_d T 2 c i j L
  left_mem : M.mem i T
  right_mem : M.mem j T
  root_mem : M.mem L T
  left_bound : M.mem i L
  right_bound : M.mem j L

def norAppend_m {d} (T ω n F L G K c i j : Term d) : Formula 1 d :=
  .conj (boundedFormula_m T ω n L F) <| .conj (boundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T 2 c i j L) <| .conj (.mem i T) <| .conj (.mem j T) <|
        .conj (.mem L T) <| .conj (.mem i L) (.mem j L)
derive_free_closed norAppend_m

theorem norAppend_delta_l {d} (T ω n F L G K c i j : Term d) :
    (norAppend_m T ω n F L G K c i j).IsDelta0 :=
  .conj (boundedFormula_delta_l ..) (.conj (boundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
        (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))))))

theorem norAppend_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n F L G K c i j : Term d) :
    Formula.satisfies ρ (norAppend_m T ω n F L G K c i j) ↔
      NorAppend_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [norAppend_m,Formula.satisfies_conj_iff,boundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,
      h.left_mem,h.right_mem,h.root_mem,h.left_bound,h.right_bound⟩⟩

def NorAnswer_d (positive : Bool) (P Q : Prop) : Prop :=
  if positive then ¬ (P ∨ Q) else P ∨ Q

def norAnswer_m (positive : Bool) {d} (φ ψ : Formula 1 d) : Formula 1 d :=
  if positive then .neg (.disj φ ψ) else .disj φ ψ

@[simp] theorem norAnswer_closed_l (positive : Bool) {d} (φ ψ : Formula 1 d)
    (hφ : φ.FreeClosed) (hψ : ψ.FreeClosed) : (norAnswer_m positive φ ψ).FreeClosed := by
  cases positive <;> simp [norAnswer_m,Definitional.Formula.FreeClosed] at * <;> simp_all

theorem norAnswer_sat_l (positive : Bool) {d} (ρ : Env M d) (φ ψ : Formula 1 d) :
    Formula.satisfies ρ (norAnswer_m positive φ ψ) ↔
      NorAnswer_d positive (Formula.satisfies ρ φ) (Formula.satisfies ρ ψ) := by
  cases positive <;> simp only [norAnswer_m,NorAnswer_d,Bool.false_eq_true,↓reduceIte,
    Formula.satisfies_neg_iff,Formula.satisfies_disj_iff]

/-- 生成记录中的新根准确组合原程序的两个子查询，含负极性。 -/
theorem norAppend_eval_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L G K c i j f : M.Domain} (hω : M.IsOmega ω)
    (program : NorAppend_d T ω n F L G K c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    FiniteTruth_d positive T ω n X G K L f ↔
      NorAnswer_d positive (FiniteTruth_d true T ω n X F L i f) (FiniteTruth_d true T ω n X F L j f) := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  have hfE := (full f).mpr hf
  obtain ⟨V,H,check⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) program.valid
  have eval := btruthEval_of_check_l hZF program.valid check
  have query (r : M.Domain) : FiniteTruth_d true T ω n X G K r f ↔ Bhit_d H r f :=
    (finiteTruth_space_l hZF true hω program.valid.variables full).trans
      ((and_congr_right fun _ => certifiedTruth_value_l hZF true program.valid check).trans (and_iff_right hfE))
  have sub : M.MemberSubset L K := fun r hr => (program.length r).mpr (Or.inl hr)
  have left := (query i).symm.trans
    (finiteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.left_bound).symm
  have right := (query j).symm.trans
    (finiteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.right_bound).symm
  obtain ⟨Y,hY⟩ := (eval.1.2.2 L).mp program.length.predecessor_mem
  have row := btruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans (((row f).trans (and_iff_right hfE)).trans
    (btruthNode_decode_l hKP ⟨2,by decide⟩ program.left_mem program.right_mem program.root_mem program.instruction))
  have answer : FiniteTruth_d true T ω n X G K L f ↔
      ¬ (FiniteTruth_d true T ω n X F L i f ∨ FiniteTruth_d true T ω n X F L j f) :=
    (query L).trans (hit.trans (not_congr (or_congr left right)))
  cases positive
  · change FiniteTruth_d false T ω n X G K L f ↔ _ ∨ _
    exact (finiteTruth_complement_l hZF hω program.valid hf).trans
      ((not_congr answer).trans Classical.not_not)
  · exact answer

/-- 两个子公式的语义对应可在正负或非模板下组合。 -/
theorem norAnswer_congr_l (positive : Bool) {P Q R S : Prop} (left : P ↔ R) (right : Q ↔ S) :
    NorAnswer_d positive P Q ↔ NorAnswer_d positive R S := by
  cases positive
  · exact or_congr left right
  · exact not_congr (or_congr left right)

/-- 原 Project 公式的两个子语义对应，经实际追加组合为原或非公式。 -/
theorem sourceNor_compile_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L G K c i j f : M.Domain} {d} (ρ : Env M d) (φ ψ : Formula 1 d)
    (hω : M.IsOmega ω) (program : NorAppend_d T ω n F L G K c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (left : FiniteTruth_d true T ω n X F L i f ↔ Formula.satisfies ρ φ)
    (right : FiniteTruth_d true T ω n X F L j f ↔ Formula.satisfies ρ ψ) :
    FiniteTruth_d positive T ω n X G K L f ↔ Formula.satisfies ρ (norAnswer_m positive φ ψ) :=
  (norAppend_eval_l hZF positive hω program hf).trans
    ((norAnswer_congr_l positive left right).trans (norAnswer_sat_l positive ρ φ ψ).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
