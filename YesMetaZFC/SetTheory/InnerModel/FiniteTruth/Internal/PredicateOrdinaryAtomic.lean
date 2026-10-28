import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AtomicCompiler
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateLegacyOpcode

/-! # 在已有内部程序后追加原子叶

根行是旧内部长度，不再限定为零。实际限制证书保留全部旧指令，新增行
准确解释成员关系或相等；两个极性仍使用原统一 Σ₁ 查询。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

structure PAtomicAppend_d (equal : Bool) (T ω n F L G K c i j : M.Domain) : Prop where
  old : PBoundedFormula_d T ω n L F
  valid : PBoundedFormula_d T ω n K G
  restriction : Res0_d F G L T
  length : M.SuccessorOf K L
  root : Rd_entry_d L c G
  instruction : Bop_d T (atomicTag equal) c i j L
  left_mem : M.mem i T
  right_mem : M.mem j T
  root_mem : M.mem L T
  left_bound : M.mem i n
  right_bound : M.mem j n

def patomicAppend_m (equal : Bool) {d} (T ω n F L G K c i j : Term d) : Formula 1 d :=
  .conj (pboundedFormula_m T ω n L F) <| .conj (pboundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T (atomicTag equal) c i j L) <| .conj (.mem i T) <| .conj (.mem j T) <|
        .conj (.mem L T) <| .conj (.mem i n) (.mem j n)
 derive_free_closed patomicAppend_m

theorem patomicAppend_delta_l (equal : Bool) {d} (T ω n F L G K c i j : Term d) :
    (patomicAppend_m equal T ω n F L G K c i j).IsDelta0 :=
  .conj (pboundedFormula_delta_l ..) (.conj (pboundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
        (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))))))

theorem patomicAppend_sat_l (hKP : M.Models KP) (equal : Bool) {d} (ρ : Env M d)
    (T ω n F L G K c i j : Term d) :
    Formula.satisfies ρ (patomicAppend_m equal T ω n F L G K c i j) ↔
      PAtomicAppend_d equal (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [patomicAppend_m,Formula.satisfies_conj_iff,pboundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,
      h.left_mem,h.right_mem,h.root_mem,h.left_bound,h.right_bound⟩⟩

/-- 追加原子叶的真实新根不依赖前面程序所计算的任何真值。 -/
theorem patomicAppend_eval_l (hZF : M.Models ZF) (positive equal : Bool)
    {T A ω n X F L G K c i j f a b : M.Domain} (hω : M.IsOmega ω)
    (program : PAtomicAppend_d equal T ω n F L G K c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (hia : Rd_entry_d i a f) (hjb : Rd_entry_d j b f) :
    PFiniteTruth_d positive T A ω n X G K L f ↔ AtomicAnswer_d positive equal a b := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  have hfE := (full f).mpr hf
  obtain ⟨V,H,check⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) program.valid
  have eval := ptruthEval_of_check_l hZF program.valid check
  obtain ⟨Y,hY⟩ := (eval.1.2.2 L).mp program.length.predecessor_mem
  have row := ptruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans (((row f).trans (and_iff_right hfE)).trans
    ((ptruthNode_oldOpcode_l hKP (show atomicTag equal < 4 by cases equal <;> decide) program.instruction).trans
      (atomicNode_l hKP equal program.left_mem program.right_mem program.root_mem program.instruction hf hia hjb)))
  have answer : BtruthAnswer_d positive H L f ↔ AtomicAnswer_d positive equal a b := by
    cases positive <;> simp only [BtruthAnswer_d,AtomicAnswer_d,Bool.false_eq_true,↓reduceIte,hit]
  exact (pfiniteTruth_space_l hZF positive hω program.valid.variables full).trans
    ((and_congr_right fun _ => (pcertifiedTruth_value_l hZF positive program.valid check).trans answer).trans (and_iff_right hfE))

/-- 原源变量的条目对应在任意已有程序的原子追加后仍给出准确语义。 -/
theorem sourcePAtomicAppend_compile_l (hZF : M.Models ZF) (positive equal : Bool)
    {T A ω n X F L G K c f : M.Domain} {d} (v : Fin d → M.Domain) (ρ : Env M d) (p q : Fin d)
    (hω : M.IsOmega ω) (program : PAtomicAppend_d equal T ω n F L G K c (v p) (v q))
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corresponds : ∀ i, Rd_entry_d (v i) (ρ.bound i) f) :
    PFiniteTruth_d positive T A ω n X G K L f ↔
      Formula.satisfies ρ (atomicAnswer_m positive equal (.bound p) (.bound q)) :=
  (patomicAppend_eval_l hZF positive equal hω program hf (corresponds p) (corresponds q)).trans
    (atomicAnswer_sat_l hZF.1 positive equal ρ (.bound p) (.bound q)).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
