import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateLegacyOpcode
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NorCompiler

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

structure PNorAppend_d (T ω n F L G K c i j : M.Domain) : Prop where
  old : PBoundedFormula_d T ω n L F
  valid : PBoundedFormula_d T ω n K G
  restriction : Res0_d F G L T
  length : M.SuccessorOf K L
  root : Rd_entry_d L c G
  instruction : Bop_d T 2 c i j L
  left_mem : M.mem i T
  right_mem : M.mem j T
  root_mem : M.mem L T
  left_bound : M.mem i L
  right_bound : M.mem j L

def pnorAppend_m {d} (T ω n F L G K c i j : Term d) : Formula 1 d :=
  .conj (pboundedFormula_m T ω n L F) <| .conj (pboundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T 2 c i j L) <| .conj (.mem i T) <| .conj (.mem j T) <|
        .conj (.mem L T) <| .conj (.mem i L) (.mem j L)
derive_free_closed pnorAppend_m

theorem pnorAppend_delta_l {d} (T ω n F L G K c i j : Term d) :
    (pnorAppend_m T ω n F L G K c i j).IsDelta0 :=
  .conj (pboundedFormula_delta_l ..) (.conj (pboundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
        (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))))))

theorem pnorAppend_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n F L G K c i j : Term d) :
    Formula.satisfies ρ (pnorAppend_m T ω n F L G K c i j) ↔
      PNorAppend_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [pnorAppend_m,Formula.satisfies_conj_iff,pboundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,
      h.left_mem,h.right_mem,h.root_mem,h.left_bound,h.right_bound⟩⟩

/-- 生成记录中的新根准确组合原程序的两个子查询，含负极性。 -/
theorem pnorAppend_eval_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L G K c i j f : M.Domain} (hω : M.IsOmega ω)
    (program : PNorAppend_d T ω n F L G K c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    PFiniteTruth_d positive T A ω n X G K L f ↔
      NorAnswer_d positive (PFiniteTruth_d true T A ω n X F L i f) (PFiniteTruth_d true T A ω n X F L j f) := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  have hfE := (full f).mpr hf
  obtain ⟨V,H,check⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) program.valid
  have eval := ptruthEval_of_check_l hZF program.valid check
  have query (r : M.Domain) : PFiniteTruth_d true T A ω n X G K r f ↔ Bhit_d H r f :=
    (pfiniteTruth_space_l hZF true hω program.valid.variables full).trans
      ((and_congr_right fun _ => pcertifiedTruth_value_l hZF true program.valid check).trans (and_iff_right hfE))
  have sub : M.MemberSubset L K := fun r hr => (program.length r).mpr (Or.inl hr)
  have left := (query i).symm.trans
    (pfiniteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.left_bound).symm
  have right := (query j).symm.trans
    (pfiniteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.right_bound).symm
  obtain ⟨Y,hY⟩ := (eval.1.2.2 L).mp program.length.predecessor_mem
  have row := ptruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans (((row f).trans (and_iff_right hfE)).trans
    ((ptruthNode_oldOpcode_l hKP (by decide) program.instruction).trans
      (btruthNode_decode_l hKP ⟨2,by decide⟩ program.left_mem program.right_mem program.root_mem program.instruction)))
  have answer : PFiniteTruth_d true T A ω n X G K L f ↔
      ¬ (PFiniteTruth_d true T A ω n X F L i f ∨ PFiniteTruth_d true T A ω n X F L j f) :=
    (query L).trans (hit.trans (not_congr (or_congr left right)))
  cases positive
  · change PFiniteTruth_d false T A ω n X G K L f ↔ _ ∨ _
    exact (pfiniteTruth_complement_l hZF hω program.valid hf).trans
      ((not_congr answer).trans Classical.not_not)
  · exact answer

/-- 原 Project 公式的两个子语义对应，经实际追加组合为原或非公式。 -/
theorem sourcePNor_compile_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L G K c i j f : M.Domain} {d} (ρ : Env M d) (φ ψ : Formula 1 d)
    (hω : M.IsOmega ω) (program : PNorAppend_d T ω n F L G K c i j)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (left : PFiniteTruth_d true T A ω n X F L i f ↔ Formula.satisfies ρ φ)
    (right : PFiniteTruth_d true T A ω n X F L j f ↔ Formula.satisfies ρ ψ) :
    PFiniteTruth_d positive T A ω n X G K L f ↔ Formula.satisfies ρ (norAnswer_m positive φ ψ) :=
  (pnorAppend_eval_l hZF positive hω program hf).trans
    ((norAnswer_congr_l positive left right).trans (norAnswer_sat_l positive ρ φ ψ).symm)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
