import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramExtension
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentRealization

/-! # 实际有界存在指令的追加与源语义

新指令读取原赋值的界变量，更新一个新鲜槽，再查询较早子行。全部图和
程序长度都是模型对象；传递求值域保证源有界量词的见证仍在赋值空间内。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure PExistsAppend_d (T ω n F L G K c i j k : M.Domain) : Prop where
  old : PBoundedFormula_d T ω n L F
  valid : PBoundedFormula_d T ω n K G
  restriction : Res0_d F G L T
  length : M.SuccessorOf K L
  root : Rd_entry_d L c G
  instruction : Bop_d T 3 c i j k
  fresh_mem : M.mem i T
  bound_mem : M.mem j T
  child_mem : M.mem k T
  fresh_bound : M.mem i n
  bound_bound : M.mem j n
  child_bound : M.mem k L

def pexistsAppend_m {d} (T ω n F L G K c i j k : Term d) : Formula 1 d :=
  .conj (pboundedFormula_m T ω n L F) <| .conj (pboundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T 3 c i j k) <| .conj (.mem i T) <| .conj (.mem j T) <|
        .conj (.mem k T) <| .conj (.mem i n) <| .conj (.mem j n) (.mem k L)
derive_free_closed pexistsAppend_m

theorem pexistsAppend_delta_l {d} (T ω n F L G K c i j k : Term d) :
    (pexistsAppend_m T ω n F L G K c i j k).IsDelta0 :=
  .conj (pboundedFormula_delta_l ..) (.conj (pboundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
        (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _)))))))))))

theorem pexistsAppend_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n F L G K c i j k : Term d) :
    Formula.satisfies ρ (pexistsAppend_m T ω n F L G K c i j k) ↔
      PExistsAppend_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) (k.eval ρ) := by
  simp only [pexistsAppend_m,Formula.satisfies_conj_iff,pboundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,
      h.fresh_mem,h.bound_mem,h.child_mem,h.fresh_bound,h.bound_bound,h.child_bound⟩⟩

theorem PExistsAppend_d.extension_l {T U ω n F L G K c i j k : M.Domain}
    (program : PExistsAppend_d U ω n F L G K c i j k)
    (old : PBoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    PProgramExtension_d T ω n F L U G K :=
  ⟨old,program.valid,sub,fun r hr => (program.length r).mpr (Or.inl hr),program.restriction⟩

def PExistsStep_d (T A ω n X F L i j k f : M.Domain) : Prop :=
  ∃ a, M.mem a X ∧ Rd_entry_d j a f ∧ ∃ x, M.mem x X ∧ M.mem x a ∧
    ∃ g, Fn0_d n X g ∧ Bupdate_d n X f i x g ∧ PFiniteTruth_d true T A ω n X F L k g

/-- 操作语义先消去完整空间参数，再以真实函数图表述更新后的子查询。 -/
theorem pexistsAppend_eval_l (hZF : M.Models ZF) (positive : Bool)
    {T A ω n X F L G K c i j k f : M.Domain} (hω : M.IsOmega ω)
    (program : PExistsAppend_d T ω n F L G K c i j k)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    PFiniteTruth_d positive T A ω n X G K L f ↔
      (if positive then PExistsStep_d T A ω n X F L i j k f else ¬ PExistsStep_d T A ω n X F L i j k f) := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  obtain ⟨V,H,check⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) program.valid
  have eval := ptruthEval_of_check_l hZF program.valid check
  have query (r g : M.Domain) (hg : M.IsSetFunctionFromTo (kp_pair_l hKP) g n X) :
      PFiniteTruth_d true T A ω n X G K r g ↔ Bhit_d H r g :=
    (pfiniteTruth_space_l hZF true hω program.valid.variables full).trans
      ((and_congr_right fun _ => pcertifiedTruth_value_l hZF true program.valid check).trans (and_iff_right ((full g).mpr hg)))
  have sub : M.MemberSubset L K := fun r hr => (program.length r).mpr (Or.inl hr)
  have child (g : M.Domain) (hg : M.IsSetFunctionFromTo (kp_pair_l hKP) g n X) :
      Bhit_d H k g ↔ PFiniteTruth_d true T A ω n X F L k g :=
    (query k g hg).symm.trans
      (pfiniteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.child_bound).symm
  have node : PtruthNode_d T A n X E H c f ↔ PExistsStep_d T A ω n X F L i j k f := by
    rw [ptruthNode_oldOpcode_l hKP (by decide) program.instruction,btruthNode_decode_l hKP ⟨3,by decide⟩ program.fresh_mem program.bound_mem program.child_mem program.instruction]
    constructor
    · rintro ⟨a,ha,hja,x,hx,hxa,g,hg,update,hit⟩
      have fn := (full g).mp hg
      exact ⟨a,ha,hja,x,hx,hxa,g,fn0_of_function_l hKP fn,update,(child g fn).mp hit⟩
    · rintro ⟨a,ha,hja,x,hx,hxa,g,fn,update,answer⟩
      have hg := fn0_function_l hKP fn
      exact ⟨a,ha,hja,x,hx,hxa,g,(full g).mpr hg,update,(child g hg).mpr answer⟩
  obtain ⟨Y,hY⟩ := (eval.1.2.2 L).mp program.length.predecessor_mem
  have row := ptruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans
    (((row f).trans (and_iff_right ((full f).mpr hf))).trans node)
  have answer := (query L f hf).trans hit
  cases positive
  · exact (pfiniteTruth_complement_l hZF hω program.valid hf).trans (not_congr answer)
  · exact answer


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
