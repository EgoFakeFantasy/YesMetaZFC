import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramExtension
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

structure ExistsAppend_d (T ω n F L G K c i j k : M.Domain) : Prop where
  old : BoundedFormula_d T ω n L F
  valid : BoundedFormula_d T ω n K G
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

def existsAppend_m {d} (T ω n F L G K c i j k : Term d) : Formula 1 d :=
  .conj (boundedFormula_m T ω n L F) <| .conj (boundedFormula_m T ω n K G) <|
    .conj (res0_m F G L T) <| .conj (KP.succ0_m K L) <| .conj (rd_entry0_m L c G) <|
      .conj (bop_m T 3 c i j k) <| .conj (.mem i T) <| .conj (.mem j T) <|
        .conj (.mem k T) <| .conj (.mem i n) <| .conj (.mem j n) (.mem k L)
derive_free_closed existsAppend_m

theorem existsAppend_delta_l {d} (T ω n F L G K c i j k : Term d) :
    (existsAppend_m T ω n F L G K c i j k).IsDelta0 :=
  .conj (boundedFormula_delta_l ..) (.conj (boundedFormula_delta_l ..)
    (.conj (res0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _)
        (.conj (.mem _ _) (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _)))))))))))

theorem existsAppend_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n F L G K c i j k : Term d) :
    Formula.satisfies ρ (existsAppend_m T ω n F L G K c i j k) ↔
      ExistsAppend_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (F.eval ρ) (L.eval ρ)
        (G.eval ρ) (K.eval ρ) (c.eval ρ) (i.eval ρ) (j.eval ρ) (k.eval ρ) := by
  simp only [existsAppend_m,Formula.satisfies_conj_iff,boundedFormula_sat_l hKP,
    res0_sat_l hKP.1,KP.succ0_sat_l hKP.1,rd_entry0_sat_l hKP.1,bop_sat_l hKP.1,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩,
    fun h => ⟨h.old,h.valid,h.restriction,h.length,h.root,h.instruction,
      h.fresh_mem,h.bound_mem,h.child_mem,h.fresh_bound,h.bound_bound,h.child_bound⟩⟩

theorem ExistsAppend_d.extension_l {T U ω n F L G K c i j k : M.Domain}
    (program : ExistsAppend_d U ω n F L G K c i j k)
    (old : BoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    ProgramExtension_d T ω n F L U G K :=
  ⟨old,program.valid,sub,fun r hr => (program.length r).mpr (Or.inl hr),program.restriction⟩

def ExistsStep_d (T ω n X F L i j k f : M.Domain) : Prop :=
  ∃ a, M.mem a X ∧ Rd_entry_d j a f ∧ ∃ x, M.mem x X ∧ M.mem x a ∧
    ∃ g, Fn0_d n X g ∧ Bupdate_d n X f i x g ∧ FiniteTruth_d true T ω n X F L k g

/-- 操作语义先消去完整空间参数，再以真实函数图表述更新后的子查询。 -/
theorem existsAppend_eval_l (hZF : M.Models ZF) (positive : Bool)
    {T ω n X F L G K c i j k f : M.Domain} (hω : M.IsOmega ω)
    (program : ExistsAppend_d T ω n F L G K c i j k)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X) :
    FiniteTruth_d positive T ω n X G K L f ↔
      (if positive then ExistsStep_d T ω n X F L i j k f else ¬ ExistsStep_d T ω n X F L i j k f) := by
  let hKP := ZF.modelsKP hZF
  obtain ⟨E,full⟩ := ZF.exists_functionSpace hZF (kp_pair_l hKP) n X
  obtain ⟨V,H,check⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) program.valid
  have eval := btruthEval_of_check_l hZF program.valid check
  have query (r g : M.Domain) (hg : M.IsSetFunctionFromTo (kp_pair_l hKP) g n X) :
      FiniteTruth_d true T ω n X G K r g ↔ Bhit_d H r g :=
    (finiteTruth_space_l hZF true hω program.valid.variables full).trans
      ((and_congr_right fun _ => certifiedTruth_value_l hZF true program.valid check).trans (and_iff_right ((full g).mpr hg)))
  have sub : M.MemberSubset L K := fun r hr => (program.length r).mpr (Or.inl hr)
  have child (g : M.Domain) (hg : M.IsSetFunctionFromTo (kp_pair_l hKP) g n X) :
      Bhit_d H k g ↔ FiniteTruth_d true T ω n X F L k g :=
    (query k g hg).symm.trans
      (finiteTruth_prefix_l hZF true hω program.old program.valid sub program.restriction program.child_bound).symm
  have node : BtruthNode_d T n X E H c f ↔ ExistsStep_d T ω n X F L i j k f := by
    rw [btruthNode_decode_l hKP ⟨3,by decide⟩ program.fresh_mem program.bound_mem program.child_mem program.instruction]
    constructor
    · rintro ⟨a,ha,hja,x,hx,hxa,g,hg,update,hit⟩
      have fn := (full g).mp hg
      exact ⟨a,ha,hja,x,hx,hxa,g,fn0_of_function_l hKP fn,update,(child g fn).mp hit⟩
    · rintro ⟨a,ha,hja,x,hx,hxa,g,fn,update,answer⟩
      have hg := fn0_function_l hKP fn
      exact ⟨a,ha,hja,x,hx,hxa,g,(full g).mpr hg,update,(child g hg).mpr answer⟩
  obtain ⟨Y,hY⟩ := (eval.1.2.2 L).mp program.length.predecessor_mem
  have row := btruthEval_row_l hKP (fn0_function_l hKP program.valid.graph).1 eval program.root hY
    (program.valid.at_l program.root).2.2
  have hit := (Bhit_d.value_l eval.1.2.1.2 hY).trans
    (((row f).trans (and_iff_right ((full f).mpr hf))).trans node)
  have answer := (query L f hf).trans hit
  cases positive
  · exact (finiteTruth_complement_l hZF hω program.valid hf).trans (not_congr answer)
  · exact answer

/-- 新鲜槽和传递域将操作有界存在准确连接到原 Project binder。 -/
theorem sourceExistsAppend_compile_l (hZF : M.Models ZF) (positive : Bool) {d}
    (v : Fin d → M.Domain) (ρ : Env M d) (φ : Formula 1 (d+1)) (q : Fin d)
    {T ω n X F L G K c fresh k f : M.Domain} (hω : M.IsOmega ω) (hx : M.TransitiveSet X)
    (program : ExistsAppend_d T ω n F L G K c fresh (v q) k)
    (unused : ∀ i, v i ≠ fresh)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f n X)
    (corr : ∀ i, Rd_entry_d (v i) (ρ.bound i) f)
    (body : ∀ x g, M.mem x X → M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) g n X →
      (∀ i, Rd_entry_d (Fin.cases fresh v i) ((ρ.push x).bound i) g) →
      (FiniteTruth_d true T ω n X F L k g ↔ Formula.satisfies (ρ.push x) φ)) :
    FiniteTruth_d positive T ω n X G K L f ↔
      Formula.satisfies ρ (if positive then Formula.existsMem (.bound q) φ else .neg (Formula.existsMem (.bound q) φ)) := by
  let hKP := ZF.modelsKP hZF
  have valueX : M.mem (ρ.bound q) X := hf.output_mem_of_pairMember (corr q)
  have step : ExistsStep_d T ω n X F L fresh (v q) k f ↔
      ∃ x, M.mem x (ρ.bound q) ∧ Formula.satisfies (ρ.push x) φ := by
    constructor
    · rintro ⟨a,_,hja,x,hxX,hxa,g,fn,update,answer⟩
      have eq := hf.1.2 (v q) a (ρ.bound q) hja (corr q)
      subst a
      have hg := fn0_function_l hKP fn
      have actual := (bupdate_correct_l hKP hf hg program.fresh_bound hxX).mp update
      have newCorr := assignment_push_correspond_l hKP corr unused actual
      exact ⟨x,hxa,(body x g hxX hg newCorr).mp answer⟩
    · rintro ⟨x,hxa,hφ⟩
      have hxX := hx (ρ.bound q) valueX x hxa
      obtain ⟨g,actual,hg⟩ := senv_update_exists_l (kp_pair_l hKP) hZF hf program.fresh_bound hxX
      have newCorr := assignment_push_correspond_l hKP corr unused actual
      exact ⟨ρ.bound q,valueX,corr q,x,hxX,hxa,g,fn0_of_function_l hKP hg,
        (bupdate_correct_l hKP hf hg program.fresh_bound hxX).mpr actual,(body x g hxX hg newCorr).mpr hφ⟩
  have truth := (existsAppend_eval_l hZF true hω program hf).trans
    (step.trans (Formula.satisfies_existsMem_iff ρ (.bound q) φ).symm)
  cases positive
  · exact (finiteTruth_complement_l hZF hω program.valid hf).trans
      ((not_congr truth).trans (Formula.satisfies_neg_iff ρ (Formula.existsMem (.bound q) φ)).symm)
  · exact truth

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
