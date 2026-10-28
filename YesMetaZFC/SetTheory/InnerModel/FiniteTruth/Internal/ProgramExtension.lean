import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AtomicAppend
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NorCompiler

/-! # 编译中连续程序扩展的组合

代码容器与程序长度可以同时增长。实际限制证书可传递组合，旧根的两个
真值极性因而跨越任意有限次已验证追加保持。此处不另设程序或推导核。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

structure ProgramExtension_d (T ω n F L U G K : M.Domain) : Prop where
  old : BoundedFormula_d T ω n L F
  valid : BoundedFormula_d U ω n K G
  containers : M.MemberSubset T U
  lengths : M.MemberSubset L K
  restriction : Res0_d F G L U

/-- 连续扩展通过真实限制图组合，不要求两个代码容器相同。 -/
theorem ProgramExtension_d.trans_l (hKP : M.Models KP) {T U V ω n F G H L K J : M.Domain}
    (first : ProgramExtension_d T ω n F L U G K) (second : ProgramExtension_d U ω n G K V H J) :
    ProgramExtension_d T ω n F L V H J := by
  have left := res0_restriction_l hKP first.valid.graph first.restriction
  have right := res0_restriction_l hKP second.valid.graph second.restriction
  have composed : M.IsRestrictionOf (kp_pair_l hKP) F H L := by
    refine ⟨left.1,fun r c => ?_⟩
    constructor
    · intro h
      obtain ⟨hr,hG⟩ := (left.2 r c).mp h
      exact ⟨hr,((right.2 r c).mp hG).2⟩
    · rintro ⟨hr,hH⟩
      exact (left.2 r c).mpr ⟨hr,(right.2 r c).mpr ⟨first.lengths r hr,hH⟩⟩
  exact ⟨first.old,second.valid,fun x hx => second.containers x (first.containers x hx),
    fun x hx => second.lengths x (first.lengths x hx),res0_of_restriction_l hKP second.valid.graph composed⟩

/-- 实际容器增长和程序增长共同保持全部旧查询。 -/
theorem ProgramExtension_d.query_l (hZF : M.Models ZF) (positive : Bool)
    {T U ω n X F L G K r f : M.Domain} (extension : ProgramExtension_d T ω n F L U G K)
    (hω : M.IsOmega ω) (hr : M.mem r L) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive U ω n X G K r f :=
  (finiteTruth_container_l (ZF.modelsKP hZF) positive extension.old extension.containers).trans
    (finiteTruth_prefix_l hZF positive hω (extension.old.container_mono_l (ZF.modelsKP hZF) extension.containers)
      extension.valid extension.lengths extension.restriction hr)

/-- 原子追加具有原容器到新容器的完整扩展证书。 -/
theorem AtomicAppend_d.extension_l {equal : Bool} {T U ω n F L G K c i j : M.Domain}
    (program : AtomicAppend_d equal U ω n F L G K c i j)
    (old : BoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    ProgramExtension_d T ω n F L U G K :=
  ⟨old,program.valid,sub,fun r hr => (program.length r).mpr (Or.inl hr),program.restriction⟩

/-- 或非追加同样保留连续编译所需的全部前缀证书。 -/
theorem NorAppend_d.extension_l {T U ω n F L G K c i j : M.Domain}
    (program : NorAppend_d U ω n F L G K c i j)
    (old : BoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    ProgramExtension_d T ω n F L U G K :=
  ⟨old,program.valid,sub,fun r hr => (program.length r).mpr (Or.inl hr),program.restriction⟩

/-- 不追加指令的原程序也可作为组合中的恒等前缀。 -/
theorem ProgramExtension_d.refl_l (hKP : M.Models KP) {T ω n F L : M.Domain}
    (valid : BoundedFormula_d T ω n L F) : ProgramExtension_d T ω n F L T F L := by
  have same : M.IsRestrictionOf (kp_pair_l hKP) F F L :=
    ⟨(fn0_function_l hKP valid.graph).1.1,fun r c =>
      ⟨fun h => ⟨(valid.graph.bound_l h).1,h⟩,And.right⟩⟩
  exact ⟨valid,valid,fun _ h => h,fun _ h => h,res0_of_restriction_l hKP valid.graph same⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
