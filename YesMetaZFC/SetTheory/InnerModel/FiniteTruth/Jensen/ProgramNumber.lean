import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteAssignmentSpace

/-! # 内部程序图、编号列与自然数码的同层预算

原 J 层包含内部 ω 即包含任意合法内部有限程序图。证明用固定四重
自然数代码空间及已证的完整有限函数空间，不使用小层 KP 或 Collection。
编号关系本身的局部准确性及其隐藏配对证书预算仍是另外的义务。
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

theorem jh_finite_function_mem_l (hZF : M.Models ZF) {a C ω n X F : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hXC : M.mem X C) (hn : M.mem n ω)
    (hf : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F n X) : M.mem F C := by
  obtain ⟨E,hEC,full⟩ := jh_finite_functionSpace_l hZF ha h hω hωC hXC n hn
  exact jh_value_transitive_l (ZF.models_kpi_l hZF) h E hEC F ((full F).mpr hf)

/-- 所有合法内部有限程序图均属于每个包含内部 ω 的原 J 层。 -/
theorem jh_bounded_program_mem_l (hZF : M.Models ZF) {a C T ω n L F : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (valid : BoundedFormula_d T ω n L F) : M.mem F C := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  obtain ⟨P,hPC,hP⟩ := closed.exists_l hKP .prod hωC hωC hωC
  obtain ⟨Q,hQC,hQ⟩ := closed.exists_l hKP .prod hωC hPC hωC
  obtain ⟨S,hSC,hS⟩ := closed.exists_l hKP .prod hωC hQC hωC
  have node {r c : M.Domain} (hr : M.mem r ω) (hc : Bnode_d T ω n r c) : M.mem c S := by
    have one (tag : Nat) {A B D : M.Domain} (aω : M.MemberSubset A ω)
        (bω : M.MemberSubset B ω) (dω : M.MemberSubset D ω) (hc : Bcase_d T tag c A B D) : M.mem c S := by
      obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,⟨p,hp,hv⟩,pair⟩,hi,hj,hk⟩ := hc
      have hpP := (hP p).mpr ⟨j,k,bω j hj,dω k hk,hp⟩
      have hvQ := (hQ v).mpr ⟨i,p,aω i hi,hpP,hv⟩
      exact (hS c).mpr ⟨t,v,num_mem_l hZF.1 hω ht,hvQ,pair⟩
    have nω := hω.transitive hZF n valid.variables
    have rω := hω.transitive hZF r hr
    rcases hc with hc | hc | hc | hc
    · exact one 0 nω nω (fun _ h => h) hc
    · exact one 1 nω nω (fun _ h => h) hc
    · exact one 2 rω rω (fun _ h => h) hc
    · exact one 3 nω nω rω hc
  have hf := fn0_function_l hKP valid.graph
  have fs : M.IsSetFunctionFromTo I F L S := by
    refine ⟨hf.1,hf.2.1,fun i hi => ?_⟩
    obtain ⟨c,_,hic⟩ := hf.2.2 i hi
    exact ⟨c,node (hω.transitive hZF L valid.finite i hi) (valid.at_l hic).2.2,hic⟩
  exact jh_finite_function_mem_l hZF ha h hω hωC hSC valid.finite fs

/-- 编码列是真实自然数值有限函数，故它与编号一起留在原层。 -/
theorem jh_programNumber_l (hZF : M.Models ZF) {a C T ω n L F r : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) :
    M.mem F C ∧ ∃ e G, M.mem e ω ∧ M.mem e C ∧ M.mem G C ∧
      ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e ∧
      NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G := by
  obtain ⟨e,he,num⟩ := programNumber_exists_l hZF hω valid hr
  have details := num
  obtain ⟨_,_,_,_,G,_,_,rows,_⟩ := details
  have hGC := jh_finite_function_mem_l hZF ha h hω hωC hωC valid.finite rows.1
  exact ⟨jh_bounded_program_mem_l hZF ha h hω hωC valid,e,G,he,
    jh_value_transitive_l (ZF.models_kpi_l hZF) h ω hωC e he,hGC,num,rows⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
