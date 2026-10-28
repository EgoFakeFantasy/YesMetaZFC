import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedCodeConstruction
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruth

/-! # 编译中的语法容器扩张及实际追加

新代码可能需要较大的同层容器。扩张只改变有界解码的搜索范围，原有效指令
和整张真值证书的意义保持不变；实际同层追加图也保持原程序合法性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem btruthNode_container_l (hKP : M.Models KP) {T U ω n r c X E H f : M.Domain}
    (sub : M.MemberSubset T U) (valid : Bnode_d T ω n r c) :
    BtruthNode_d T n X E H c f ↔ BtruthNode_d U n X E H c f := by
  rcases valid with valid | valid | valid | valid
  · obtain ⟨i,hi,j,hj,k,hk,hop,_⟩ := valid
    rw [btruthNode_decode_l hKP ⟨0,by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨0,by decide⟩ (sub i hi) (sub j hj) (sub k hk) (bop_mono_l sub 0 hop)]
  · obtain ⟨i,hi,j,hj,k,hk,hop,_⟩ := valid
    rw [btruthNode_decode_l hKP ⟨1,by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨1,by decide⟩ (sub i hi) (sub j hj) (sub k hk) (bop_mono_l sub 1 hop)]
  · obtain ⟨i,hi,j,hj,k,hk,hop,_⟩ := valid
    rw [btruthNode_decode_l hKP ⟨2,by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨2,by decide⟩ (sub i hi) (sub j hj) (sub k hk) (bop_mono_l sub 2 hop)]
  · obtain ⟨i,hi,j,hj,k,hk,hop,_⟩ := valid
    rw [btruthNode_decode_l hKP ⟨3,by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨3,by decide⟩ (sub i hi) (sub j hj) (sub k hk) (bop_mono_l sub 3 hop)]

theorem btruthCheck_container_l (hKP : M.Models KP) {T U ω n X E F L Z H : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    BtruthCheck_d T n X E F L Z H ↔ BtruthCheck_d U n X E F L Z H := by
  constructor
  · rintro ⟨fn,check⟩
    refine ⟨fn,fun r hr c _ hrc Y hYZ hY => ?_⟩
    have hc := (valid.graph.bound_l hrc).2
    obtain ⟨bound,row⟩ := check r hr c hc hrc Y hYZ hY
    exact ⟨bound,fun f hf => (row f hf).trans
      (btruthNode_container_l hKP sub (valid.row r hr c hc hrc))⟩
  · rintro ⟨fn,check⟩
    refine ⟨fn,fun r hr c hc hrc Y hYZ hY => ?_⟩
    obtain ⟨bound,row⟩ := check r hr c (sub c hc) hrc Y hYZ hY
    exact ⟨bound,fun f hf => (row f hf).trans
      (btruthNode_container_l hKP sub (valid.row r hr c hc hrc)).symm⟩

/-- 组合解释器也保持语法容器扩张，含负真值及合法赋值条件。 -/
theorem finiteTruth_container_l (hKP : M.Models KP) (positive : Bool) {T U ω n X F L r f : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (sub : M.MemberSubset T U) :
    FiniteTruth_d positive T ω n X F L r f ↔ FiniteTruth_d positive U ω n X F L r f := by
  constructor
  · rintro ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩
    exact ⟨e,s,Z,S,E,V,H,space,hf,(btruthCheck_container_l hKP valid sub).mp truth,answer⟩
  · rintro ⟨e,s,Z,S,E,V,H,space,hf,truth,answer⟩
    exact ⟨e,s,Z,S,E,V,H,space,hf,(btruthCheck_container_l hKP valid sub).mpr truth,answer⟩

/-- 对已有实际追加图恢复合法性，而不把背景构造的另一个图直接当作层内图。 -/
theorem BoundedFormula_d.snoc_l (hKP : M.Models KP) {T ω n L F c s G : M.Domain}
    (valid : BoundedFormula_d T ω n L F) (hc : M.mem c T) (node : Bnode_d T ω n L c)
    (hsω : M.mem s ω) (hs : M.IsOrdinal s) (hls : M.SuccessorOf s L)
    (snoc : Snoc_d (kp_pair_l hKP) F L c G) : BoundedFormula_d T ω n s G := by
  let I := kp_pair_l hKP
  obtain ⟨K,hK,entries⟩ := valid.append_l hKP hc node hsω hs hls
  obtain ⟨rel,ge⟩ := (snoc_iff_entries_l I (fn0_function_l hKP valid.graph).1.1).mp snoc
  have eq := rel.eq_of_pairMember_iff hKP.1 (fn0_function_l hKP hK.graph).1.1
    (fun r d => (ge r d).trans (entries r d).symm)
  exact eq.symm ▸ hK

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
