import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruth

/-! # 合法内部程序的整图递推方程

合法指令只读取严格较早的行，因此精确前缀与整张真值图具有相同一步语义。
此处的行和程序均为内部对象，不使用宿主自然数递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem bhit_restriction_l (hKP : M.Models KP) {P H r i f : M.Domain}
    (hp : M.IsRestrictionOf (kp_pair_l hKP) P H r) (hi : M.mem i r) :
    Bhit_d P i f ↔ Bhit_d H i f := by
  constructor
  · rintro ⟨A, hA, hf⟩
    exact ⟨A, ((hp.2 i A).mp hA).2, hf⟩
  · rintro ⟨A, hA, hf⟩
    exact ⟨A, (hp.2 i A).mpr ⟨hi, hA⟩, hf⟩

/-- 语法的前驱行界使整图核验与递归定义中的精确前缀准确一致。 -/
theorem btruthNode_restriction_l (hKP : M.Models KP) {T ω n X E P H r c f : M.Domain}
    (hp : M.IsRestrictionOf (kp_pair_l hKP) P H r) (hc : Bnode_d T ω n r c) :
    BtruthNode_d T n X E P c f ↔ BtruthNode_d T n X E H c f := by
  rcases hc with hc | hc | hc | hc
  · obtain ⟨i, hi, j, hj, k, hk, hop, _⟩ := hc
    rw [btruthNode_decode_l hKP ⟨0, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨0, by decide⟩ hi hj hk hop]
    rfl
  · obtain ⟨i, hi, j, hj, k, hk, hop, _⟩ := hc
    rw [btruthNode_decode_l hKP ⟨1, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨1, by decide⟩ hi hj hk hop]
    rfl
  · obtain ⟨i, hi, j, hj, k, hk, hop, hir, hjr, _⟩ := hc
    rw [btruthNode_decode_l hKP ⟨2, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨2, by decide⟩ hi hj hk hop]
    simp only [Barg_d, bhit_restriction_l hKP hp hir, bhit_restriction_l hKP hp hjr]
  · obtain ⟨i, hi, j, hj, k, hk, hop, _, _, hkr⟩ := hc
    rw [btruthNode_decode_l hKP ⟨3, by decide⟩ hi hj hk hop,
      btruthNode_decode_l hKP ⟨3, by decide⟩ hi hj hk hop]
    simp only [Barg_d, bhit_restriction_l hKP hp hkr]

/-- 每个合法行按整张历史中的旧行递推，真值集合仍精确受赋值空间限制。 -/
theorem btruthEval_row_l (hKP : M.Models KP) {T ω n X E F length H r c Y : M.Domain}
    (hF : M.IsSetFunction (kp_pair_l hKP) F)
    (hH : BtruthEval_d (kp_pair_l hKP) T n X E F length H)
    (hc : Rd_entry_d r c F) (hY : Rd_entry_d r Y H) (valid : Bnode_d T ω n r c) :
    ∀ f, M.mem f Y ↔ M.mem f E ∧ BtruthNode_d T n X E H c f := by
  obtain ⟨P, hp, _, step⟩ := btruthEval_unfold_l hKP hF hH hc hY
  exact fun f => (step f).trans
    (and_congr_right fun _ => btruthNode_restriction_l hKP hp valid)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
