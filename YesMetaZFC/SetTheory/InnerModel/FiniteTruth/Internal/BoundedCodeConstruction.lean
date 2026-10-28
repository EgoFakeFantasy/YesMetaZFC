import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomainStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.Separation.Enclosure

/-! # 内部有界指令的实际同层构造

标签使用模型中的唯一数码，三字段与指令码均由实际 rud 配对构造。语法容器
扩张保留全部旧指令与合法性；这为后续源公式递归编译提供实际集合代码。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem bop_mono_l {T U c i j k : M.Domain} (sub : M.MemberSubset T U) (tag : Nat)
    (h : Bop_d T tag c i j k) : Bop_d U tag c i j k := by
  obtain ⟨t,ht,v,hv,hn,trip,pair⟩ := h
  exact ⟨t,sub t ht,v,sub v hv,hn,trip,pair⟩

theorem bcase_mono_l {T U c A B D : M.Domain} (sub : M.MemberSubset T U) (tag : Nat)
    (h : Bcase_d T tag c A B D) : Bcase_d U tag c A B D := by
  obtain ⟨i,hi,j,hj,k,hk,hop,bounds⟩ := h
  exact ⟨i,sub i hi,j,sub j hj,k,sub k hk,bop_mono_l sub tag hop,bounds⟩

theorem bnode_mono_l {T U ω n r c : M.Domain} (sub : M.MemberSubset T U)
    (h : Bnode_d T ω n r c) : Bnode_d U ω n r c := by
  rcases h with h | h | h | h
  · exact Or.inl (bcase_mono_l sub 0 h)
  · exact Or.inr (Or.inl (bcase_mono_l sub 1 h))
  · exact Or.inr (Or.inr (Or.inl (bcase_mono_l sub 2 h)))
  · exact Or.inr (Or.inr (Or.inr (bcase_mono_l sub 3 h)))

theorem BoundedFormula_d.container_mono_l (hKP : M.Models KP) {T U ω n r F : M.Domain}
    (h : BoundedFormula_d T ω n r F) (sub : M.MemberSubset T U) : BoundedFormula_d U ω n r F := by
  refine ⟨h.variables,h.finite,h.ordinal,
    fn0_of_function_l hKP (function_codomain_mono_l (kp_pair_l hKP) sub (fn0_function_l hKP h.graph)),?_⟩
  intro i hi c _ hic
  exact bnode_mono_l sub (h.row i hi c (h.graph.bound_l hic).2 hic)

/-- 所有指令字段在同层时，构造真实代码并取得包含旧容器的新同层传递容器。 -/
theorem bop_in_rud_l (hKP : M.Models KP) {C T ω i j k : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    (hω : M.IsOmega ω) (hωC : M.mem ω C) (hTC : M.mem T C)
    (hiC : M.mem i C) (hjC : M.mem j C) (hkC : M.mem k C) (tag : Nat) :
    ∃ U c, M.mem U C ∧ M.TransitiveSet U ∧ M.MemberSubset T U ∧ M.mem c U ∧
      M.mem i U ∧ M.mem j U ∧ M.mem k U ∧ Bop_d U tag c i j k := by
  let I := kp_pair_l hKP
  obtain ⟨t,ht⟩ := num_exists_l hKP tag
  have htC := hc ω hωC t (num_mem_l hKP.1 hω ht)
  obtain ⟨q,hq⟩ := I.total j k
  obtain ⟨v,hv⟩ := I.total i q
  have trip : Rd_triple_d v i j k := ⟨q,hq,hv⟩
  have hvC := hC .triple i j k hiC hjC hkC v (rd_triple_value_l hKP.1 trip)
  obtain ⟨c,cpair⟩ := I.total t v
  have hcC := hC .opair t v t htC hvC htC c (rd_opair_value_l hKP.1 cpair)
  have members : ∀ x, x ∈ [T,i,j,k,t,v,c] → M.mem x C := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨B,hBC,hb,_⟩ := cover T hTC
  obtain ⟨U,hUC,hu,_,all⟩ := rd_finite_enclosed_l hKP hC hBC hb [T,i,j,k,t,v,c]
    (fun x hx => cover x (members x hx))
  have hTU := all T (by simp)
  exact ⟨U,c,hUC,hu,fun x hx => hu T hTU x hx,all c (by simp),
    all i (by simp),all j (by simp),all k (by simp),t,all t (by simp),v,all v (by simp),ht,trip,cpair⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
