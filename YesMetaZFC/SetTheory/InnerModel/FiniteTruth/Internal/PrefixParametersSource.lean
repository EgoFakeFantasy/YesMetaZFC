import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PrefixParameters
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SourceParameterSequence

/-! # 任意固定源的全部普通参数在双槽前缀中的逐项对应 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem PrefixParameters_d.source_l (hZF : M.Models ZF) {p}
    {ω P x l s k X z f g params : M.Domain}
    (hω : M.IsOmega ω) (cert : PrefixParameters_d ω P x l s k X z f g params)
    (hl : Num_d p l) {values : Fin p → M.Domain}
    (corr : SourceParameter_d values P) :
    SourceParameter_d (Fin.cases x (Fin.cases z values)) params := by
  have upd := PrefixParameters_d.update_l hZF hω cert
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · exact ⟨z,cert.first.zero,(upd.2 z x).mpr (Or.inl ⟨rfl,rfl⟩)⟩
  · obtain ⟨one,hone⟩ := num_exists_l (ZF.modelsKP hZF) 1
    have hs := sourceNum_successor_l hZF.1 hone cert.first.zero
    have atZero := cert.first.zero_l hZF hω
    have shifted := cert.second.shift_l hZF hω atZero.1 hs atZero.2
    have ne : one ≠ z := fun eq => cert.first.zero z (eq ▸ hs.predecessor_mem)
    exact ⟨one,hone,(upd.2 one z).mpr (Or.inr ⟨ne,shifted.2⟩)⟩
  · obtain ⟨t,ht,entry⟩ := corr i
    obtain ⟨t1,ht1⟩ := num_exists_l (ZF.modelsKP hZF) (i.val+1)
    obtain ⟨t2,ht2⟩ := num_exists_l (ZF.modelsKP hZF) (i.val+2)
    have hs1 := sourceNum_successor_l hZF.1 ht1 ht
    have first := cert.first.shift_l hZF hω (num_lt_l hZF.1 ht hl i.isLt) hs1 entry
    have hs2 := sourceNum_successor_l hZF.1 ht2 ht1
    have second := cert.second.shift_l hZF hω first.1 hs2 first.2
    have ne : t2 ≠ z := fun eq => cert.first.zero t1 (eq ▸ hs2.predecessor_mem)
    exact ⟨t2,ht2,(upd.2 t2 (values i)).mpr (Or.inr ⟨ne,second.2⟩)⟩

theorem PrefixParameters_d.count_l {p} {ω P x l s k X z f g params : M.Domain}
    (cert : PrefixParameters_d (M := M) ω P x l s k X z f g params) (hl : Num_d p l) :
    Num_d (p+2) k := ⟨s,⟨l,hl,cert.step1⟩,cert.step2⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
