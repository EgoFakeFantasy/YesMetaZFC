import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignment

/-! # 固定原源模板的实际参数列及完整性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 固定模板宽度的内部数码域无额外位置；不限制一般内部有限程序。 -/
theorem sourceNum_member_l (hE : Extensional M) {d : Nat} {k r : M.Domain}
    (hk : Num_d d k) (hr : M.mem r k) : ∃ j : Fin d, Num_d j.val r := by
  induction d generalizing k with
  | zero => exact (hk r hr).elim
  | succ d ih =>
    obtain ⟨q,hq,hs⟩ := hk
    rcases (hs r).mp hr with hr | eq
    · obtain ⟨j,hj⟩ := ih hq hr
      exact ⟨j.castSucc,hj⟩
    · have eq := hE.eq_of_same_members r q eq
      subst r
      exact ⟨Fin.last d,hq⟩

theorem sourceNum_successor_l (hE : Extensional M) {d : Nat} {r j : M.Domain}
    (hr : Num_d (d+1) r) (hj : Num_d d j) : M.SuccessorOf r j := by
  obtain ⟨q,hq,hs⟩ := hr
  have eq := num_unique_l hE hq hj
  subst q
  exact hs

def SourceParameter_d {d} (values : Fin d → M.Domain) (a : M.Domain) : Prop :=
  ∀ j, ∃ t, Num_d j.val t ∧ Rd_entry_d t (values j) a

theorem sourceParameter_unique_l (hKP : M.Models KP) {d} {k X Y a b : M.Domain} {values : Fin d → M.Domain}
    (hk : Num_d d k) (ha : Fn0_d k X a) (hb : Fn0_d k Y b)
    (ca : SourceParameter_d values a) (cb : SourceParameter_d values b) : a = b := by
  have fa := fn0_function_l hKP ha
  have fb := fn0_function_l hKP hb
  have transfer {A B : M.Domain} (fA : M.IsSetFunctionFromTo (kp_pair_l hKP) A k X)
      (cA : SourceParameter_d values A) (cB : SourceParameter_d values B) {r y : M.Domain}
      (entry : Rd_entry_d r y A) : Rd_entry_d r y B := by
    obtain ⟨j,hj⟩ := sourceNum_member_l hKP.1 hk (fA.input_mem_of_pairMember entry)
    obtain ⟨t,ht,atA⟩ := cA j
    obtain ⟨s,hs,atB⟩ := cB j
    have eqt := num_unique_l hKP.1 ht hj
    have eqs := num_unique_l hKP.1 hs hj
    subst t; subst s
    have eq := fA.1.2 r y (values j) entry atA
    exact eq.symm ▸ atB
  apply fa.1.1.eq_of_pairMember_iff hKP.1 fb.1.1
  intro r y
  constructor
  · exact transfer fa ca cb
  · intro entry
    obtain ⟨j,hj⟩ := sourceNum_member_l hKP.1 hk (fb.input_mem_of_pairMember entry)
    obtain ⟨t,ht,atA⟩ := ca j
    obtain ⟨s,hs,atB⟩ := cb j
    have eqt := num_unique_l hKP.1 ht hj
    have eqs := num_unique_l hKP.1 hs hj
    subst t; subst s
    exact (fb.1.2 r y (values j) entry atB).symm ▸ atA

/-- 原源参数位置恰好进入规范完整图的后继寄存器。 -/
theorem parameterCheck_source_l (hZF : M.Models ZF) {d} {ω k n X a z f : M.Domain}
    {v : Fin (d+1) → M.Domain} {values : Fin d → M.Domain}
    (hω : M.IsOmega ω) (hk : Num_d d k) (slots : ∀ j, Num_d j.val (v j))
    (cert : ParameterCheck_d ω k n X a z f) (corr : SourceParameter_d values a) :
    z = v 0 ∧ ∀ j : Fin d, Rd_entry_d (v j.succ) (values j) f := by
  refine ⟨num_unique_l hZF.1 cert.zero (slots 0),fun j => ?_⟩
  obtain ⟨t,ht,entry⟩ := corr j
  have htK := num_lt_l hZF.1 ht hk j.isLt
  have hs := sourceNum_successor_l hZF.1 (slots j.succ) ht
  exact (cert.shift_l hZF hω htK hs entry).2

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
