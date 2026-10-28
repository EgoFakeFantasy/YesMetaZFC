import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ParameterAssignment
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentUpdate

/-! # 原内部有限参数前缀的双槽扩展 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure PrefixParameters_d (ω P x l s k X z f g params : M.Domain) : Prop where
  step1 : M.SuccessorOf s l
  step2 : M.SuccessorOf k s
  first : ParameterCheck_d ω l s X P z f
  second : ParameterCheck_d ω s k X f z g
  value : M.mem x X
  full : Fn0_d k X params
  update : ∀ j, M.mem j k → ∀ y, M.mem y X →
    (Rd_entry_d j y params ↔ (j = z ∧ y = x) ∨ (j ≠ z ∧ Rd_entry_d j y g))

def prefixParameters_m {d} (ω P x l s k X z f g params : Term d) : Formula 1 d :=
  .conj (KP.succ0_m s l) <| .conj (KP.succ0_m k s) <|
    .conj (parameterCheck_m ω l s X P z f) <| .conj (parameterCheck_m ω s k X f z g) <|
      .conj (.mem x X) <| .conj (fn0_m k X params) (updateCheck_m k X g z x params)
derive_free_closed prefixParameters_m

theorem prefixParameters_delta_l {d} (ω P x l s k X z f g params : Term d) :
    (prefixParameters_m ω P x l s k X z f g params).IsDelta0 :=
  .conj (KP.succ0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.conj (parameterCheck_delta_l ..)
    (.conj (parameterCheck_delta_l ..) (.conj (.mem _ _) (.conj (fn0_delta_l ..) (updateCheck_delta_l ..))))))

theorem prefixParameters_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω P x l s k X z f g params : Term d) :
    Formula.satisfies ρ (prefixParameters_m ω P x l s k X z f g params) ↔
      PrefixParameters_d (ω.eval ρ) (P.eval ρ) (x.eval ρ) (l.eval ρ) (s.eval ρ) (k.eval ρ)
        (X.eval ρ) (z.eval ρ) (f.eval ρ) (g.eval ρ) (params.eval ρ) := by
  simp only [prefixParameters_m,Formula.satisfies_conj_iff,KP.succ0_sat_l hKP.1,
    parameterCheck_sat_l hKP.1,Formula.satisfies_mem_iff,fn0_sat_l hKP.1,updateCheck_sat_l hKP]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩,
    fun h => ⟨h.step1,h.step2,h.first,h.second,h.value,h.full,h.update⟩⟩

theorem PrefixParameters_d.update_l (hZF : M.Models ZF) {ω P x l s k X z f g params : M.Domain}
    (hω : M.IsOmega ω) (cert : PrefixParameters_d ω P x l s k X z f g params) :
    Senv_update_d (kp_pair_l (ZF.modelsKP hZF)) g z x params :=
  (updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF))
    (fn0_function_l (ZF.modelsKP hZF) cert.second.full) (fn0_function_l (ZF.modelsKP hZF) cert.full)
    (cert.second.zero_l hZF hω).1 cert.value).mp cert.update

theorem PrefixParameters_d.unique_l (hZF : M.Models ZF)
    {ω P x l s k X z f g params l' s' k' Y z' f' g' other : M.Domain}
    (hω : M.IsOmega ω) (left : PrefixParameters_d ω P x l s k X z f g params)
    (right : PrefixParameters_d ω P x l' s' k' Y z' f' g' other) : params = other := by
  have eql := (fn0_function_l (ZF.modelsKP hZF) left.first.parameters).2.1.eq hZF.1
    (fn0_function_l (ZF.modelsKP hZF) right.first.parameters).2.1
  subst l'
  have eqs := hZF.1.eq_of_same_members s s' (fun v => (left.step1 v).trans (right.step1 v).symm)
  subst s'
  have eqk := hZF.1.eq_of_same_members k k' (fun v => (left.step2 v).trans (right.step2 v).symm)
  subst k'
  have eqz := num_unique_l hZF.1 left.first.zero right.first.zero
  subst z'
  have eqf := left.first.unique_l (ZF.modelsKP hZF) right.first
  subst f'
  have eqg := left.second.unique_l (ZF.modelsKP hZF) right.second
  subst g'
  exact senv_update_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 (left.update_l hZF hω) (right.update_l hZF hω)

theorem prefixParameters_exists_l (hZF : M.Models ZF) {ω P x l X z : M.Domain}
    (hω : M.IsOmega ω) (hl : M.mem l ω) (zero : Num_d 0 z)
    (hz : M.mem z X) (hx : M.mem x X) (pref : Fn0_d l X P) :
    ∃ s k f g params, PrefixParameters_d ω P x l s k X z f g params := by
  obtain ⟨s,hs,hsω⟩ := hω.1.2 l hl
  obtain ⟨k,hk,hkω⟩ := hω.1.2 s hsω
  obtain ⟨f,first⟩ := parameterCheck_exists_l hZF hω hsω hs.predecessor_mem zero hz pref
  obtain ⟨g,second⟩ := parameterCheck_exists_l hZF hω hkω hk.predecessor_mem zero hz first.full
  obtain ⟨params,update,full⟩ := senv_update_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF
    (fn0_function_l (ZF.modelsKP hZF) second.full) (second.zero_l hZF hω).1 hx
  exact ⟨s,k,f,g,params,hs,hk,first,second,hx,fn0_of_function_l (ZF.modelsKP hZF) full,
    (updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF)) (fn0_function_l (ZF.modelsKP hZF) second.full)
      full (second.zero_l hZF hω).1 hx).mpr update⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
