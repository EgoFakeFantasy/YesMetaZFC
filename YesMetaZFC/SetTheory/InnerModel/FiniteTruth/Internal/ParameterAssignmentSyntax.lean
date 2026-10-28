import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentRealization

/-! # 原参数列的规范完整寄存器赋值 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def ParameterIndex_d (k r : M.Domain) : Prop := ∃ j, M.mem j k ∧ M.SuccessorOf r j

def parameterIndex_m {d} (k r : Term d) : Formula 1 d := Formula.existsMem k (KP.succ0_m r.weaken .newest)
derive_free_closed parameterIndex_m

theorem parameterIndex_delta_l {d} (k r : Term d) : (parameterIndex_m k r).IsDelta0 := .existsMem _ (KP.succ0_delta_l ..)

theorem parameterIndex_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k r : Term d) :
    Formula.satisfies ρ (parameterIndex_m k r) ↔ ParameterIndex_d (k.eval ρ) (r.eval ρ) := by
  simp only [parameterIndex_m,ParameterIndex_d,Formula.satisfies_existsMem_iff,KP.succ0_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def ParameterSlot_d (k a z r y : M.Domain) : Prop :=
  (∃ j, M.mem j k ∧ M.SuccessorOf r j ∧ Rd_entry_d j y a) ∨ (¬ ParameterIndex_d k r ∧ y = z)

def parameterSlot_m {d} (k a z r y : Term d) : Formula 1 d :=
  .disj (Formula.existsMem k (.conj (KP.succ0_m r.weaken .newest) (rd_entry0_m .newest y.weaken a.weaken)))
    (.conj (.neg (parameterIndex_m k r)) (Formula.extensionalEq y z))
derive_free_closed parameterSlot_m

theorem parameterSlot_delta_l {d} (k a z r y : Term d) : (parameterSlot_m k a z r y).IsDelta0 :=
  .disj (.existsMem _ (.conj (KP.succ0_delta_l ..) (rd_entry0_delta_l ..)))
    (.conj (.neg (parameterIndex_delta_l ..)) (.atom _ _ _))

theorem parameterSlot_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k a z r y : Term d) :
    Formula.satisfies ρ (parameterSlot_m k a z r y) ↔ ParameterSlot_d (k.eval ρ) (a.eval ρ) (z.eval ρ) (r.eval ρ) (y.eval ρ) := by
  simp only [parameterSlot_m,ParameterSlot_d,Formula.satisfies_disj_iff,Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff,KP.succ0_sat_l hE,rd_entry0_sat_l hE,Formula.satisfies_neg_iff,
    parameterIndex_sat_l hE,Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

structure ParameterCheck_d (ω k n X a z f : M.Domain) : Prop where
  finite : M.mem n ω
  capacity : M.mem k n
  zero : Num_d 0 z
  inhabited : M.mem z X
  parameters : Fn0_d k X a
  full : Fn0_d n X f
  row : ∀ r, M.mem r n → ∀ y, M.mem y X → (Rd_entry_d r y f ↔ ParameterSlot_d k a z r y)

def parameterCheck_m {d} (ω k n X a z f : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (.mem k n) <| .conj (pc_num_m 0 z) <| .conj (.mem z X) <|
    .conj (fn0_m k X a) <| .conj (fn0_m n X f) <| Formula.forallMem n <| Formula.forallMem X.weaken <|
      .iff (rd_entry0_m (.bound 1) .newest f.weaken.weaken)
        (parameterSlot_m k.weaken.weaken a.weaken.weaken z.weaken.weaken (.bound 1) .newest)
derive_free_closed parameterCheck_m

theorem parameterCheck_delta_l {d} (ω k n X a z f : Term d) : (parameterCheck_m ω k n X a z f).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (pc_num_delta_l ..) (.conj (.mem _ _) (.conj (fn0_delta_l ..)
    (.conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (parameterSlot_delta_l ..)))))))))

theorem parameterCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω k n X a z f : Term d) :
    Formula.satisfies ρ (parameterCheck_m ω k n X a z f) ↔
      ParameterCheck_d (ω.eval ρ) (k.eval ρ) (n.eval ρ) (X.eval ρ) (a.eval ρ) (z.eval ρ) (f.eval ρ) := by
  simp only [parameterCheck_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,pc_num_sat_l hE,fn0_sat_l hE,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hE,parameterSlot_sat_l hE,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩,
    fun h => ⟨h.finite,h.capacity,h.zero,h.inhabited,h.parameters,h.full,h.row⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
