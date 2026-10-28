import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgram

/-! # 赋值图之外的一元谓词查询与准确迹局部化 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PredicateAtom_d (A X f i : M.Domain) : Prop := ∃ a, M.mem a X ∧ Rd_entry_d i a f ∧ M.mem a A

def predicateAtom_m {d} (A X f i : Term d) : Formula 1 d :=
  Formula.existsMem X <| .conj (rd_entry0_m i.weaken .newest f.weaken) (.mem .newest A.weaken)

@[simp] theorem predicateAtom_closed_l {d} (A X f i : Term d)
    (hA : A.freeSupport = []) (hX : X.freeSupport = []) (hf : f.freeSupport = []) (hi : i.freeSupport = []) :
    (predicateAtom_m A X f i).FreeClosed := by
  simp -implicitDefEqProofs [predicateAtom_m,Definitional.Formula.FreeClosed,hA,hX,hf,hi]

theorem predicateAtom_delta_l {d} (A X f i : Term d) : (predicateAtom_m A X f i).IsDelta0 :=
  .existsMem _ (.conj (rd_entry0_delta_l ..) (.mem _ _))

theorem predicateAtom_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A X f i : Term d) :
    Formula.satisfies ρ (predicateAtom_m A X f i) ↔ PredicateAtom_d (A.eval ρ) (X.eval ρ) (f.eval ρ) (i.eval ρ) := by
  simp only [predicateAtom_m,PredicateAtom_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

def PredicateQuery_d (T A X c f : M.Domain) : Prop :=
  ∃ i, M.mem i T ∧ ∃ j, M.mem j T ∧ ∃ k, M.mem k T ∧ Bop_d T 4 c i j k ∧ PredicateAtom_d A X f i

def predicateQuery_m {d} (T A X c f : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem T.weaken <| Formula.existsMem T.weaken.weaken <|
    .conj (bop_m T.weaken.weaken.weaken 4 c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
      (predicateAtom_m A.weaken.weaken.weaken X.weaken.weaken.weaken f.weaken.weaken.weaken (.bound 2))

@[simp] theorem predicateQuery_closed_l {d} (T A X c f : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hX : X.freeSupport = [])
    (hc : c.freeSupport = []) (hf : f.freeSupport = []) : (predicateQuery_m T A X c f).FreeClosed := by
  simp -implicitDefEqProofs [predicateQuery_m,Definitional.Formula.FreeClosed,hT,hA,hX,hc,hf]

theorem predicateQuery_delta_l {d} (T A X c f : Term d) : (predicateQuery_m T A X c f).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (bop_delta_l ..) (predicateAtom_delta_l ..))))

theorem predicateQuery_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A X c f : Term d) :
    Formula.satisfies ρ (predicateQuery_m T A X c f) ↔
      PredicateQuery_d (T.eval ρ) (A.eval ρ) (X.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [predicateQuery_m,PredicateQuery_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    bop_sat_l hE,predicateAtom_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def PtruthNode_d (T A n X E H c f : M.Domain) : Prop := BtruthNode_d T n X E H c f ∨ PredicateQuery_d T A X c f

def ptruthNode_m {d} (T A n X E H c f : Term d) : Formula 1 d :=
  .disj (btruthNode_m T n X E H c f) (predicateQuery_m T A X c f)

@[simp] theorem ptruthNode_closed_l {d} (T A n X E H c f : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hH : H.freeSupport = []) (hc : c.freeSupport = []) (hf : f.freeSupport = []) :
    (ptruthNode_m T A n X E H c f).FreeClosed := by
  simp -implicitDefEqProofs [ptruthNode_m,Definitional.Formula.FreeClosed,hT,hA,hn,hX,hE,hH,hc,hf]

theorem ptruthNode_delta_l {d} (T A n X E H c f : Term d) : (ptruthNode_m T A n X E H c f).IsDelta0 :=
  .disj (btruthNode_delta_l ..) (predicateQuery_delta_l ..)

theorem ptruthNode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A n X E H c f : Term d) :
    Formula.satisfies ρ (ptruthNode_m T A n X E H c f) ↔
      PtruthNode_d (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [ptruthNode_m,PtruthNode_d,Formula.satisfies_disj_iff,btruthNode_sat_l hE,predicateQuery_sat_l hE]

theorem predicateAtom_trace_l {A B X f i : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PredicateAtom_d A X f i ↔ PredicateAtom_d B X f i := by
  constructor
  · rintro ⟨a,ha,read,hit⟩
    exact ⟨a,ha,read,(trace a).mpr ⟨ha,hit⟩⟩
  · rintro ⟨a,ha,read,hit⟩
    exact ⟨a,ha,read,((trace a).mp hit).2⟩

theorem predicateQuery_trace_l {T A B X c f : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PredicateQuery_d T A X c f ↔ PredicateQuery_d T B X c f := by
  simp only [PredicateQuery_d,predicateAtom_trace_l trace]

theorem ptruthNode_trace_l {T A B n X E H c f : M.Domain} (trace : YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTrace_d A X B) :
    PtruthNode_d T A n X E H c f ↔ PtruthNode_d T B n X E H c f :=
  or_congr Iff.rfl (predicateQuery_trace_l trace)

theorem predicateQuery_decode_l (hKP : M.Models KP) {T A X c f i j k : M.Domain}
    (hi : M.mem i T) (hj : M.mem j T) (hk : M.mem k T) (code : Bop_d T 4 c i j k) :
    PredicateQuery_d T A X c f ↔ PredicateAtom_d A X f i := by
  constructor
  · rintro ⟨a,_,b,_,d,_,other,hit⟩
    obtain ⟨_,rfl,rfl,rfl⟩ := bop_injective_l hKP code other
    exact hit
  · exact fun hit => ⟨i,hi,j,hj,k,hk,code,hit⟩

theorem ptruthNode_predicate_l (hKP : M.Models KP) {T A n X E H c f i j k : M.Domain}
    (hi : M.mem i T) (hj : M.mem j T) (hk : M.mem k T) (code : Bop_d T 4 c i j k) :
    PtruthNode_d T A n X E H c f ↔ PredicateAtom_d A X f i := by
  have noOld : ¬ BtruthNode_d T n X E H c f := by
    rintro ⟨tag,a,_,b,_,d,_,old,_⟩
    have eq := (bop_injective_l hKP code old).1
    have small := tag.isLt
    omega
  exact ⟨fun hit => hit.elim (fun old => (noOld old).elim) ((predicateQuery_decode_l hKP hi hj hk code).mp),
    fun hit => Or.inr ((predicateQuery_decode_l hKP hi hj hk code).mpr hit)⟩

theorem ptruthNode_legacy_l (hKP : M.Models KP) {T A ω n X E H r c f : M.Domain}
    (valid : Bnode_d T ω n r c) : PtruthNode_d T A n X E H c f ↔ BtruthNode_d T n X E H c f := by
  have one (tag : Nat) (small : tag < 4) {U V W : M.Domain} (node : Bcase_d T tag c U V W) :
      ¬ PredicateQuery_d T A X c f := by
    obtain ⟨i,_,j,_,k,_,code,_⟩ := node
    rintro ⟨a,_,b,_,d,_,other,_⟩
    have eq := (bop_injective_l hKP code other).1
    omega
  have noQuery : ¬ PredicateQuery_d T A X c f := by
    rcases valid with zero | oneCase | two | three
    · exact one 0 (by decide) zero
    · exact one 1 (by decide) oneCase
    · exact one 2 (by decide) two
    · exact one 3 (by decide) three
  exact ⟨fun hit => hit.elim id (fun query => (noQuery query).elim),Or.inl⟩

theorem ptruthNode_restriction_l (hKP : M.Models KP) {T A ω n X E P H r c f : M.Domain}
    (pref : M.IsRestrictionOf (kp_pair_l hKP) P H r) (valid : Pnode_d T ω n r c) :
    PtruthNode_d T A n X E P c f ↔ PtruthNode_d T A n X E H c f := by
  rcases valid with old | predicate
  · exact (ptruthNode_legacy_l hKP old).trans ((btruthNode_restriction_l hKP pref old).trans
      (ptruthNode_legacy_l hKP old).symm)
  · obtain ⟨i,hi,j,hj,k,hk,code,_⟩ := predicate
    exact (ptruthNode_predicate_l hKP hi hj hk code).trans (ptruthNode_predicate_l hKP hi hj hk code).symm

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
