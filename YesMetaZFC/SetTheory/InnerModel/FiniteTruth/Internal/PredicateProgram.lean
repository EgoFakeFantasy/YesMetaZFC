import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateUniformizationObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthCertificate

/-! # 原内部程序编码的一元谓词只读指令

复用原 Bop_d；标签 4 查询当前赋值的 i 坐标是否属于 A。
A 不进入赋值图。原四类指令、原函数图及内部有限长度原样保留。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def predicateCode_m {d} (T ω n c : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem T.weaken <| Formula.existsMem T.weaken.weaken <|
    .conj (bop_m T.weaken.weaken.weaken 4 c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) <|
      .conj (.mem (.bound 2) n.weaken.weaken.weaken) <|
        .conj (.mem (.bound 1) ω.weaken.weaken.weaken) (.mem .newest ω.weaken.weaken.weaken)

@[simp] theorem predicateCode_closed_l {d} (T ω n c : Term d)
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : n.freeSupport = []) (hc : c.freeSupport = []) :
    (predicateCode_m T ω n c).FreeClosed := by
  simp -implicitDefEqProofs [predicateCode_m,Definitional.Formula.FreeClosed,hT,hω,hn,hc]

theorem predicateCode_delta_l {d} (T ω n c : Term d) : (predicateCode_m T ω n c).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))

theorem predicateCode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T ω n c : Term d) :
    Formula.satisfies ρ (predicateCode_m T ω n c) ↔ Bcase_d (T.eval ρ) 4 (c.eval ρ) (n.eval ρ) (ω.eval ρ) (ω.eval ρ) := by
  simp only [predicateCode_m,Bcase_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    bop_sat_l hE,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def Pnode_d (T ω n r c : M.Domain) : Prop := Bnode_d T ω n r c ∨ Bcase_d T 4 c n ω ω

def pnode_m {d} (T ω n r c : Term d) : Formula 1 d :=
  .disj (bnode_m T ω n r c) (predicateCode_m T ω n c)

@[simp] theorem pnode_closed_l {d} (T ω n r c : Term d)
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : n.freeSupport = [])
    (hr : r.freeSupport = []) (hc : c.freeSupport = []) : (pnode_m T ω n r c).FreeClosed := by
  simp -implicitDefEqProofs [pnode_m,Definitional.Formula.FreeClosed,hT,hω,hn,hr,hc]

theorem pnode_delta_l {d} (T ω n r c : Term d) : (pnode_m T ω n r c).IsDelta0 :=
  .disj (bnode_delta_l ..) (predicateCode_delta_l ..)

theorem pnode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T ω n r c : Term d) :
    Formula.satisfies ρ (pnode_m T ω n r c) ↔ Pnode_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [pnode_m,Pnode_d,Formula.satisfies_disj_iff,bnode_sat_l hE,predicateCode_sat_l hE]

structure PBoundedFormula_d (T ω n length F : M.Domain) : Prop where
  variables : M.mem n ω
  finite : M.mem length ω
  ordinal : M.IsOrdinal length
  graph : Fn0_d length T F
  row : ∀ r, M.mem r length → ∀ c, M.mem c T → Rd_entry_d r c F → Pnode_d T ω n r c

def pboundedFormula_m {d} (T ω n length F : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (.mem length ω) <| .conj (KP.ord0_m length) <|
    .conj (fn0_m length T F) <| Formula.forallMem length <| Formula.forallMem T.weaken <|
      .imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
        (pnode_m T.weaken.weaken ω.weaken.weaken n.weaken.weaken (.bound 1) .newest)

@[simp] theorem pboundedFormula_closed_l {d} (T ω n length F : Term d)
    (hT : T.freeSupport = []) (hω : ω.freeSupport = []) (hn : n.freeSupport = [])
    (hl : length.freeSupport = []) (hF : F.freeSupport = []) : (pboundedFormula_m T ω n length F).FreeClosed := by
  simp -implicitDefEqProofs [pboundedFormula_m,Definitional.Formula.FreeClosed,hT,hω,hn,hl,hF]

theorem pboundedFormula_delta_l {d} (T ω n length F : Term d) : (pboundedFormula_m T ω n length F).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (KP.ord0_delta_l _)
    (.conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (pnode_delta_l ..)))))))

theorem pboundedFormula_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n length F : Term d) :
    Formula.satisfies ρ (pboundedFormula_m T ω n length F) ↔
      PBoundedFormula_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (length.eval ρ) (F.eval ρ) := by
  simp only [pboundedFormula_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,KP.ord0_sat_l hKP,
    fn0_sat_l hKP.1,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hKP.1,
    pnode_sat_l hKP.1,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.variables,h.finite,h.ordinal,h.graph,h.row⟩⟩

theorem BoundedFormula_d.predicate_l {T ω n L F : M.Domain} (h : BoundedFormula_d T ω n L F) :
    PBoundedFormula_d T ω n L F := ⟨h.variables,h.finite,h.ordinal,h.graph,fun r hr c hc entry => Or.inl (h.row r hr c hc entry)⟩

theorem PBoundedFormula_d.at_l {T ω n L F r c : M.Domain} (h : PBoundedFormula_d T ω n L F)
    (entry : Rd_entry_d r c F) : M.mem r L ∧ M.mem c T ∧ Pnode_d T ω n r c :=
  ⟨(h.graph.bound_l entry).1,(h.graph.bound_l entry).2,h.row r (h.graph.bound_l entry).1 c (h.graph.bound_l entry).2 entry⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
