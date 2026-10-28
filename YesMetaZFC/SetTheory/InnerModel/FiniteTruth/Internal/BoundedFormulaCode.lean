import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentUpdate
import YesMetaZFC.SetTheory.InnerModel.ProofCode.Syntax
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 内部有界公式程序的统一合法性

指令采用 (标签,(i,(j,k)))。四个标签分别表示隶属、相等、或非、有界存在量词。
前三类的第三字段仅作自然数占位；有界存在指令读变量 i、界变量 j 及较早子行 k。
所有程序长度与变量编号均为模型内对象，尚不在这里断言统一真值正确性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal

universe u
variable {M : SetTheory.Structure.{u}}

def Bop_d (T : M.Domain) (tag : Nat) (c i j k : M.Domain) : Prop :=
  ∃ t, M.mem t T ∧ ∃ v, M.mem v T ∧
    Num_d tag t ∧ Rd_triple_d v i j k ∧ KPair_d M c t v

def bop_m {d} (T : Term d) (tag : Nat) (c i j k : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem T.weaken <|
    .conj (pc_num_m tag (.bound 1)) <|
      .conj (rd_triple0_m .newest i.weaken.weaken j.weaken.weaken k.weaken.weaken)
        (kpair0_m c.weaken.weaken (.bound 1) .newest)
derive_free_closed bop_m

theorem bop_delta_l {d} (T : Term d) (tag : Nat) (c i j k : Term d) :
    (bop_m T tag c i j k).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (pc_num_delta_l ..)
    (.conj (rd_triple0_delta_l ..) (kpair0_delta_l ..))))

theorem bop_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T : Term d) (tag : Nat)
    (c i j k : Term d) :
    Formula.satisfies ρ (bop_m T tag c i j k) ↔
      Bop_d (T.eval ρ) tag (c.eval ρ) (i.eval ρ) (j.eval ρ) (k.eval ρ) := by
  simp only [bop_m, Bop_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_num_sat_l hE, rd_triple0_sat_l hE, kpair0_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem bop_injective_l (hKP : M.Models KP) {T U c i j k a b d : M.Domain} {tag other : Nat}
    (h : Bop_d T tag c i j k) (g : Bop_d U other c a b d) :
    tag = other ∧ i = a ∧ j = b ∧ k = d := by
  obtain ⟨t, _, v, _, ht, hv, hc⟩ := h
  obtain ⟨s, _, w, _, hs, hw, hd⟩ := g
  obtain ⟨he, hf⟩ := kpair_injective_l M hc hd
  subst s
  subst w
  exact ⟨num_injective_l hKP ht hs, pc_triple_inj_l hv hw⟩

def Bcase_d (T : M.Domain) (tag : Nat) (c A B D : M.Domain) : Prop :=
  ∃ i, M.mem i T ∧ ∃ j, M.mem j T ∧ ∃ k, M.mem k T ∧
    Bop_d T tag c i j k ∧ M.mem i A ∧ M.mem j B ∧ M.mem k D

private def bcase_m {d} (T : Term d) (tag : Nat) (c A B D : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem T.weaken <| Formula.existsMem T.weaken.weaken <|
    .conj (bop_m T.weaken.weaken.weaken tag c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) <|
      .conj (.mem (.bound 2) A.weaken.weaken.weaken) <|
        .conj (.mem (.bound 1) B.weaken.weaken.weaken) (.mem .newest D.weaken.weaken.weaken)
derive_free_closed bcase_m

private theorem bcase_delta_l {d} (T : Term d) (tag : Nat) (c A B D : Term d) :
    (bcase_m T tag c A B D).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _
    (.conj (bop_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))

private theorem bcase_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T : Term d) (tag : Nat)
    (c A B D : Term d) :
    Formula.satisfies ρ (bcase_m T tag c A B D) ↔
      Bcase_d (T.eval ρ) tag (c.eval ρ) (A.eval ρ) (B.eval ρ) (D.eval ρ) := by
  simp only [bcase_m, Bcase_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, bop_sat_l hE,
    Formula.satisfies_mem_iff, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

def Bnode_d (T ω arity row c : M.Domain) : Prop :=
  Bcase_d T 0 c arity arity ω ∨ Bcase_d T 1 c arity arity ω ∨
    Bcase_d T 2 c row row ω ∨ Bcase_d T 3 c arity arity row

def bnode_m {d} (T ω arity row c : Term d) : Formula 1 d :=
  .disj (bcase_m T 0 c arity arity ω) <| .disj (bcase_m T 1 c arity arity ω) <|
    .disj (bcase_m T 2 c row row ω) (bcase_m T 3 c arity arity row)
derive_free_closed bnode_m

theorem bnode_delta_l {d} (T ω arity row c : Term d) : (bnode_m T ω arity row c).IsDelta0 :=
  .disj (bcase_delta_l ..) (.disj (bcase_delta_l ..) (.disj (bcase_delta_l ..) (bcase_delta_l ..)))

theorem bnode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T ω arity row c : Term d) :
    Formula.satisfies ρ (bnode_m T ω arity row c) ↔
      Bnode_d (T.eval ρ) (ω.eval ρ) (arity.eval ρ) (row.eval ρ) (c.eval ρ) := by
  simp only [bnode_m, Bnode_d, Formula.satisfies_disj_iff, bcase_sat_l hE]

structure BoundedFormula_d (T ω arity length F : M.Domain) : Prop where
  variables : M.mem arity ω
  finite : M.mem length ω
  ordinal : M.IsOrdinal length
  graph : Fn0_d length T F
  row : ∀ r, M.mem r length → ∀ c, M.mem c T → Rd_entry_d r c F → Bnode_d T ω arity r c

def boundedFormula_m {d} (T ω arity length F : Term d) : Formula 1 d :=
  .conj (.mem arity ω) <| .conj (.mem length ω) <| .conj (KP.ord0_m length) <|
    .conj (fn0_m length T F) <| Formula.forallMem length <| Formula.forallMem T.weaken <|
      .imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
        (bnode_m T.weaken.weaken ω.weaken.weaken arity.weaken.weaken (.bound 1) .newest)
derive_free_closed boundedFormula_m

theorem boundedFormula_delta_l {d} (T ω arity length F : Term d) :
    (boundedFormula_m T ω arity length F).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.conj (KP.ord0_delta_l _)
    (.conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (bnode_delta_l ..)))))))

theorem boundedFormula_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω arity length F : Term d) :
    Formula.satisfies ρ (boundedFormula_m T ω arity length F) ↔
      BoundedFormula_d (T.eval ρ) (ω.eval ρ) (arity.eval ρ) (length.eval ρ) (F.eval ρ) := by
  simp only [boundedFormula_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    KP.ord0_sat_l hKP, fn0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, bnode_sat_l hKP.1,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.variables, h.finite, h.ordinal, h.graph, h.row⟩⟩

theorem BoundedFormula_d.at_l {T ω arity length F r c : M.Domain}
    (h : BoundedFormula_d T ω arity length F) (hc : Rd_entry_d r c F) :
    M.mem r length ∧ M.mem c T ∧ Bnode_d T ω arity r c := by
  have bounds := h.graph.bound_l hc
  exact ⟨bounds.1, bounds.2, h.row r bounds.1 c bounds.2 hc⟩

/-- 空程序是合法的内部有限程序；变量数仍由内部 ω 给出。 -/
theorem boundedFormula_empty_l {T ω arity e : M.Domain}
    (ha : M.mem arity ω) (heω : M.mem e ω) (he : ∀ p, ¬ M.mem p e) :
    BoundedFormula_d T ω arity e e := by
  refine ⟨ha, heω, Structure.IsOrdinal.of_no_members he, ?_, ?_⟩
  · exact ⟨fun p hp => (he p hp).elim, fun r hr => (he r hr).elim, fun r hr => (he r hr).elim⟩
  · exact fun r hr => (he r hr).elim

/-- 追加一条只读较早子行的合法指令，得到原图的实际后继程序。 -/
theorem BoundedFormula_d.append_l (hKP : M.Models KP) {T ω arity length F c s : M.Domain}
    (h : BoundedFormula_d T ω arity length F) (hc : M.mem c T)
    (hnew : Bnode_d T ω arity length c) (hsω : M.mem s ω)
    (hs : M.IsOrdinal s) (hls : M.SuccessorOf s length) :
    ∃ G, BoundedFormula_d T ω arity s G ∧
      ∀ r d, Rd_entry_d r d G ↔ Rd_entry_d r d F ∨ (r = length ∧ d = c) := by
  let I := kp_pair_l hKP
  have hf := fn0_function_l hKP h.graph
  obtain ⟨G, hg, he⟩ := Structure.IsSequenceOfLength.exists_append hKP I
    (show M.IsSequenceOfLength I F length from ⟨h.ordinal, hf.1, hf.2.1⟩) hs hls (value := c)
  have hgfn : M.IsSetFunctionFromTo I G s T := by
    refine ⟨hg.2.1, hg.2.2, ?_⟩
    intro r hr
    obtain ⟨d, hd⟩ := (hg.2.2 r).mp hr
    exact ⟨d, ((he r d).mp hd).elim (fun old => (h.graph.bound_l old).2) (fun new => new.2 ▸ hc), hd⟩
  refine ⟨G, ⟨h.variables, hsω, hs, fn0_of_function_l hKP hgfn, ?_⟩, he⟩
  intro r _ d hd hrd
  rcases (he r d).mp hrd with old | ⟨rfl, rfl⟩
  · exact h.row r (h.graph.bound_l old).1 d hd old
  · exact hnew

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
