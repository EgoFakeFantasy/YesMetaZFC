import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteAssignmentSpace
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthNode
import YesMetaZFC.SetTheory.KP.Natural

/-! # 完整有限赋值空间的有界证书语法

证书显式保存长度 0 到 n 的空间表。每行成员都核验为实际函数，零行包含空函数，
每个旧函数及新值的追加都在后继行中出现；这些检查均为实际 Δ₀ 公式。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def SnocCheck_d (f n x g : M.Domain) : Prop := M.MemberSubset f g ∧ Rd_entry_d n x g ∧
  ∀ p, M.mem p g → M.mem p f ∨ KPair_d M p n x

def snocCheck_m {d} (f n x g : Term d) : Formula 1 d :=
  .conj (Formula.subset f g) (.conj (rd_entry0_m n x g)
    (Formula.forallMem g (.disj (.mem .newest f.weaken) (kpair0_m .newest n.weaken x.weaken))))
derive_free_closed snocCheck_m

theorem snocCheck_delta_l {d} (f n x g : Term d) : (snocCheck_m f n x g).IsDelta0 :=
  .conj (.atom _ _ _) (.conj (rd_entry0_delta_l ..) (.forallMem _ (.disj (.mem _ _) (kpair0_delta_l ..))))

theorem snocCheck_sat_l (hE : Extensional M) {d} (ρ : Env M d) (f n x g : Term d) :
    Formula.satisfies ρ (snocCheck_m f n x g) ↔ SnocCheck_d (f.eval ρ) (n.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [snocCheck_m, SnocCheck_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    rd_entry0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, kpair0_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem snocCheck_correct_l (hKP : M.Models KP) {f n x g : M.Domain} :
    SnocCheck_d f n x g ↔ Snoc_d (kp_pair_l hKP) f n x g := by
  constructor
  · rintro ⟨sub, ⟨q, hq, hqg⟩, check⟩ p
    constructor
    · exact check p
    · rintro (hpf | hpn)
      · exact sub p hpf
      · exact ((kp_pair_l hKP).unique hpn hq).symm ▸ hqg
  · intro snoc
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total n x
    exact ⟨fun p hp => (snoc p).mpr (Or.inl hp), ⟨p, hp, (snoc p).mpr (Or.inr hp)⟩,
      fun p hp => (snoc p).mp hp⟩

def SpaceRows_d (s X Z S : M.Domain) : Prop := ∀ r, M.mem r s → ∀ A, M.mem A Z →
  Rd_entry_d r A S → ∀ f, M.mem f A → Fn0_d r X f

def spaceRows_m {d} (s X Z S : Term d) : Formula 1 d :=
  Formula.forallMem s <| Formula.forallMem Z.weaken <|
    .imp (rd_entry0_m (.bound 1) .newest S.weaken.weaken) <|
      Formula.forallMem .newest (fn0_m (.bound 2) X.weaken.weaken.weaken .newest)
derive_free_closed spaceRows_m

theorem spaceRows_delta_l {d} (s X Z S : Term d) : (spaceRows_m s X Z S).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.forallMem _ (fn0_delta_l ..))))

theorem spaceRows_sat_l (hE : Extensional M) {d} (ρ : Env M d) (s X Z S : Term d) :
    Formula.satisfies ρ (spaceRows_m s X Z S) ↔ SpaceRows_d (s.eval ρ) (X.eval ρ) (Z.eval ρ) (S.eval ρ) := by
  simp only [spaceRows_m, SpaceRows_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, fn0_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

def SpaceBase_d (e Z S : M.Domain) : Prop := ∀ A, M.mem A Z → Rd_entry_d e A S → M.mem e A

def spaceBase_m {d} (e Z S : Term d) : Formula 1 d := Formula.forallMem Z
  (.imp (rd_entry0_m e.weaken .newest S.weaken) (.mem e.weaken .newest))
derive_free_closed spaceBase_m

theorem spaceBase_delta_l {d} (e Z S : Term d) : (spaceBase_m e Z S).IsDelta0 :=
  .forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _))

theorem spaceBase_sat_l (hE : Extensional M) {d} (ρ : Env M d) (e Z S : Term d) :
    Formula.satisfies ρ (spaceBase_m e Z S) ↔ SpaceBase_d (e.eval ρ) (Z.eval ρ) (S.eval ρ) := by
  simp only [spaceBase_m, SpaceBase_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

def SpaceStep_d (n s X Z S : M.Domain) : Prop := ∀ r, M.mem r n → ∀ t, M.mem t s →
  M.SuccessorOf t r → ∀ A, M.mem A Z → Rd_entry_d r A S → ∀ B, M.mem B Z → Rd_entry_d t B S →
    ∀ f, M.mem f A → ∀ x, M.mem x X → ∃ g, M.mem g B ∧ SnocCheck_d f r x g

def spaceStep_m {d} (n s X Z S : Term d) : Formula 1 d :=
  Formula.forallMem n <| Formula.forallMem s.weaken <|
    .imp (KP.succ0_m .newest (.bound 1)) <| Formula.forallMem Z.weaken.weaken <|
      .imp (rd_entry0_m (.bound 2) .newest S.weaken.weaken.weaken) <|
        Formula.forallMem Z.weaken.weaken.weaken <|
          .imp (rd_entry0_m (.bound 2) .newest S.weaken.weaken.weaken.weaken) <|
            Formula.forallMem (.bound 1) <| Formula.forallMem X.weaken.weaken.weaken.weaken.weaken <|
              Formula.existsMem (.bound 2) (snocCheck_m (.bound 2) (.bound 6) (.bound 1) .newest)
derive_free_closed spaceStep_m

theorem spaceStep_delta_l {d} (n s X Z S : Term d) : (spaceStep_m n s X Z S).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (KP.succ0_delta_l ..) (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.forallMem _ (.imp (rd_entry0_delta_l ..) (.forallMem _ (.forallMem _ (.existsMem _ (snocCheck_delta_l ..))))))))))

theorem spaceStep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n s X Z S : Term d) :
    Formula.satisfies ρ (spaceStep_m n s X Z S) ↔
      SpaceStep_d (n.eval ρ) (s.eval ρ) (X.eval ρ) (Z.eval ρ) (S.eval ρ) := by
  simp only [spaceStep_m, SpaceStep_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    KP.succ0_sat_l hE, rd_entry0_sat_l hE, Formula.satisfies_existsMem_iff, snocCheck_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

structure AssignmentSpaceCert_d (ω n X e s Z S E : M.Domain) : Prop where
  finite : M.mem n ω
  zero : ∀ p, ¬ M.mem p e
  successor : M.SuccessorOf s n
  table : Fn0_d s Z S
  output : Rd_entry_d n E S
  typed : SpaceRows_d s X Z S
  base : SpaceBase_d e Z S
  step : SpaceStep_d n s X Z S

def assignmentSpaceCert_m {d} (ω n X e s Z S E : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (Formula.forallMem e .falsum) <| .conj (KP.succ0_m s n) <|
    .conj (fn0_m s Z S) <| .conj (rd_entry0_m n E S) <| .conj (spaceRows_m s X Z S) <|
      .conj (spaceBase_m e Z S) (spaceStep_m n s X Z S)
derive_free_closed assignmentSpaceCert_m

theorem assignmentSpaceCert_delta_l {d} (ω n X e s Z S E : Term d) :
    (assignmentSpaceCert_m ω n X e s Z S E).IsDelta0 :=
  .conj (.mem _ _) (.conj (.forallMem _ .falsum) (.conj (KP.succ0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (spaceRows_delta_l ..)
      (.conj (spaceBase_delta_l ..) (spaceStep_delta_l ..)))))))

theorem assignmentSpaceCert_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n X e s Z S E : Term d) :
    Formula.satisfies ρ (assignmentSpaceCert_m ω n X e s Z S E) ↔
      AssignmentSpaceCert_d (ω.eval ρ) (n.eval ρ) (X.eval ρ) (e.eval ρ) (s.eval ρ) (Z.eval ρ) (S.eval ρ) (E.eval ρ) := by
  simp only [assignmentSpaceCert_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, KP.succ0_sat_l hE,
    fn0_sat_l hE, rd_entry0_sat_l hE, spaceRows_sat_l hE, spaceBase_sat_l hE, spaceStep_sat_l hE]
  constructor
  · rintro ⟨a,b,c,d,e,f,g,h⟩
    exact ⟨a,b,c,d,e,f,g,h⟩
  · intro h
    exact ⟨h.finite,h.zero,h.successor,h.table,h.output,h.typed,h.base,h.step⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
