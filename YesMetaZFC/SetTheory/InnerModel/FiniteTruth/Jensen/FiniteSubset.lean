import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProgramNumber
import YesMetaZFC.SetTheory.Card.Finite

/-! # 原 J 层包含其集合的全部内部有限子集

归纳谓词是原对象公式，用背景 ZF 分离支持上游内部有限集合归纳。
不把模型内部有限集合替换为宿主有限列表，不假设小层 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 原层包含其全部模型内有限子集；无需另给一个层内共同值域。 -/
theorem jh_finite_members_mem_l (hZF : M.Models ZF) {a C ω X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω X) (sub : M.MemberSubset X C) : M.mem X C := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  let ρ : Env M 1 := ⟨fun _ => C,fun _ => C⟩
  let φ : UnarySchema 1 := { body := .imp (Formula.subset .newest (.bound 1)) (.mem .newest (.bound 1)) }
  have sat A : φ.denote ρ A ↔ (M.MemberSubset A C → M.mem A C) := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_imp_iff,Formula.satisfies_subset_iff,Formula.satisfies_mem_iff]
    rfl
  have all := ZF.finite_ind_l I hZF hω φ ρ (by
    intro E empty
    apply (sat E).mpr
    intro _
    obtain ⟨D,hDC,hD⟩ := closed.exists_l hKP .diff hωC hωC hωC
    have eq : E = D := hZF.1.eq_of_same_members E D (fun x =>
      iff_of_false (empty x) (fun hx => (hD x).mp hx |>.elim fun hp hn => hn hp))
    exact eq ▸ hDC) (by
      intro A x D _ ih inserted
      apply (sat D).mpr
      intro hDC
      have hAC := (sat A).mp ih (fun y hy => hDC y ((inserted y).mpr (Or.inl hy)))
      have hxC := hDC x ((inserted x).mpr (Or.inr rfl))
      obtain ⟨E,hEC,hE⟩ := rd_insert_closed_l hKP closed hAC hxC
      have eq := hZF.1.eq_of_same_members D E (fun y => (inserted y).trans (hE y).symm)
      exact eq ▸ hEC)
  exact (sat X).mp (all X finite) sub

theorem jh_finite_subset_mem_l (hZF : M.Models ZF) {a C ω U X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hUC : M.mem U C)
    (finite : Finite_d (kp_pair_l (ZF.modelsKP hZF)) ω X) (sub : M.MemberSubset X U) : M.mem X C :=
  jh_finite_members_mem_l hZF ha h hω hωC finite
    (fun x hx => jh_value_transitive_l (ZF.models_kpi_l hZF) h U hUC x (sub x hx))

private def jensenFiniteSubsetsBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 4)) <| .imp (jh_value_m (.bound 4) (.bound 3)) <|
      .imp (Formula.isOmega (.bound 2)) <| .imp (.mem (.bound 2) (.bound 3)) <|
        .imp (.mem (.bound 1) (.bound 3)) <|
          .imp (finite_m kpair_convention_l (.bound 2) .newest) <|
            .imp (Formula.subset .newest (.bound 1)) (.mem .newest (.bound 3))

def jensenFiniteSubsetsSentence : Sentence := .ofFormula jensenFiniteSubsetsBody
  (by simp -implicitDefEqProofs [jensenFiniteSubsetsBody,Definitional.Formula.FreeClosed])

theorem jensenFiniteSubsets_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenFiniteSubsetsSentence := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenFiniteSubsetsBody
  simp only [jensenFiniteSubsetsBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,finite_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,Formula.satisfies_subset_iff]
  intro a C ω U X ha h hω hωC hUC finite sub
  exact jh_finite_subset_mem_l hZF ha h hω hωC hUC finite sub

theorem jensenFiniteSubsets_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenFiniteSubsetsSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenFiniteSubsets_models M hM)

/-- 原层的 rud 笛卡尔积闭包作用于给定实际乘积，不另选不对应的集合。 -/
theorem jh_product_mem_l (hZF : M.Models ZF) {a C A B X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hAC : M.mem A C) (hBC : M.mem B C)
    (prod : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) X A B) : M.mem X C := by
  have closed := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  obtain ⟨D,hDC,hD⟩ := closed.exists_l (ZF.modelsKP hZF) .prod hAC hBC hAC
  have eq := hZF.1.eq_of_same_members X D (fun p => by
    rw [hD p]
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,pair⟩ := (prod p).mp hp
      exact ⟨x,y,hx,hy,pair⟩
    · rintro ⟨x,y,hx,hy,pair⟩
      exact (prod p).mpr ⟨x,hx,y,hy,pair⟩)
  exact eq ▸ hDC

private def jensenFiniteMembersBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 3)) <| .imp (jh_value_m (.bound 3) (.bound 2)) <|
      .imp (Formula.isOmega (.bound 1)) <| .imp (.mem (.bound 1) (.bound 2)) <|
        .imp (finite_m kpair_convention_l (.bound 1) .newest) <|
          .imp (Formula.subset .newest (.bound 2)) (.mem .newest (.bound 2))

def jensenFiniteMembersSentence : Sentence := .ofFormula jensenFiniteMembersBody
  (by simp -implicitDefEqProofs [jensenFiniteMembersBody,Definitional.Formula.FreeClosed])

theorem jensenFiniteMembers_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenFiniteMembersSentence := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenFiniteMembersBody
  simp only [jensenFiniteMembersBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff,finite_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,Formula.satisfies_subset_iff]
  intro a C ω X ha h hω hωC finite sub
  exact jh_finite_members_mem_l hZF ha h hω hωC finite sub

theorem jensenFiniteMembers_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenFiniteMembersSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenFiniteMembers_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
