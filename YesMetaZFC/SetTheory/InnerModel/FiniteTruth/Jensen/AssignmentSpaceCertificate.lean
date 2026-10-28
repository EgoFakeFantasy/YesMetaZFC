import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceTableLocal
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.LocalObjectTheorem

/-! # 原 Jensen 层中的完整有限赋值空间证书

以实际内部有限归纳装配整张空间表，再用 rud 值域与配对装配全部证书和 Σ₁ 见证。
不假设小层满足 KP 或 Collection；背景收集所得的表没有被直接放入小层。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_assignmentSpaceTables_l (hZF : M.Models ZF) {a C ω X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hXC : M.mem X C) :
    ∀ r, M.mem r ω → ∃ S, M.mem S C ∧ SpaceTable_d (kp_pair_l (ZF.modelsKP hZF)) r X S :=
  rd_spaceTables_l hZF (jh_value_closed_l (ZF.models_kpi_l hZF) ha h)
    (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hω hωC
      (jh_finite_functionSpace_l hZF ha h hω hωC hXC)

/-- 整张表、行容器、零与后继及输出空间都属于同一原 J 层。 -/
theorem jh_assignmentSpaceCertificate_l (hZF : M.Models ZF) {a C ω n X : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (hω : M.IsOmega ω)
    (hωC : M.mem ω C) (hXC : M.mem X C) (hn : M.mem n ω) :
    ∃ e s Z S E, M.mem e C ∧ M.mem s C ∧ M.mem Z C ∧ M.mem S C ∧ M.mem E C ∧
      AssignmentSpaceCert_d ω n X e s Z S E := by
  let hKP := ZF.modelsKP hZF
  have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
  have hc := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  obtain ⟨e,he,heω⟩ := hω.1.1
  obtain ⟨s,hns,hsω⟩ := hω.1.2 n hn
  obtain ⟨S,hSC,table⟩ := jh_assignmentSpaceTables_l hZF ha h hω hωC hXC s hsω
  obtain ⟨Z,hZC,hZ⟩ := hC.exists_l hKP .range hSC hSC hSC
  obtain ⟨E,hEn⟩ := (table.1.2.2 n).mp hns.predecessor_mem
  have hEZ := (hZ E).mpr ⟨n,hEn⟩
  exact ⟨e,s,Z,S,E,hc ω hωC e heω,hc ω hωC s hsω,hZC,hSC,hc Z hZC E hEZ,
    assignmentSpaceCert_of_table_l hZF hω hn he hns table hZ hEn⟩

/-- 完整有限空间的实际 Σ₁ 正规形在同层有见证，并与背景完整规格等价。 -/
theorem jh_assignmentSpace_within_l (hZF : M.Models ZF) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) (ρ : Env M 2)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hXC : M.mem (ρ.bound 0) C)
    {n : M.Domain} (hn : M.mem n (ρ.bound 1)) (E : M.Domain) :
    Within_d assignmentSpace_s ρ n E C ↔
      M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n (ρ.bound 0) := by
  constructor
  · rintro ⟨w,_,hw⟩
    obtain ⟨e,_,s,_,Z,_,S,_,cert⟩ := (assignmentSpace_matrix_sat_l hZF.1 ρ n E w).mp hw
    exact assignmentSpaceCert_sound_l hZF hω cert
  · intro full
    obtain ⟨e,s,Z,S,A,heC,hsC,hZC,hSC,_,cert⟩ :=
      jh_assignmentSpaceCertificate_l hZF ha h hω hωC hXC hn
    have fullA := assignmentSpaceCert_sound_l hZF hω cert
    have eq := hZF.1.eq_of_same_members A E (fun f => (fullA f).trans (full f).symm)
    subst A
    have hC := jh_value_closed_l (ZF.models_kpi_l hZF) ha h
    let hKP := ZF.modelsKP hZF
    obtain ⟨P,hPC,hP⟩ := hC.exists_l hKP .pair heC hsC heC
    obtain ⟨Q,hQC,hQ⟩ := hC.exists_l hKP .pair hZC hSC hZC
    obtain ⟨w,hwC,hw⟩ := hC.union_l hKP hPC hQC
    exact ⟨w,hwC,(assignmentSpace_matrix_sat_l hZF.1 ρ n E w).mpr
      ⟨e,(hw e).mpr (Or.inl ((hP e).mpr (Or.inl rfl))),
        s,(hw s).mpr (Or.inl ((hP s).mpr (Or.inr rfl))),
        Z,(hw Z).mpr (Or.inr ((hQ Z).mpr (Or.inl rfl))),
        S,(hw S).mpr (Or.inr ((hQ S).mpr (Or.inr rfl))),cert⟩⟩

/-- 子结构中的实际 Σ₁ 图准确对应背景图，不假设子结构满足 KP。 -/
theorem jh_assignmentSpace_local_l (hZF : M.Models ZF) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hnC : Nonempty {x : M.Domain // M.mem x C}) (ρ : Env (rt_model_l C hnC) 2)
    (n E : (rt_model_l C hnC).Domain) (hω : M.IsOmega (ρ.bound 1).val)
    (hn : M.mem n.val (ρ.bound 1).val) :
    assignmentSpace_s.schema.denote ρ n E ↔ assignmentSpace_s.schema.denote
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) n.val E.val :=
  (within_local_l (jh_value_transitive_l (ZF.models_kpi_l hZF) h) hnC assignmentSpace_s ρ n E).trans
    ((jh_assignmentSpace_within_l hZF ha h
      (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ)
      hω (ρ.bound 1).property (ρ.bound 0).property hn E.val).trans
        (assignmentSpace_sigma1_l hZF
          (image_env_l (fun x : (rt_model_l C hnC).Domain => (x.val : M.Domain)) ρ) hω hn).symm)

private def jensenAssignmentSpaceCertificateBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 4)) <| .imp (jh_value_m (.bound 4) (.bound 3)) <|
      .imp (Formula.isOmega (.bound 2)) <| .imp (.mem (.bound 2) (.bound 3)) <|
        .imp (.mem .newest (.bound 3)) <| .imp (.mem (.bound 1) (.bound 2)) <|
          .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
            .conj (.mem (.bound 4) (.bound 8)) <| .conj (.mem (.bound 3) (.bound 8)) <|
              .conj (.mem (.bound 2) (.bound 8)) <| .conj (.mem (.bound 1) (.bound 8)) <|
                .conj (.mem .newest (.bound 8))
                  (assignmentSpaceCert_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)

def jensenAssignmentSpaceCertificate : Sentence := .ofFormula jensenAssignmentSpaceCertificateBody
  (by simp -implicitDefEqProofs [jensenAssignmentSpaceCertificateBody, Definitional.Formula.FreeClosed])

theorem jensenAssignmentSpaceCertificate_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenAssignmentSpaceCertificate := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenAssignmentSpaceCertificateBody
  simp only [jensenAssignmentSpaceCertificateBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l, Formula.satisfies_isOmega_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, assignmentSpaceCert_sat_l hZF.1]
  exact fun a C ω n X ha h hω hωC hXC hn => jh_assignmentSpaceCertificate_l hZF ha h hω hωC hXC hn

theorem jensenAssignmentSpaceCertificate_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenAssignmentSpaceCertificate :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenAssignmentSpaceCertificate_models M hM)

private def localSpaceIndex : Fin 2 → Fin 6 := Fin.cases 1 (fun _ => 3)
private def localSpaceParams (i : Fin 2) : Term 6 := .bound (localSpaceIndex i)

private def jensenAssignmentSpaceLocalBody : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 5)) <| .imp (jh_value_m (.bound 5) (.bound 4)) <|
      .imp (Formula.isOmega (.bound 3)) <| .imp (.mem (.bound 3) (.bound 4)) <|
        .imp (.mem (.bound 1) (.bound 4)) <| .imp (.mem (.bound 2) (.bound 3)) <|
          .iff (Formula.isFunctionSpace kpair_convention_l .newest (.bound 2) (.bound 1))
            (within_m assignmentSpace_s localSpaceParams (.bound 2) .newest (.bound 4))

def jensenAssignmentSpaceLocal : Sentence := .ofFormula jensenAssignmentSpaceLocalBody
  (by simp -implicitDefEqProofs [jensenAssignmentSpaceLocalBody,localSpaceParams,Definitional.Formula.FreeClosed])

theorem jensenAssignmentSpaceLocal_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenAssignmentSpaceLocal := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) jensenAssignmentSpaceLocalBody
  simp only [jensenAssignmentSpaceLocalBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,within_sat_l]
  intro a C ω n X E ha h hω hωC hXC hn
  let ξ := ((((((⟨Fin.elim0,envFree⟩ : Env M 0).push a).push C).push ω).push n).push X).push E
  let η : Env M 2 := ⟨fun i => (localSpaceParams i).eval ξ,envFree⟩
  change M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X ↔ Within_d assignmentSpace_s η n E C
  exact (jh_assignmentSpace_within_l hZF ha h η hω hωC hXC hn E).symm

theorem jensenAssignmentSpaceLocal_derives : YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenAssignmentSpaceLocal :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenAssignmentSpaceLocal_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
