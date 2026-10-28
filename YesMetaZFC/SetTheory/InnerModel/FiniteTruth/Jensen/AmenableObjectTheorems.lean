import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSeparationSyntax

/-! # 原 ZF 中的 amenability 与逐有界模板分离推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

private def memberAmenableBody : Formula 1 3 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (.mem (.bound 2) (.bound 1)) (amenableSet_m (.bound 1) (.bound 2))

def jensenMemberAmenableSentence : Sentence := Sentence.forallClosure memberAmenableBody
  (by simp -implicitDefEqProofs [memberAmenableBody,Definitional.Formula.FreeClosed])

theorem jensenMemberAmenable_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenMemberAmenableSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 3 memberAmenableBody)
  apply (Formula.satisfies_forallClosure_iff free memberAmenableBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 3) memberAmenableBody
  simp only [memberAmenableBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,
    Formula.satisfies_mem_iff,amenableSet_sat_l]
  exact fun hα hC hA => jh_member_amenable_l hZF hα hC hA

theorem jensenMemberAmenable_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenMemberAmenableSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenMemberAmenable_models M hM)

private def amenableParamsIn_m {d} : {n : Nat} → (Fin n → Term d) → Term d → Formula 1 d
  | 0, _, _ => .truth
  | _ + 1, e, C => .conj (.mem (e 0) C) (amenableParamsIn_m (fun i => e i.succ) C)

@[simp] private theorem amenableParamsIn_closed_l {n d} (e : Fin n → Term d) (C : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = []) :
    (amenableParamsIn_m e C).FreeClosed := by
  induction n with
  | zero => simp only [amenableParamsIn_m, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
  | succ n ih =>
    simp only [amenableParamsIn_m, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
    exact ⟨⟨he 0, hC⟩, ih (fun i => e i.succ) (fun i => he i.succ)⟩

private theorem amenableParamsIn_sat_l {n d} (e : Fin n → Term d) (C : Term d) (ρ : Env M d) :
    Formula.satisfies ρ (amenableParamsIn_m e C) ↔ ∀ i, M.mem ((e i).eval ρ) (C.eval ρ) := by
  induction n with
  | zero => simp only [amenableParamsIn_m, Formula.satisfies_truth_iff, Fin.forall_fin_zero]
  | succ n ih =>
    rw [amenableParamsIn_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

private def amenableLayerParams (p offset : Nat) : Fin p → Term (p+offset) :=
  fun i => .bound ⟨i.val+offset,by omega⟩

private def amenableSeparationBody {p} (φ : UnarySchema (p+1)) : Formula 1 p :=
  .forallE <| .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 3)) <| .imp (jh_value_m (.bound 3) (.bound 2)) <|
      .imp (amenableSet_m (.bound 2) (.bound 1)) <| .imp (.mem .newest (.bound 2)) <|
        .imp (amenableParamsIn_m (amenableLayerParams p 4) (.bound 2))
          (predicateSeparation_m φ (amenableLayerParams p 4) (.bound 2) (.bound 1) .newest)

def jensenAmenableSeparationSentence {p} (φ : UnarySchema (p+1)) : Sentence :=
  Sentence.forallClosure (amenableSeparationBody φ)
    (by simp -implicitDefEqProofs [amenableSeparationBody,Definitional.Formula.FreeClosed,amenableLayerParams])

theorem jensenAmenableSeparation_models {p} (φ : UnarySchema (p+1))
    (useCert : PredicateDelta0 (1 : Fin (p+2)) φ.body) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenAmenableSeparationSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure p (amenableSeparationBody φ))
  apply (Formula.satisfies_forallClosure_iff free (amenableSeparationBody φ)).mpr
  intro b
  let ρ : Env M p := ⟨b,free⟩
  change Formula.satisfies ρ (amenableSeparationBody φ)
  simp only [amenableSeparationBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_mem_iff,
    amenableParamsIn_sat_l,predicateSeparation_sat_l]
  intro α C A X hα hC amenable hXC params
  change ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.denote (ρ.push A) x
  exact jh_amenable_delta0_separation_l hZF hα hC amenable hXC φ useCert ρ params

theorem jensenAmenableSeparation_derives {p} (φ : UnarySchema (p+1))
    (useCert : PredicateDelta0 (1 : Fin (p+2)) φ.body) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenAmenableSeparationSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => jensenAmenableSeparation_models φ useCert M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
