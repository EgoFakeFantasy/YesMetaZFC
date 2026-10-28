import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFiniteTruthLocal
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateFiniteTruthObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthDomainObjectTheorems

/-! # 不含自由赋值空间参数的原同层谓词真值推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def jensenPredicateFiniteBundleBody : Formula 1 9 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (amenableSet_m (.bound 1) (.bound 3)) <| .imp (Formula.isOmega (.bound 2)) <|
      .imp (.mem (.bound 2) (.bound 1)) <| .imp (.mem (.bound 4) (.bound 1)) <|
        .imp (.mem (.bound 5) (.bound 1)) <| .imp (.mem (.bound 6) (.bound 1)) <|
          .imp (.mem (.bound 7) (.bound 1)) <|
            .imp (pboundedFormula_m (.bound 4) (.bound 2) (.bound 5) (.bound 8) (.bound 7)) <|
              Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
                Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
                  Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <|
                    Formula.existsMem (.bound 7) <|
                      .conj (assignmentSpaceCert_m (.bound 9) (.bound 12) (.bound 13) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2))
                        (ptruthCheck_m (.bound 11) (.bound 10) (.bound 12) (.bound 13) (.bound 2) (.bound 14) (.bound 15) (.bound 1) .newest)

def jensenPredicateFiniteBundleSentence : Sentence := Sentence.forallClosure jensenPredicateFiniteBundleBody
  (by simp -implicitDefEqProofs [jensenPredicateFiniteBundleBody,Definitional.Formula.FreeClosed])

theorem jensenPredicateFiniteBundle_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenPredicateFiniteBundleSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 9 jensenPredicateFiniteBundleBody)
  apply (Formula.satisfies_forallClosure_iff free jensenPredicateFiniteBundleBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 9) jensenPredicateFiniteBundleBody
  simp only [jensenPredicateFiniteBundleBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    assignmentSpaceCert_sat_l hZF.1,ptruthCheck_sat_l hZF.1]
  intro hα hC amenable hω hωC hTC hnC hXC hFC valid
  obtain ⟨e,s,Z,S,E,V,H,heC,hsC,hZC,hSC,hEC,hVC,hHC,space,check⟩ :=
    jh_pfiniteTruth_bundle_l hZF hα hC amenable hω hωC hTC hnC hXC hFC valid
  exact ⟨e,heC,s,hsC,Z,hZC,S,hSC,E,hEC,V,hVC,H,hHC,space,check⟩

theorem jensenPredicateFiniteBundle_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenPredicateFiniteBundleSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenPredicateFiniteBundle_models M hM)

private def pfiniteLocalParams {d} (A L F X n ω T : Term d) : Fin 7 → Term d :=
  Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T))))))

@[simp] private theorem pfiniteLocalParams_closed_l {d} (A L F X n ω T : Term d)
    (hA : A.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) (hX : X.freeSupport = [])
    (hn : n.freeSupport = []) (hω : ω.freeSupport = []) (hT : T.freeSupport = []) :
    ∀ i, (pfiniteLocalParams A L F X n ω T i).freeSupport = [] :=
  Fin.cases hA (Fin.cases hL (Fin.cases hF (Fin.cases hX (Fin.cases hn (Fin.cases hω (fun _ => hT))))))

private def jensenPredicateFiniteSourceBody (positive : Bool) : Formula 1 11 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (amenableSet_m (.bound 1) (.bound 3)) <| .imp (Formula.isOmega (.bound 2)) <|
      .imp (.mem (.bound 2) (.bound 1)) <| .imp (.mem (.bound 4) (.bound 1)) <|
        .imp (.mem (.bound 5) (.bound 1)) <| .imp (.mem (.bound 6) (.bound 1)) <|
          .imp (.mem (.bound 7) (.bound 1)) <|
            .imp (pboundedFormula_m (.bound 4) (.bound 2) (.bound 5) (.bound 8) (.bound 7)) <|
              .iff (within_m (pfiniteTruth_s positive)
                (pfiniteLocalParams (.bound 3) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 4))
                (.bound 9) (.bound 10) (.bound 1))
                (binary_pred_m (pfiniteTruth_s positive).schema
                  (pfiniteLocalParams (.bound 3) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 4))
                  (.bound 9) (.bound 10))

def jensenPredicateFiniteSourceSentence (positive : Bool) : Sentence := Sentence.forallClosure (jensenPredicateFiniteSourceBody positive)
  (by simp -implicitDefEqProofs [jensenPredicateFiniteSourceBody,Definitional.Formula.FreeClosed])

theorem jensenPredicateFiniteSource_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenPredicateFiniteSourceSentence positive) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 11 (jensenPredicateFiniteSourceBody positive))
  apply (Formula.satisfies_forallClosure_iff free (jensenPredicateFiniteSourceBody positive)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 11) (jensenPredicateFiniteSourceBody positive)
  simp only [jensenPredicateFiniteSourceBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_iff_iff,within_sat_l,binary_pred_sat_l,Term.eval_bound]
  intro hα hC amenable hω hωC hTC hnC hXC hFC valid
  have hLC := jh_value_transitive_l (ZF.models_kpi_l hZF) hC (b 2) hωC (b 8) valid.finite
  let ρ : Env M 7 := ⟨Fin.cases (b 3) (Fin.cases (b 8) (Fin.cases (b 7) (Fin.cases (b 6)
    (Fin.cases (b 5) (Fin.cases (b 2) (fun _ => b 4)))))),free⟩
  have paramsEq : (⟨fun i => (pfiniteLocalParams (.bound 3) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 4) i).eval
      (⟨b,free⟩ : Env M 11),free⟩ : Env M 7) = ρ := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl
        (fun m => Fin.cases rfl (fun n => Fin.cases rfl (fun _ => rfl) n) m) l) k) j) i
    · rfl
  rw [paramsEq]
  change Within_d (pfiniteTruth_s positive) ρ (b 9) (b 10) (b 1) ↔
    (pfiniteTruth_s positive).schema.denote ρ (b 9) (b 10)
  have hp : ∀ i : Fin 6, M.mem (ρ.bound i.succ) (b 1) :=
    Fin.cases hLC (Fin.cases hFC (Fin.cases hXC (Fin.cases hnC (Fin.cases hωC (fun _ => hTC)))))
  exact (jh_pfiniteTruth_within_l hZF positive hα hC ρ amenable hp hω valid (b 9) (b 10)).trans
    (pfiniteTruth_sat_l (ZF.modelsKP hZF) positive ρ (b 9) (b 10)).symm

theorem jensenPredicateFiniteSource_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenPredicateFiniteSourceSentence positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenPredicateFiniteSource_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
