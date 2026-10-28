import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateTruthLocal

/-! # 统一内部谓词程序与实际同层证书的原 ZF 推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def predicateHistoryExistsBody : Formula 1 7 :=
  .imp (KP.ord0_m (.bound 6)) <| .existsE <|
    ptruthEval_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest

def predicateHistoryExistsSentence : Sentence := Sentence.forallClosure predicateHistoryExistsBody
  (by simp -implicitDefEqProofs [predicateHistoryExistsBody,Definitional.Formula.FreeClosed])

theorem predicateHistoryExists_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateHistoryExistsSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 7 predicateHistoryExistsBody)
  apply (Formula.satisfies_forallClosure_iff free predicateHistoryExistsBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 7) predicateHistoryExistsBody
  simp only [predicateHistoryExistsBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_exists_iff,ptruthEval_sat_l (ZF.modelsKP hZF)]
  exact fun ordinal => ptruthEval_exists_l hZF (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) ordinal

theorem predicateHistoryExists_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateHistoryExistsSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateHistoryExists_models M hM)

private def predicateCertificateBody : Formula 1 8 :=
  .imp (pboundedFormula_m (.bound 0) (.bound 2) (.bound 3) (.bound 7) (.bound 6)) <|
    .existsE <| .existsE <|
      ptruthCheck_m (.bound 2) (.bound 3) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 1) .newest

def predicateCertificateSentence : Sentence := Sentence.forallClosure predicateCertificateBody
  (by simp -implicitDefEqProofs [predicateCertificateBody,Definitional.Formula.FreeClosed])

theorem predicateCertificate_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateCertificateSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 8 predicateCertificateBody)
  apply (Formula.satisfies_forallClosure_iff free predicateCertificateBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 8) predicateCertificateBody
  simp only [predicateCertificateBody,Formula.satisfies_imp_iff,pboundedFormula_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_exists_iff,ptruthCheck_sat_l hZF.1]
  exact fun valid => ptruthCertificate_exists_l hZF (A := b 1) (X := b 4) (E := b 5) valid

theorem predicateCertificate_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateCertificateSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateCertificate_models M hM)

private def predicateTraceBody : Formula 1 10 :=
  .imp (predicateTrace_m (.bound 1) (.bound 4) (.bound 2)) <| .conj
    (.iff (ptruthCheck_m (.bound 0) (.bound 1) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9))
      (ptruthCheck_m (.bound 0) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)))
    (.iff (ptruthEval_m (.bound 0) (.bound 1) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 9))
      (ptruthEval_m (.bound 0) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 9)))

def predicateTraceHistorySentence : Sentence := Sentence.forallClosure predicateTraceBody
  (by simp -implicitDefEqProofs [predicateTraceBody,Definitional.Formula.FreeClosed])

theorem predicateTraceHistory_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateTraceHistorySentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 10 predicateTraceBody)
  apply (Formula.satisfies_forallClosure_iff free predicateTraceBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 10) predicateTraceBody
  simp only [predicateTraceBody,Formula.satisfies_imp_iff,predicateTrace_sat_l,Formula.satisfies_conj_iff,
    Formula.satisfies_iff_iff,ptruthCheck_sat_l hZF.1,ptruthEval_sat_l (ZF.modelsKP hZF)]
  exact fun trace => ⟨ptruthCheck_trace_l trace,ptruthEval_trace_l (kp_pair_l (ZF.modelsKP hZF)) trace⟩

theorem predicateTraceHistory_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateTraceHistorySentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateTraceHistory_models M hM)

private def jensenPredicateCertificateBody : Formula 1 10 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (amenableSet_m (.bound 1) (.bound 2)) <| .imp (Formula.isOmega (.bound 3)) <|
      .imp (.mem (.bound 3) (.bound 1)) <| .imp (.mem (.bound 4) (.bound 1)) <|
        .imp (.mem (.bound 5) (.bound 1)) <| .imp (.mem (.bound 6) (.bound 1)) <|
          .imp (.mem (.bound 7) (.bound 1)) <| .imp (.mem (.bound 8) (.bound 1)) <|
            .imp (pboundedFormula_m (.bound 4) (.bound 3) (.bound 5) (.bound 9) (.bound 8)) <|
              Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
                ptruthCheck_m (.bound 6) (.bound 4) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 1) .newest

def jensenPredicateCertificateSentence : Sentence := Sentence.forallClosure jensenPredicateCertificateBody
  (by simp -implicitDefEqProofs [jensenPredicateCertificateBody,Definitional.Formula.FreeClosed])

theorem jensenPredicateCertificate_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence jensenPredicateCertificateSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 10 jensenPredicateCertificateBody)
  apply (Formula.satisfies_forallClosure_iff free jensenPredicateCertificateBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 10) jensenPredicateCertificateBody
  simp only [jensenPredicateCertificateBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_existsMem_iff,ptruthCheck_sat_l hZF.1]
  intro hα hC amenable hω hωC hTC hnC hXC hEC hFC valid
  obtain ⟨Z,H,hZC,hHC,check⟩ := jh_ptruthCertificate_l hZF hα hC amenable hω hωC hTC hnC hXC hEC hFC valid
  exact ⟨Z,hZC,H,hHC,check⟩

theorem jensenPredicateCertificate_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF jensenPredicateCertificateSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenPredicateCertificate_models M hM)


private def predicateTruthParams {d} (A L F E X n T : Term d) : Fin 7 → Term d :=
  Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases E (Fin.cases X (Fin.cases n (fun _ => T))))))

@[simp] private theorem predicateTruthParams_closed_l {d} (A L F E X n T : Term d)
    (hA : A.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) (hE : E.freeSupport = [])
    (hX : X.freeSupport = []) (hn : n.freeSupport = []) (hT : T.freeSupport = []) :
    ∀ i, (predicateTruthParams A L F E X n T i).freeSupport = [] :=
  Fin.cases hA (Fin.cases hL (Fin.cases hF (Fin.cases hE (Fin.cases hX (Fin.cases hn (fun _ => hT))))))

private def jensenPredicateSourceBody (positive : Bool) : Formula 1 12 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (amenableSet_m (.bound 1) (.bound 3)) <| .imp (Formula.isOmega (.bound 2)) <|
      .imp (.mem (.bound 2) (.bound 1)) <| .imp (.mem (.bound 4) (.bound 1)) <|
        .imp (.mem (.bound 5) (.bound 1)) <| .imp (.mem (.bound 6) (.bound 1)) <|
          .imp (.mem (.bound 7) (.bound 1)) <| .imp (.mem (.bound 8) (.bound 1)) <|
            .imp (pboundedFormula_m (.bound 4) (.bound 2) (.bound 5) (.bound 9) (.bound 8)) <|
              .imp (.mem (.bound 10) (.bound 9)) <| .imp (.mem (.bound 11) (.bound 7)) <|
                .iff (within_m (pcertifiedTruth_s positive)
                  (predicateTruthParams (.bound 3) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4))
                  (.bound 10) (.bound 11) (.bound 1))
                  (binary_pred_m (pcertifiedTruth_s positive).schema
                    (predicateTruthParams (.bound 3) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4))
                    (.bound 10) (.bound 11))

def jensenPredicateSourceSentence (positive : Bool) : Sentence := Sentence.forallClosure (jensenPredicateSourceBody positive)
  (by simp -implicitDefEqProofs [jensenPredicateSourceBody,Definitional.Formula.FreeClosed])

theorem jensenPredicateSource_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenPredicateSourceSentence positive) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 12 (jensenPredicateSourceBody positive))
  apply (Formula.satisfies_forallClosure_iff free (jensenPredicateSourceBody positive)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 12) (jensenPredicateSourceBody positive)
  simp only [jensenPredicateSourceBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_iff_iff,within_sat_l,binary_pred_sat_l,Term.eval_bound]
  intro hα hC amenable hω hωC hTC hnC hXC hEC hFC valid _ _
  let ρ : Env M 7 := ⟨Fin.cases (b 3) (Fin.cases (b 9) (Fin.cases (b 8) (Fin.cases (b 7)
    (Fin.cases (b 6) (Fin.cases (b 5) (fun _ => b 4)))))),free⟩
  have paramsEq : (⟨fun i => (predicateTruthParams (.bound 3) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) i).eval
      (⟨b,free⟩ : Env M 12),free⟩ : Env M 7) = ρ := by
    rw [Env.mk.injEq]
    constructor
    · funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl
        (fun m => Fin.cases rfl (fun n => Fin.cases rfl (fun _ => rfl) n) m) l) k) j) i
    · rfl
  rw [paramsEq]
  change Within_d (pcertifiedTruth_s positive) ρ (b 10) (b 11) (b 1) ↔
    (pcertifiedTruth_s positive).schema.denote ρ (b 10) (b 11)
  exact (jh_pcertifiedTruth_within_l hZF positive hα hC ρ amenable hω hωC hTC hnC hXC hEC hFC valid (b 10) (b 11)).trans
    (pcertifiedTruth_sat_l (ZF.modelsKP hZF) positive ρ (b 10) (b 11)).symm

theorem jensenPredicateSource_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenPredicateSourceSentence positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenPredicateSource_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
