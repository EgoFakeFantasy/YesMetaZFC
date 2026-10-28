import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateNumberedTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 五类程序编号与双参数数码真值的原 ZF 推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def pnumParams {d} (A ω : Term d) : Fin 2 → Term d := Fin.cases A (fun _ => ω)
private def pfinParams {d} (A L F X n ω T : Term d) : Fin 7 → Term d :=
  Fin.cases A (Fin.cases L (Fin.cases F (Fin.cases X (Fin.cases n (Fin.cases ω (fun _ => T))))))

@[simp] private theorem pnumParams_closed_l {d} (A ω : Term d) (hA : A.freeSupport = []) (hω : ω.freeSupport = []) :
    ∀ i, (pnumParams A ω i).freeSupport = [] := Fin.cases hA (fun _ => hω)

@[simp] private theorem pfinParams_closed_l {d} (A L F X n ω T : Term d)
    (hA : A.freeSupport = []) (hL : L.freeSupport = []) (hF : F.freeSupport = []) (hX : X.freeSupport = [])
    (hn : n.freeSupport = []) (hω : ω.freeSupport = []) (hT : T.freeSupport = []) :
    ∀ i, (pfinParams A L F X n ω T i).freeSupport = [] :=
  Fin.cases hA (Fin.cases hL (Fin.cases hF (Fin.cases hX (Fin.cases hn (Fin.cases hω (fun _ => hT))))))

@[simp] private theorem pnumParams_env_l {M : SetTheory.Structure.{u}} {d} (ρ : Env M d) (A ω : Term d) :
    (⟨fun i => (pnumParams A ω i).eval ρ,ρ.free⟩ : Env M 2) =
      ⟨Fin.cases (A.eval ρ) (fun _ => ω.eval ρ),ρ.free⟩ := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)),rfl⟩

private def predicateProgramNumberExistsBody : Formula 1 6 :=
  .imp (Formula.isOmega (.bound 1)) <| .imp (pboundedFormula_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) <|
    .imp (.mem (.bound 5) (.bound 3)) <| Formula.existsMem (.bound 1) <|
      programNumber_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest

def predicateProgramNumberExistsSentence : Sentence := Sentence.forallClosure predicateProgramNumberExistsBody
  (by simp -implicitDefEqProofs [predicateProgramNumberExistsBody,Definitional.Formula.FreeClosed])

theorem predicateProgramNumberExists_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence predicateProgramNumberExistsSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 6 predicateProgramNumberExistsBody)
  apply (Formula.satisfies_forallClosure_iff free predicateProgramNumberExistsBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 6) predicateProgramNumberExistsBody
  simp only [predicateProgramNumberExistsBody,Formula.satisfies_imp_iff,Formula.satisfies_isOmega_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,
    programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1]
  exact fun hω valid hr => pprogramNumber_exists_l hZF hω valid hr

theorem predicateProgramNumberExists_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF predicateProgramNumberExistsSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateProgramNumberExists_models M hM)

private def predicateNumberedFixedBody (positive : Bool) : Formula 1 10 :=
  .imp (Formula.isOmega (.bound 2)) <| .imp (pboundedFormula_m (.bound 0) (.bound 2) (.bound 3) (.bound 4) (.bound 5)) <|
    .imp (programNumber_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)) <|
      .imp (Formula.isTransitive (.bound 8)) <| .imp (fn0_m (.bound 3) (.bound 8) (.bound 9)) <|
        .iff (binary_pred_m (pnumberedTruth_s positive).schema (pnumParams (.bound 1) (.bound 2)) (.bound 7) (.bound 9))
          (binary_pred_m (pfiniteTruth_s positive).schema
            (pfinParams (.bound 1) (.bound 4) (.bound 5) (.bound 8) (.bound 3) (.bound 2) (.bound 0)) (.bound 6) (.bound 9))

def predicateNumberedFixedSentence (positive : Bool) : Sentence := Sentence.forallClosure (predicateNumberedFixedBody positive)
  (by simp -implicitDefEqProofs [predicateNumberedFixedBody,Definitional.Formula.FreeClosed])

theorem predicateNumberedFixed_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (predicateNumberedFixedSentence positive) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 10 (predicateNumberedFixedBody positive))
  apply (Formula.satisfies_forallClosure_iff free (predicateNumberedFixedBody positive)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 10) (predicateNumberedFixedBody positive)
  simp only [predicateNumberedFixedBody,Formula.satisfies_imp_iff,Formula.satisfies_isOmega_iff,
    pboundedFormula_sat_l (ZF.modelsKP hZF),programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isTransitive_iff,fn0_sat_l hZF.1,Formula.satisfies_iff_iff,binary_pred_sat_l,
    pfiniteTruth_sat_l (ZF.modelsKP hZF),pfinParams,Term.eval_bound]
  intro hω valid code hx fn
  rw [pnumParams_env_l (⟨b,free⟩ : Env M 10) (.bound 1) (.bound 2)]
  let ρ : Env M 2 := ⟨Fin.cases (b 1) (fun _ : Fin 1 => b 2),free⟩
  have hωρ : M.IsOmega (ρ.bound 1) := by
    change M.IsOmega (b 2)
    exact hω
  have correct := pnumberedTruth_fixed_l (M := M) hZF positive ρ
    (T := b 0) (n := b 3) (L := b 4) (F := b 5) (r := b 6) (X := b 8) (e := b 7) (f := b 9)
    hωρ valid code hx (fn0_function_l (ZF.modelsKP hZF) fn)
  exact correct

theorem predicateNumberedFixed_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (predicateNumberedFixedSentence positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => predicateNumberedFixed_models positive M hM)

private def jensenPredicateNumberedLocalBody (positive : Bool) : Formula 1 6 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (amenableSet_m (.bound 1) (.bound 2)) <| .imp (Formula.isOmega (.bound 3)) <|
      .imp (.mem (.bound 3) (.bound 1)) <|
        .iff (within_m (pnumberedTruth_s positive) (pnumParams (.bound 2) (.bound 3)) (.bound 4) (.bound 5) (.bound 1))
          (.conj (.mem (.bound 5) (.bound 1))
            (binary_pred_m (pnumberedTruth_s positive).schema (pnumParams (.bound 2) (.bound 3)) (.bound 4) (.bound 5)))

def jensenPredicateNumberedLocalSentence (positive : Bool) : Sentence := Sentence.forallClosure (jensenPredicateNumberedLocalBody positive)
  (by simp -implicitDefEqProofs [jensenPredicateNumberedLocalBody,Definitional.Formula.FreeClosed])

theorem jensenPredicateNumberedLocal_models (positive : Bool) (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (jensenPredicateNumberedLocalSentence positive) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 6 (jensenPredicateNumberedLocalBody positive))
  apply (Formula.satisfies_forallClosure_iff free (jensenPredicateNumberedLocalBody positive)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 6) (jensenPredicateNumberedLocalBody positive)
  simp only [jensenPredicateNumberedLocalBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,amenableSet_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_conj_iff,within_sat_l,binary_pred_sat_l,Term.eval_bound]
  intro hα hC amenable hω hωC
  rw [pnumParams_env_l (⟨b,free⟩ : Env M 6) (.bound 2) (.bound 3)]
  let ρ : Env M 2 := ⟨Fin.cases (b 2) (fun _ => b 3),free⟩
  exact (jh_pnumberedTruth_exact_within_l hZF positive hα hC ρ (b 4) (b 5) amenable hω hωC).trans
    (and_congr_right fun _ => (pnumberedTruth_sat_l hZF positive ρ (b 4) (b 5) hω).symm)

theorem jensenPredicateNumberedLocal_derives (positive : Bool) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (jensenPredicateNumberedLocalSentence positive) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => jensenPredicateNumberedLocal_models positive M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
