import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthDomainStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateCertifiedTruth
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomain

/-! # 含只读谓词的原内部程序在扩大传递域时保值

归纳使用实际有界行一致公式和原 KPi 内部归纳。背景模型可外部非良基，长度
可为模型内非标准有限对象；证明不沿宿主自然数或外部程序列表递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

/-- 全部合法内部行在旧完整赋值空间上保值，包含正负嵌套及有界量词。 -/
theorem ptruthEval_domain_l (hZF : M.Models ZF) {T A ω n X Y E G F L H J : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : PBoundedFormula_d T ω n L F)
    (hH : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n X E F L H)
    (hJ : PtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T A n Y G F L J) :
    ∀ r, M.mem r L → BtruthAgreement_d E H J r := by
  let hKP := ZF.modelsKP hZF
  let ρ : Env M 4 := ⟨Fin.cases J (Fin.cases H (Fin.cases E (fun _ => L))), fun _ => L⟩
  let φ : UnarySchema 4 := {
    body := .imp (.mem .newest (.bound 4)) (btruthAgreement_m (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat r : φ.denote ρ r ↔ (M.mem r L → BtruthAgreement_d E H J r) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      btruthAgreement_sat_l hZF.1]
    rfl
  obtain ⟨_, induction⟩ := KPi.models_iff_l.mp (ZF.models_kpi_l hZF)
  have all := induction φ ρ (by
    intro r ih
    apply (sat r).mpr
    intro hr f hf
    obtain ⟨c, hc, hrc⟩ := valid.graph.2.1 r hr
    obtain ⟨A, hA⟩ := (hH.1.2.2 r).mp hr
    obtain ⟨B, hB⟩ := (hJ.1.2.2 r).mp hr
    have rowValid := valid.row r hr c hc hrc
    have previous : ∀ i, M.mem i r → ∀ g, M.mem g E → (Bhit_d H i g ↔ Bhit_d J i g) :=
      fun i hi => (sat i).mp (ih i hi) (valid.ordinal.transitive r hr i hi)
    have rowH := ptruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 hH hrc hA rowValid
    have rowJ := ptruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 hJ hrc hB rowValid
    have hfG := functionSpace_inclusion_l (kp_pair_l hKP) sub he hg f hf
    exact (Bhit_d.value_l hH.1.2.1.2 hA).trans (((rowH f).trans (and_iff_right hf)).trans
      ((ptruthNode_domain_l hKP hx sub he hg hf previous rowValid).trans
        (((rowJ f).trans (and_iff_right hfG)).symm.trans (Bhit_d.value_l hJ.1.2.1.2 hB).symm))))
  exact fun r hr => (sat r).mp (all r) hr

/-- 任意两份完整证书也给出相同的旧赋值真值，不要求它们在同一 J 层中。 -/
theorem ptruthCertificate_domain_l (hZF : M.Models ZF) {T A ω n X Y E G F L Z H W J : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : PBoundedFormula_d T ω n L F)
    (hH : PtruthCheck_d T A n X E F L Z H) (hJ : PtruthCheck_d T A n Y G F L W J) :
    ∀ r, M.mem r L → BtruthAgreement_d E H J r :=
  ptruthEval_domain_l hZF hx sub he hg valid
    (ptruthEval_of_check_l hZF valid hH) (ptruthEval_of_check_l hZF valid hJ)

/-- 正负两个统一谓词 Σ₁ 操作真值模板都在扩大传递求值域时保值。 -/
theorem pcertifiedTruth_domain_l (hZF : M.Models ZF) (positive : Bool) {T A ω n X Y E G F L r f : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : PBoundedFormula_d T ω n L F) (hr : M.mem r L) (hf : M.mem f E) :
    PCertifiedTruth_d positive T A n X E F L r f ↔ PCertifiedTruth_d positive T A n Y G F L r f := by
  obtain ⟨Z, H, hH⟩ := ptruthCertificate_exists_l hZF (A := A) (X := X) (E := E) valid
  obtain ⟨W, J, hJ⟩ := ptruthCertificate_exists_l hZF (A := A) (X := Y) (E := G) valid
  have eq := ptruthCertificate_domain_l hZF hx sub he hg valid hH hJ r hr f hf
  rw [pcertifiedTruth_value_l hZF positive valid hH, pcertifiedTruth_value_l hZF positive valid hJ]
  cases positive <;> simp only [BtruthAnswer_d, Bool.false_eq_true, ↓reduceIte, eq]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
