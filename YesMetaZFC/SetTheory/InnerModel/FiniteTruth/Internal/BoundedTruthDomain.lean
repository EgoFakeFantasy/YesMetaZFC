import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthDomainStep
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.CertifiedTruth

/-! # 内部有界程序在扩大传递求值域时的真值不变

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

def BtruthAgreement_d (E H J r : M.Domain) : Prop :=
  ∀ f, M.mem f E → (Bhit_d H r f ↔ Bhit_d J r f)

def btruthAgreement_m {d} (E H J r : Term d) : Formula 1 d :=
  Formula.forallMem E (.iff (bhit_m H.weaken r.weaken .newest) (bhit_m J.weaken r.weaken .newest))
derive_free_closed btruthAgreement_m

theorem btruthAgreement_delta_l {d} (E H J r : Term d) : (btruthAgreement_m E H J r).IsDelta0 :=
  .forallMem _ (.iff (bhit_delta_l ..) (bhit_delta_l ..))

theorem btruthAgreement_sat_l (hE : Extensional M) {d} (ρ : Env M d) (E H J r : Term d) :
    Formula.satisfies ρ (btruthAgreement_m E H J r) ↔
      BtruthAgreement_d (E.eval ρ) (H.eval ρ) (J.eval ρ) (r.eval ρ) := by
  simp only [btruthAgreement_m, BtruthAgreement_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, bhit_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 全部合法内部行在旧完整赋值空间上保值，包含正负嵌套及有界量词。 -/
theorem btruthEval_domain_l (hZF : M.Models ZF) {T ω n X Y E G F L H J : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : BoundedFormula_d T ω n L F)
    (hH : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n X E F L H)
    (hJ : BtruthEval_d (kp_pair_l (ZF.modelsKP hZF)) T n Y G F L J) :
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
    have rowH := btruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 hH hrc hA rowValid
    have rowJ := btruthEval_row_l hKP (fn0_function_l hKP valid.graph).1 hJ hrc hB rowValid
    have hfG := functionSpace_inclusion_l (kp_pair_l hKP) sub he hg f hf
    exact (Bhit_d.value_l hH.1.2.1.2 hA).trans (((rowH f).trans (and_iff_right hf)).trans
      ((btruthNode_domain_l hKP hx sub he hg hf previous rowValid).trans
        (((rowJ f).trans (and_iff_right hfG)).symm.trans (Bhit_d.value_l hJ.1.2.1.2 hB).symm))))
  exact fun r hr => (sat r).mp (all r) hr

/-- 任意两份完整证书也给出相同的旧赋值真值，不要求它们在同一 J 层中。 -/
theorem btruthCertificate_domain_l (hZF : M.Models ZF) {T ω n X Y E G F L Z H W J : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : BoundedFormula_d T ω n L F)
    (hH : BtruthCheck_d T n X E F L Z H) (hJ : BtruthCheck_d T n Y G F L W J) :
    ∀ r, M.mem r L → BtruthAgreement_d E H J r :=
  btruthEval_domain_l hZF hx sub he hg valid
    (btruthEval_of_check_l hZF valid hH) (btruthEval_of_check_l hZF valid hJ)

/-- 正负两个统一 Σ₁ 操作真值模板都在扩大传递求值域时保值。 -/
theorem certifiedTruth_domain_l (hZF : M.Models ZF) (positive : Bool) {T ω n X Y E G F L r f : M.Domain}
    (hx : M.TransitiveSet X) (sub : M.MemberSubset X Y)
    (he : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X)
    (hg : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) G n Y)
    (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) (hf : M.mem f E) :
    CertifiedTruth_d positive T n X E F L r f ↔ CertifiedTruth_d positive T n Y G F L r f := by
  obtain ⟨Z, H, hH⟩ := btruthCertificate_exists_l hZF (X := X) (E := E) valid
  obtain ⟨W, J, hJ⟩ := btruthCertificate_exists_l hZF (X := Y) (E := G) valid
  have eq := btruthCertificate_domain_l hZF hx sub he hg valid hH hJ r hr f hf
  rw [certifiedTruth_value_l hZF positive valid hH, certifiedTruth_value_l hZF positive valid hJ]
  cases positive <;> simp only [BtruthAnswer_d, Bool.false_eq_true, ↓reduceIte, eq]

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
