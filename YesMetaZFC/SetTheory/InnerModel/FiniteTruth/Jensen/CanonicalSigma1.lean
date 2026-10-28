import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.Sigma1Local
import YesMetaZFC.SetTheory.InnerModel.Jensen.Model

/-! # Σ₁ 关系的规范选取

先在 Jensen 规范序中选取最小的输出与见证对，再投影到输出。固定模板的
构造不使用任意选择；内部全部公式码的统一 Skolem 图仍需单独编码。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

private def pairParams (n offset : Nat) : Fin n → Term (n + offset) :=
  fun i => .bound ⟨i.val + offset, by omega⟩

/-- 输出及见证都沿有序对的成员路径取出，因此配对后的关系仍是 Δ₀。 -/
def pairedMatrix {n} (φ : S1_binary n) : Delta0BinarySchema n where
  body := Formula.existsMem .newest <| Formula.existsMem .newest <|
    Formula.existsMem (.bound 1) <|
      .conj (kpair0_m (.bound 3) (.bound 1) .newest)
        (φ.matrix_m (pairParams n 5) (.bound 4) (.bound 1) .newest)
  freeClosed := by simp -implicitDefEqProofs [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, pairParams]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (φ.matrix.delta0.bind_l _))))

theorem pairedMatrix_sat_l (hE : Extensional M) {n} (φ : S1_binary n)
    (ρ : Env M n) (x p : M.Domain) :
    (pairedMatrix φ).toBinarySchema.denote ρ x p ↔
      ∃ y w, KPair_d M p y w ∧
        Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
  simp only [pairedMatrix, BinarySchema.denote, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, kpair0_sat_l hE, S1_binary.matrix_sat_l, pairParams]
  change (∃ t, M.mem t p ∧ ∃ y, M.mem y t ∧ ∃ w, M.mem w t ∧
    KPair_d M p y w ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) ↔ _
  constructor
  · rintro ⟨_, _, y, _, w, _, hp, hw⟩
    exact ⟨y, w, hp, hw⟩
  · rintro ⟨y, w, hp, hw⟩
    have hpCopy := hp
    obtain ⟨s, t, _, ht, hpt⟩ := hp
    exact ⟨t, (hpt t).mpr (Or.inr rfl), y, (ht y).mpr (Or.inl rfl),
      w, (ht w).mpr (Or.inr rfl), hpCopy, hw⟩

/-- 第一投影只需沿输入的两条成员边寻找第二坐标。 -/
def firstProjection (n : Nat) : Delta0BinarySchema n where
  body := Formula.existsMem (.bound 1) <| Formula.existsMem .newest <|
    kpair0_m (.bound 3) (.bound 2) .newest
  freeClosed := by simp -implicitDefEqProofs
  delta0 := .existsMem _ (.existsMem _ (kpair0_delta_l ..))

theorem firstProjection_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p y : M.Domain) :
    (firstProjection n).toBinarySchema.denote ρ p y ↔ ∃ w, KPair_d M p y w := by
  simp only [firstProjection, BinarySchema.denote, Formula.satisfies_existsMem_iff,
    kpair0_sat_l hE]
  change (∃ t, M.mem t p ∧ ∃ w, M.mem w t ∧ KPair_d M p y w) ↔ _
  constructor
  · rintro ⟨_, _, w, _, hw⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨t, ht, hwt⟩ := (kpair_union_l M hw w).mpr (Or.inr rfl)
    exact ⟨t, ht, w, hwt, hw⟩

/-- 规范图通过最小见证对和第一投影的实际 Σ₁ 复合给出。 -/
def canonicalPick_s {n} (φ : S1_binary n) : S1_binary n :=
  (leastWitness_s (pairedMatrix φ)).comp (S1_binary.of_delta0 (firstProjection n))

def CanonicalPick_d {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) : Prop :=
  ∃ p, LeastWitness_d (pairedMatrix φ) ρ x p ∧ ∃ w, KPair_d M p y w

theorem canonicalPick_sat_l (hM : M.Models KPi) {n} (φ : S1_binary n)
    (ρ : Env M n) (x y : M.Domain) :
    (canonicalPick_s φ).schema.denote ρ x y ↔ CanonicalPick_d φ ρ x y := by
  simp only [canonicalPick_s, S1_binary.comp_sat_l (KPi.models_iff_l.mp hM).1,
    S1_binary.of_delta0_sat_l, leastWitness_sat_l hM,
    firstProjection_sat_l (KPi.models_iff_l.mp hM).1.1, CanonicalPick_d]

theorem canonicalPick_unique_l (hM : M.Models KPi) {n} (φ : S1_binary n)
    (ρ : Env M n) {x y z : M.Domain}
    (hy : CanonicalPick_d φ ρ x y) (hz : CanonicalPick_d φ ρ x z) : y = z := by
  obtain ⟨p, hp, w, hpy⟩ := hy
  obtain ⟨q, hq, v, hqz⟩ := hz
  have eq := leastWitness_unique_l hM (pairedMatrix φ) ρ hp hq
  subst q
  exact (kpair_injective_l M hpy hqz).1

/-- 规范投影的输出满足原 Σ₁ 关系。 -/
theorem canonicalPick_sound_l (hM : M.Models KPi) {n} (φ : S1_binary n)
    (ρ : Env M n) {x y : M.Domain} (hy : CanonicalPick_d φ ρ x y) :
    φ.schema.denote ρ x y := by
  obtain ⟨p, hp, w, hpy⟩ := hy
  obtain ⟨z, v, hpz, hv⟩ := (pairedMatrix_sat_l (KPi.models_iff_l.mp hM).1.1 φ ρ x p).mp hp.2.1
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hpz hpy
  exact (φ.sat_l ρ x z).mpr ⟨v, hv⟩

/-- 构造性输出及见证存在时，规范选取确实有输出。 -/
theorem canonicalPick_exists_l (hM : M.Models KPi) {n} (φ : S1_binary n)
    (ρ : Env M n) {x y w : M.Domain} (hy : L_d y) (hw : L_d w)
    (hφ : Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) :
    ∃ z, CanonicalPick_d φ ρ x z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total y w
  have hpL := l_closed_l hM .opair hy hw hw (rd_opair_value_l hKP.1 hp)
  obtain ⟨q, hq⟩ := leastWitness_exists_l hM (pairedMatrix φ) ρ hpL
    ((pairedMatrix_sat_l hKP.1 φ ρ x p).mpr ⟨y, w, hp, hφ⟩)
  obtain ⟨z, v, hqz, _⟩ := (pairedMatrix_sat_l hKP.1 φ ρ x q).mp hq.2.1
  exact ⟨z, q, hq, v, hqz⟩

/-- 层内图准确等价于规范见证对位于该层；仅输出位于该层并不足够。 -/
theorem jh_canonicalPick_local_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) (x y : (rt_model_l C hn).Domain) :
    (canonicalPick_s φ).schema.denote ρ x y ↔
      ∃ p : (rt_model_l C hn).Domain,
        LeastWitness_d (pairedMatrix φ) (image_env_l Subtype.val ρ) x.val p.val ∧
          ∃ w, KPair_d M p.val y.val w := by
  simp only [canonicalPick_s, rt_s1_comp_sat_l (KPi.models_iff_l.mp hM).1
    (jh_value_closed_l hM ha h) hn, S1_binary.of_delta0_sat_l,
    jh_leastWitness_local_l hM ha h hn,
    delta0Binary_local_l (jh_value_transitive_l hM h) hn,
    firstProjection_sat_l (KPi.models_iff_l.mp hM).1.1]

/-- 层内规范图确实给出原 Σ₁ 关系的层内见证。 -/
theorem jh_canonicalPick_sound_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) {x y : (rt_model_l C hn).Domain}
    (hy : (canonicalPick_s φ).schema.denote ρ x y) : φ.schema.denote ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let hc := jh_value_transitive_l hM h
  let η := image_env_l Subtype.val ρ
  obtain ⟨p, hp, w, hpw⟩ := (jh_canonicalPick_local_l hM ha h hn φ ρ x y).mp hy
  have hwC := (po_pair_bound_l hc p.property hpw).2
  have hφ : Formula.satisfies (((η.push x.val).push y.val).push w) φ.matrix.body := by
    obtain ⟨z, v, hpz, hv⟩ := (pairedMatrix_sat_l hKP.1 φ η x.val p.val).mp hp.2.1
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hpz hpw
    exact hv
  exact (φ.sat_l ρ x y).mpr ⟨⟨w, hwC⟩, (s1_matrix_local_l hc hn φ ρ x y ⟨w, hwC⟩).mpr hφ⟩

/-- 层内存在原 Σ₁ 输出时，同一层内有唯一的规范输出。 -/
theorem jh_canonicalPick_function_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) (x : (rt_model_l C hn).Domain)
    (he : ∃ y, φ.schema.denote ρ x y) :
    ∃ z : (rt_model_l C hn).Domain, (canonicalPick_s φ).schema.denote ρ x z ∧
      ∀ v, (canonicalPick_s φ).schema.denote ρ x v → v = z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let hc := jh_value_transitive_l hM h
  let hC := jh_value_closed_l hM ha h
  let η := image_env_l Subtype.val ρ
  obtain ⟨y, hy⟩ := he
  obtain ⟨w, hw⟩ := (φ.sat_l ρ x y).mp hy
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total y.val w.val
  have hpC := hC .opair y.val w.val w.val y.property w.property w.property p
    (rd_opair_value_l hKP.1 hp)
  have hpφ : (pairedMatrix φ).toBinarySchema.denote ρ x ⟨p, hpC⟩ :=
    (delta0Binary_local_l hc hn (pairedMatrix φ) ρ x ⟨p, hpC⟩).mpr
      ((pairedMatrix_sat_l hKP.1 φ η x.val p).mpr
        ⟨y.val, w.val, hp, (s1_matrix_local_l hc hn φ ρ x y w).mp hw⟩)
  obtain ⟨q, hq, _⟩ := jh_leastWitness_function_l hM ha h hn (pairedMatrix φ) ρ x ⟨⟨p, hpC⟩, hpφ⟩
  have hqMin := (jh_leastWitness_local_l hM ha h hn (pairedMatrix φ) ρ x q).mp hq
  obtain ⟨z, v, hqz, _⟩ := (pairedMatrix_sat_l hKP.1 φ η x.val q.val).mp hqMin.2.1
  have hzC := (po_pair_bound_l hc q.property hqz).1
  refine ⟨⟨z, hzC⟩, (jh_canonicalPick_local_l hM ha h hn φ ρ x ⟨z, hzC⟩).mpr
    ⟨q, hqMin, v, hqz⟩, ?_⟩
  intro t ht
  obtain ⟨r, hr, s, hrs⟩ := (jh_canonicalPick_local_l hM ha h hn φ ρ x t).mp ht
  exact Subtype.ext (canonicalPick_unique_l hM φ η ⟨r.val, hr, s, hrs⟩ ⟨q.val, hqMin, v, hqz⟩)

/-- 包含关系所给的实际层嵌入，不作任何见证选择。 -/
def rt_include_l {C D : M.Domain} (hCD : M.MemberSubset C D)
    (hnC : Nonempty {x : M.Domain // M.mem x C})
    (hnD : Nonempty {x : M.Domain // M.mem x D})
    (x : (rt_model_l C hnC).Domain) : (rt_model_l D hnD).Domain :=
  ⟨x.val, hCD x.val x.property⟩

/-- 同一规范图沿嵌套 J 层向上保值；不假设两层之间已有初等性。 -/
theorem jh_canonicalPick_up_l (hM : M.Models KPi) {a b C D : M.Domain}
    (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hC : Jh_value_d a C) (hD : Jh_value_d b D)
    (hCD : M.MemberSubset C D)
    (hnC : Nonempty {x : M.Domain // M.mem x C})
    (hnD : Nonempty {x : M.Domain // M.mem x D}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hnC) n) (x y : (rt_model_l C hnC).Domain)
    (hy : (canonicalPick_s φ).schema.denote ρ x y) :
    (canonicalPick_s φ).schema.denote (image_env_l (rt_include_l hCD hnC hnD) ρ)
      (rt_include_l hCD hnC hnD x) (rt_include_l hCD hnC hnD y) := by
  obtain ⟨p, hp, w, hpw⟩ := (jh_canonicalPick_local_l hM ha hC hnC φ ρ x y).mp hy
  apply (jh_canonicalPick_local_l hM hb hD hnD φ
    (image_env_l (rt_include_l hCD hnC hnD) ρ)
    (rt_include_l hCD hnC hnD x) (rt_include_l hCD hnC hnD y)).mpr
  refine ⟨rt_include_l hCD hnC hnD p, ?_, w, hpw⟩
  exact hp

private def pickSpecificationBody {n} (φ : S1_binary n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (binary_pred_m (canonicalPick_s φ).schema (pairParams n 2) (.bound 1) .newest)
    (.conj (binary_pred_m φ.schema (pairParams n 2) (.bound 1) .newest)
      (.forallE (.imp
        (binary_pred_m (canonicalPick_s φ).schema (pairParams n 3) (.bound 2) .newest)
        (Formula.extensionalEq .newest (.bound 1)))))))

/-- 每个固定 Σ₁ 模板的规范图满足原关系且单值，陈述为原对象闭句。 -/
def canonicalPickSpecification {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (pickSpecificationBody φ)
    (by simp -implicitDefEqProofs [pickSpecificationBody,
      YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, pairParams])

theorem canonicalPickSpecification_models {n} (φ : S1_binary n)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalPickSpecification φ) := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0)
    (Formula.forallClosure n (pickSpecificationBody φ))
  apply (Formula.satisfies_forallClosure_iff f (pickSpecificationBody φ)).mpr
  intro b
  let ρ : Env M n := ⟨b, f⟩
  change Formula.satisfies ρ (pickSpecificationBody φ)
  simp only [pickSpecificationBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, binary_pred_sat_l, canonicalPick_sat_l (ZF.models_kpi_l hZF),
    Formula.satisfies_extensionalEq_iff_eq hZF.1]
  intro x y
  change CanonicalPick_d φ ρ x y → φ.schema.denote ρ x y ∧
    ∀ z, CanonicalPick_d φ ρ x z → z = y
  intro hy
  exact ⟨canonicalPick_sound_l (ZF.models_kpi_l hZF) φ ρ hy,
    fun z hz => canonicalPick_unique_l (ZF.models_kpi_l hZF) φ ρ hz hy⟩

/-- 原 ZF 推导核中的逐模板规范选取证书。 -/
theorem canonicalPickSpecification_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPickSpecification φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalPickSpecification_models φ M hM)

/-- 已有低层见证时，高层规范输出被低层捕获。 -/
theorem jh_canonicalPick_capture_l (hM : M.Models KPi) {a b C D : M.Domain}
    (ha : M.IsOrdinal a) (hb : M.IsOrdinal b) (hC : Jh_value_d a C) (hD : Jh_value_d b D)
    (hCD : M.MemberSubset C D)
    (hnC : Nonempty {x : M.Domain // M.mem x C})
    (hnD : Nonempty {x : M.Domain // M.mem x D}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hnC) n) (x : (rt_model_l C hnC).Domain)
    (he : ∃ z, φ.schema.denote ρ x z) (y : (rt_model_l D hnD).Domain)
    (hy : (canonicalPick_s φ).schema.denote (image_env_l (rt_include_l hCD hnC hnD) ρ)
      (rt_include_l hCD hnC hnD x) y) :
    ∃ z : (rt_model_l C hnC).Domain, (canonicalPick_s φ).schema.denote ρ x z ∧
      rt_include_l hCD hnC hnD z = y := by
  obtain ⟨z, hz, _⟩ := jh_canonicalPick_function_l hM ha hC hnC φ ρ x he
  refine ⟨z, hz, Subtype.ext ?_⟩
  have hzD := jh_canonicalPick_up_l hM ha hb hC hD hCD hnC hnD φ ρ x z hz
  let η := image_env_l (rt_include_l hCD hnC hnD) ρ
  obtain ⟨p, hp, w, hpw⟩ := (jh_canonicalPick_local_l hM hb hD hnD φ η
    (rt_include_l hCD hnC hnD x) (rt_include_l hCD hnC hnD z)).mp hzD
  obtain ⟨q, hq, v, hqv⟩ := (jh_canonicalPick_local_l hM hb hD hnD φ η
    (rt_include_l hCD hnC hnD x) y).mp hy
  exact canonicalPick_unique_l hM φ (image_env_l Subtype.val η)
    ⟨p.val, hp, w, hpw⟩ ⟨q.val, hq, v, hqv⟩

private def pickTotalBody {n} (φ : S1_binary n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp
    (.conj (l_m (.bound 1)) (.conj (l_m .newest)
      (φ.matrix_m (pairParams n 3) (.bound 2) (.bound 1) .newest)))
    (.existsE (binary_pred_m (canonicalPick_s φ).schema (pairParams n 4) (.bound 3) .newest)))))

/-- 当原输出和存在见证均构造时，规范图有输出，陈述为原对象闭句。 -/
def canonicalPickTotal {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (pickTotalBody φ)
    (by simp -implicitDefEqProofs [pickTotalBody,
      YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, pairParams])

theorem canonicalPickTotal_models {n} (φ : S1_binary n)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalPickTotal φ) := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0)
    (Formula.forallClosure n (pickTotalBody φ))
  apply (Formula.satisfies_forallClosure_iff f (pickTotalBody φ)).mpr
  intro b
  let ρ : Env M n := ⟨b, f⟩
  change Formula.satisfies ρ (pickTotalBody φ)
  simp only [pickTotalBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, binary_pred_sat_l,
    S1_binary.matrix_sat_l, l_sat_l (ZF.modelsKP hZF),
    canonicalPick_sat_l (ZF.models_kpi_l hZF)]
  intro x y w
  change (L_d y ∧ L_d w ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) →
    ∃ z, CanonicalPick_d φ ρ x z
  intro hy
  exact canonicalPick_exists_l (ZF.models_kpi_l hZF) φ ρ hy.1 hy.2.1 hy.2.2

/-- 原 ZF 中对每个固定 Σ₁ 模板的规范图存在性推导。 -/
theorem canonicalPickTotal_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPickTotal φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalPickTotal_models φ M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
