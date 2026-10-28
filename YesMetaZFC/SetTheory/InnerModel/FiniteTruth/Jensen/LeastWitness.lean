import YesMetaZFC.SetTheory.InnerModel.Order.Global
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness
import YesMetaZFC.Model.SetTheory.KPInduction

/-! # Δ₀ 关系的规范最小构造性见证

使用完整全局初段，把最小性的否定检查限制在一个实际集合内。
输出图有一个携带 Δ₀ 矩阵证书的 Σ₁ 正规形；不是任意选择图。
这里仍按宿主的固定 Δ₀ 模板索引，内部全部公式码的统一 Skolem 图另行建设。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

def LeastWitness_d {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (x y : M.Domain) : Prop :=
  L_d y ∧ φ.toBinarySchema.denote ρ x y ∧
    ∀ z, Js_lt_d z y → ¬ φ.toBinarySchema.denote ρ x z

/-- 三歧性保证规范见证唯一，而不需要任意选择函数。 -/
theorem leastWitness_unique_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) {x y z : M.Domain}
    (hy : LeastWitness_d φ ρ x y) (hz : LeastWitness_d φ ρ x z) : y = z := by
  rcases js_compare_l hM hy.1 hz.1 with he | hlt | hgt
  · exact he
  · exact (hz.2.2 y hlt hy.2.1).elim
  · exact (hy.2.2 z hgt hz.2.1).elim

/-- 一份已有构造性见证的完整初段足以界住规范搜索。 -/
theorem leastWitness_exists_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) {x y : M.Domain} (hy : L_d y) (hφ : φ.toBinarySchema.denote ρ x y) :
    ∃ z, LeastWitness_d φ ρ x z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨I, _, hi⟩ := js_initial_exists_l hM hy
  obtain ⟨A, hA⟩ := KP.exists_insert hKP I y
  let δ : Delta0UnarySchema (n + 1) := {
    body := φ.body
    freeClosed := φ.freeClosed
    delta0 := φ.delta0 }
  obtain ⟨X, hX'⟩ := KP.separation_exists_d hKP δ (ρ.push x) A
  have hX z : M.mem z X ↔ M.mem z A ∧ φ.toBinarySchema.denote ρ x z := hX' z
  have inL z (hz : M.mem z X) : L_d z := by
    rcases (hA z).mp ((hX z).mp hz).1 with hzI | he
    · exact (js_domain_l hM ((hi.2 z).mp hzI)).1
    · exact he ▸ hy
  have hyX : M.mem y X := (hX y).mpr ⟨(hA y).mpr (Or.inr rfl), hφ⟩
  obtain ⟨z, hzX, hmin⟩ := js_min_l hM inL ⟨y, hyX⟩
  refine ⟨z, inL z hzX, ((hX z).mp hzX).2, ?_⟩
  intro w hwz hw
  have hwy : Js_lt_d w y := by
    rcases (hA z).mp ((hX z).mp hzX).1 with hzI | he
    · exact js_trans_l hM hwz ((hi.2 z).mp hzI)
    · exact he ▸ hwz
  have hwX : M.mem w X := (hX w).mpr ⟨(hA w).mpr (Or.inl ((hi.2 w).mpr hwy)), hw⟩
  rcases hmin w hwX with he | hzw
  · exact js_irrefl_l hM z (he ▸ hwz)
  · exact js_irrefl_l hM w (js_trans_l hM hwz hzw)

private def leastParams (n offset : Nat) : Fin n → Term (n + offset) :=
  fun i => .bound ⟨i.val + offset, by omega⟩

/-- 对输入 x 和输出 y，猜测其全局初段及完整初段证书。 -/
def leastWitness_s {n} (φ : Delta0BinarySchema n) : S1_binary n where
  matrix := {
    -- 量词后的槽位为 T,I,B,y,x,参数；B 是唯一无界存在见证。
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <|
      .conj (js_initial_s.matrix_m Fin.elim0 (.bound 3) (.bound 1) .newest) <|
        .conj (binary_pred_m φ.toBinarySchema (leastParams n 5) (.bound 4) (.bound 3)) <|
          Formula.forallMem (.bound 1) <|
            .neg (binary_pred_m φ.toBinarySchema (leastParams n 6) (.bound 5) .newest)
    freeClosed := by simp -implicitDefEqProofs [YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, leastParams]
    delta0 := .existsMem _ (.existsMem _ (.conj (js_initial_s.matrix.delta0.bind_l _)
      (.conj (φ.delta0.bind_l _) (.forallMem _ (.neg (φ.delta0.bind_l _)))))) }

private theorem leastWitness_matrix_l {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) (x y B : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push B) (leastWitness_s φ).matrix.body ↔
      ∃ I, M.mem I B ∧ ∃ T, M.mem T B ∧
        Formula.satisfies ((((⟨Fin.elim0, ρ.free⟩ : Env M 0).push y).push I).push T)
          js_initial_s.matrix.body ∧ φ.toBinarySchema.denote ρ x y ∧
          ∀ z, M.mem z I → ¬ φ.toBinarySchema.denote ρ x z := by
  simp only [leastWitness_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    S1_binary.matrix_sat_l, binary_pred_sat_l, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, leastParams]
  apply exists_congr
  intro I
  apply and_congr_right
  intro _
  apply exists_congr
  intro T
  apply and_congr_right
  intro _
  apply and_congr
  · exact Formula.closed_env_l _ js_initial_s.matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  · rfl

/-- 实际 Σ₁ 正规形准确表达规范最小见证。 -/
theorem leastWitness_sat_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) (x y : M.Domain) :
    (leastWitness_s φ).schema.denote ρ x y ↔ LeastWitness_d φ ρ x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let η : Env M 0 := ⟨Fin.elim0, ρ.free⟩
  rw [S1_binary.sat_l]
  simp only [leastWitness_matrix_l]
  constructor
  · rintro ⟨B, I, _, T, _, ht, hφ, hmin⟩
    have hi := (js_initial_sat_l hM η y I).mp ((js_initial_s.sat_l η y I).mpr ⟨T, ht⟩)
    exact ⟨hi.1, hφ, fun z hz => hmin z ((hi.2 z).mpr hz)⟩
  · intro hy
    obtain ⟨I, _, hi⟩ := js_initial_exists_l hM hy.1
    obtain ⟨T, ht⟩ := (js_initial_s.sat_l η y I).mp ((js_initial_sat_l hM η y I).mpr hi)
    obtain ⟨B, hB⟩ := KP.exists_pair hKP I T
    exact ⟨B, I, (hB I).mpr (Or.inl rfl), T, (hB T).mpr (Or.inr rfl), ht,
      hy.2.1, fun z hz => hy.2.2 z ((hi.2 z).mp hz)⟩


/-- 同一规范图在每个包含输入、输出和参数的 J 层中都准确；不要求该层满足 KP。 -/
theorem jh_leastWitness_local_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : Delta0BinarySchema n)
    (ρ : Env (rt_model_l C hn) n) (x y : (rt_model_l C hn).Domain) :
    (leastWitness_s φ).schema.denote ρ x y ↔
      LeastWitness_d φ (image_env_l Subtype.val ρ) x.val y.val := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let hc := jh_value_transitive_l hM h
  let hC := jh_value_closed_l hM ha h
  let η := image_env_l Subtype.val ρ
  have matrix (B : (rt_model_l C hn).Domain) :
      Formula.satisfies (((ρ.push x).push y).push B) (leastWitness_s φ).matrix.body ↔
        Formula.satisfies (((η.push x.val).push y.val).push B.val)
          (leastWitness_s φ).matrix.body := by
    apply (rt_model_delta_l hc hn (leastWitness_s φ).matrix.delta0 _).trans
    exact Formula.closed_env_l _ (leastWitness_s φ).matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  rw [S1_binary.sat_l]
  constructor
  · rintro ⟨B, hB⟩
    exact (leastWitness_sat_l hM φ η x.val y.val).mp
      ((S1_binary.sat_l _ η x.val y.val).mpr ⟨B.val, (matrix B).mp hB⟩)
  · intro hy
    obtain ⟨I, hIC, hi⟩ := jh_initial_in_l hM ha h y.property
    let ζ : Env M 0 := ⟨Fin.elim0, η.free⟩
    obtain ⟨T, hTC, ht⟩ := js_initial_cert_in_l hM hC hc
      (js_rep_access_l hM hC (jh_order_rep_l hM ha h) y.val y.property) hi ζ
    obtain ⟨B, hB⟩ := KP.exists_pair hKP I T
    have hBC : M.mem B C := hC .pair I T T hIC hTC hTC B hB
    refine ⟨⟨B, hBC⟩, (matrix ⟨B, hBC⟩).mpr ?_⟩
    apply (leastWitness_matrix_l φ η x.val y.val B).mpr
    exact ⟨I, (hB I).mpr (Or.inl rfl), T, (hB T).mpr (Or.inr rfl),
      (js_initial_matrix_l hKP ζ y.val I T).mpr ht, hy.2.1,
      fun z hz => hy.2.2 z ((hi.2 z).mp hz)⟩

/-- 对任何已知见证，规范值都在它之前或与它相等。 -/
theorem leastWitness_le_l (hM : M.Models KPi) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) {x y z : M.Domain} (hz : LeastWitness_d φ ρ x z)
    (hy : L_d y) (hφ : φ.toBinarySchema.denote ρ x y) : z = y ∨ Js_lt_d z y := by
  rcases js_compare_l hM hz.1 hy with he | hlt | hgt
  · exact Or.inl he
  · exact Or.inr hlt
  · exact (hz.2.2 y hgt hφ).elim

/-- 有界矩阵在任意传递层中的解释与背景一致。 -/
theorem delta0Binary_local_l {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : Delta0BinarySchema n)
    (ρ : Env (rt_model_l C hn) n) (x y : (rt_model_l C hn).Domain) :
    φ.toBinarySchema.denote ρ x y ↔
      φ.toBinarySchema.denote (image_env_l Subtype.val ρ) x.val y.val := by
  apply (rt_model_delta_l hc hn φ.delta0 ((ρ.push x).push y)).trans
  exact Formula.closed_env_l _ φ.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))

/-- 一旦层内存在 Δ₀ 见证，规范图在同一层内有唯一输出；不使用层内收集。 -/
theorem jh_leastWitness_function_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : Delta0BinarySchema n)
    (ρ : Env (rt_model_l C hn) n) (x : (rt_model_l C hn).Domain)
    (he : ∃ y, φ.toBinarySchema.denote ρ x y) :
    ∃ z : (rt_model_l C hn).Domain, (leastWitness_s φ).schema.denote ρ x z ∧
      ∀ w, (leastWitness_s φ).schema.denote ρ x w → w = z := by
  obtain ⟨y, hy⟩ := he
  let η := image_env_l Subtype.val ρ
  let hc := jh_value_transitive_l hM h
  have hyL : L_d y.val := ⟨a, C, ⟨ha, h⟩, y.property⟩
  have hφ := (delta0Binary_local_l hc hn φ ρ x y).mp hy
  obtain ⟨z, hz⟩ := leastWitness_exists_l hM φ η hyL hφ
  have hzC : M.mem z C := by
    rcases leastWitness_le_l hM φ η hz hyL hφ with heq | hlt
    · exact heq ▸ y.property
    · obtain ⟨I, hIC, hi⟩ := jh_initial_in_l hM ha h y.property
      exact hc I hIC z ((hi.2 z).mpr hlt)
  refine ⟨⟨z, hzC⟩, (jh_leastWitness_local_l hM ha h hn φ ρ x ⟨z, hzC⟩).mpr hz, ?_⟩
  intro w hw
  exact Subtype.ext (leastWitness_unique_l hM φ η
    ((jh_leastWitness_local_l hM ha h hn φ ρ x w).mp hw) hz)

private def leastUniqueBody {n} (φ : Delta0BinarySchema n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp
    (.conj (binary_pred_m (leastWitness_s φ).schema (leastParams n 3) (.bound 2) (.bound 1))
      (binary_pred_m (leastWitness_s φ).schema (leastParams n 3) (.bound 2) .newest))
    (Formula.extensionalEq (.bound 1) .newest))))

/-- 对每个固定 Δ₀ 模板，规范 Σ₁ 图的单值性是原对象句子。 -/
def leastWitnessUnique {n} (φ : Delta0BinarySchema n) : Sentence :=
  Sentence.forallClosure (leastUniqueBody φ)
    (by simp -implicitDefEqProofs [leastUniqueBody,
      YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, leastParams])

theorem leastWitnessUnique_models {n} (φ : Delta0BinarySchema n)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (leastWitnessUnique φ) := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0)
    (Formula.forallClosure n (leastUniqueBody φ))
  apply (Formula.satisfies_forallClosure_iff f (leastUniqueBody φ)).mpr
  intro b
  let ρ : Env M n := ⟨b, f⟩
  change Formula.satisfies ρ (leastUniqueBody φ)
  simp only [leastUniqueBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, binary_pred_sat_l,
    leastWitness_sat_l (ZF.models_kpi_l hZF), Formula.satisfies_extensionalEq_iff_eq hZF.1]
  intro x y z
  change LeastWitness_d φ ρ x y ∧ LeastWitness_d φ ρ x z → y = z
  intro h
  exact leastWitness_unique_l (ZF.models_kpi_l hZF) φ ρ h.1 h.2

/-- 新构造的规范见证图在原 ZF 中有逐模板的单值性推导。 -/
theorem leastWitnessUnique_derives {n} (φ : Delta0BinarySchema n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (leastWitnessUnique φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => leastWitnessUnique_models φ M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
