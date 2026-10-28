import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness
import YesMetaZFC.SetTheory.Collapse.RelationSyntax
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 无幂集集合论的原对象理论与集合构造

采用原 KP 加全分离、全收集，不加入 Power Set 或 Choice。这里的公理谓词仅选择
原 Project 句子；后续塌缩在该原理论中证明，不把较弱模型强制当作 ZF 模型。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u

/-- 含无穷的 KP 加全部分离和收集实例。 -/
inductive Axiom : Project.Theory where
  | kp {φ : Sentence} : KP φ → Axiom φ
  | separation {n : Nat} (φ : UnarySchema n) : Axiom (Axioms.Schema.separation φ)
  | collection {n : Nat} (φ : BinarySchema n) : Axiom (Axioms.Schema.collection φ)

abbrev ZFMinus : Project.Theory := Axiom

/-- 无幂集理论的模型保留全部原 KP 公理。 -/
theorem modelsKP_l {M : SetTheory.Structure.{u}} (h : M.Models ZFMinus) : M.Models KP :=
  ⟨h.1, fun φ hφ => h.2 φ (.kp hφ)⟩

/-- 原 ZF 模型也是上述无幂集理论的模型。 -/
theorem models_of_zf_l {M : SetTheory.Structure.{u}} (h : M.Models ZF) : M.Models ZFMinus := by
  refine ⟨h.1, ?_⟩
  intro φ hφ
  cases hφ with
  | kp hφ => exact (ZF.modelsKP h).2 φ hφ
  | separation ψ => exact h.2 _ (.separation ψ)
  | collection ψ => exact h.2 _ (.collection ψ)

/-- 从原分离公理实例取得集合。 -/
theorem separation_exists_d {ℳ : Structure.{u}} (hZF : ℳ.Models ZFMinus)
    {parameterCount : Nat} (schema : Definitional.Project.UnarySchema parameterCount) (env : Env ℳ parameterCount) (source : ℳ.Domain) :
    ∃ subset, ∀ value,
      ℳ.mem value subset ↔
        ℳ.mem value source ∧
          Definitional.Project.Formula.satisfies (env.push value) schema.body := by
  have hSentence :=
    hZF.2 (Axioms.Schema.separation schema) (Axiom.separation schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env (Axioms.Schema.separationCore schema) := by
    have hAll := (Definitional.Project.Formula.satisfies_forallClosure_iff env.free (Axioms.Schema.separationCore schema)).mp hSentence
    simpa only using hAll env.bound
  exact (Axioms.Schema.separation_sat_iff_d env schema).mp
      hCore source

/-- 从原收集公理实例取得共同见证集合。 -/
theorem collection_exists_d {ℳ : Structure.{u}} (hZF : ℳ.Models ZFMinus)
    {parameterCount : Nat} (schema : Definitional.Project.BinarySchema parameterCount) (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output,
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body) :
    ∃ collection, ∀ input, ℳ.mem input source →
      ∃ output, ℳ.mem output collection ∧
        Definitional.Project.Formula.satisfies ((env.push input).push output)
          schema.body := by
  have hSentence :=
    hZF.2 (Axioms.Schema.collection schema) (Axiom.collection schema) env.free
  have hCore :
      Definitional.Project.Formula.satisfies env (Axioms.Schema.collectionCore schema) := by
    have hAll := (Definitional.Project.Formula.satisfies_forallClosure_iff env.free (Axioms.Schema.collectionCore schema)).mp hSentence
    simpa only using hAll env.bound
  exact (Axioms.Schema.collection_sat_iff_d env schema).mp
      hCore source hTotal

/-- 全收集和全分离给出单值关系的精确像。 -/
theorem exists_functionalImageOn {ℳ : Structure.{u}} (hZF : ℳ.Models ZFMinus)
    {parameterCount : Nat} (schema : Definitional.Project.BinarySchema parameterCount) (env : Env ℳ parameterCount) (source : ℳ.Domain)
    (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output) (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second) :
    ∃ image, ∀ output,
      ℳ.mem output image ↔
        ∃ input, ℳ.mem input source ∧
          schema.denote env input output := by
  rcases collection_exists_d hZF schema env source (by simpa [Definitional.Project.BinarySchema.denote] using hTotal) with
    ⟨collection, hCollection⟩
  rcases separation_exists_d hZF schema.imageMembership (env.push source) collection with
    ⟨image, hImage⟩
  refine ⟨image, fun output => ?_⟩
  rw [hImage output,
    Definitional.Project.Formula.satisfies_imageMembership_iff
      env schema source output]
  constructor
  · rintro ⟨_, input, hInput, hOutput⟩
    exact ⟨input, hInput, hOutput⟩
  · rintro ⟨input, hInput, hOutput⟩
    rcases hCollection input hInput with
      ⟨selected, hSelectedMem, hSelected⟩
    have hSelected' : schema.denote env input selected := by
      simpa [Definitional.Project.BinarySchema.denote] using hSelected
    have hEq :=
      hUnique input hInput output selected hOutput hSelected'
    subst selected
    exact ⟨hSelectedMem, input, hInput, hOutput⟩

/-- 用精确像构造实际函数图，无需幂集。 -/
theorem exists_setFunctionFromTo_of_denote
    {ℳ : Structure.{u}} (hZF : ℳ.Models ZFMinus)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (schema : Definitional.Project.BinarySchema parameterCount) (env : Env ℳ parameterCount)
    {source target : ℳ.Domain} (hTotal : ∀ input, ℳ.mem input source →
      ∃ output, schema.denote env input output) (hUnique : ∀ input, ℳ.mem input source → ∀ first second,
      schema.denote env input first →
      schema.denote env input second →
      first = second) (hTarget : ∀ input output,
      ℳ.mem input source →
      schema.denote env input output →
      ℳ.mem output target) :
    ∃ function,
      ℳ.IsSetFunctionFromTo 𝕀 function source target ∧
        ∀ input output,
          ℳ.PairMember 𝕀 input output function ↔
            ℳ.mem input source ∧
              schema.denote env input output := by
  have hGraphTotal :
      ∀ input, ℳ.mem input source →
        ∃ pair, (schema.functionGraph 𝒞).denote env input pair := by
    intro input hInput
    rcases hTotal input hInput with ⟨output, hOutput⟩
    rcases 𝕀.total input output with ⟨pair, hCode⟩
    exact ⟨pair, (Definitional.Project.Formula.denote_functionGraph_iff
        𝕀 schema env input pair).mpr
        ⟨output, hOutput, hCode⟩⟩
  have hGraphUnique :
      ∀ input, ℳ.mem input source → ∀ first second, (schema.functionGraph 𝒞).denote env input first → (schema.functionGraph 𝒞).denote env input second →
        first = second := by
    intro input hInput first second hFirst hSecond
    rcases (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input first).mp hFirst with
      ⟨firstOutput, hFirstValue, hFirstCode⟩
    rcases (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input second).mp hSecond with
      ⟨secondOutput, hSecondValue, hSecondCode⟩
    have hOutputEq :=
      hUnique input hInput firstOutput secondOutput hFirstValue hSecondValue
    subst secondOutput
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImageOn hZF (schema.functionGraph 𝒞) env source hGraphTotal hGraphUnique with
    ⟨function, hFunctionMembers⟩
  have hPairMember (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output function ↔
        ℳ.mem input source ∧ schema.denote env input output := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hFunctionMembers pair).mp hPairMem with
        ⟨sourceInput, hSourceInput, hGraph⟩
      rcases (Definitional.Project.Formula.denote_functionGraph_iff
            𝕀 schema env sourceInput pair).mp hGraph with
        ⟨graphOutput, hValue, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hInputEq, hOutputEq⟩
      subst sourceInput
      subst graphOutput
      exact ⟨hSourceInput, hValue⟩
    · rintro ⟨hInput, hValue⟩
      rcases 𝕀.total input output with ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hFunctionMembers pair).mpr ?_⟩
      exact ⟨input, hInput, (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input pair).mpr
          ⟨output, hValue, hPairCode⟩⟩
  have hRelation : ℳ.IsSetRelation 𝕀 function := by
    intro pair hPair
    rcases (hFunctionMembers pair).mp hPair with
      ⟨input, _, hGraph⟩
    rcases (Definitional.Project.Formula.denote_functionGraph_iff
          𝕀 schema env input pair).mp hGraph with
      ⟨output, _, hCode⟩
    exact ⟨input, output, hCode⟩
  have hSetFunction : ℳ.IsSetFunction 𝕀 function := by
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    exact hUnique input ((hPairMember input first).mp hFirst).1 first second ((hPairMember input first).mp hFirst).2 ((hPairMember input second).mp hSecond).2
  have hDomain : ℳ.IsDomainOf 𝕀 source function := by
    intro input
    constructor
    · intro hInput
      rcases hTotal input hInput with ⟨output, hOutput⟩
      exact ⟨output, (hPairMember input output).mpr ⟨hInput, hOutput⟩⟩
    · rintro ⟨output, hOutput⟩
      exact ((hPairMember input output).mp hOutput).1
  have hIntoTarget :
      ∀ input, ℳ.mem input source →
        ∃ output, ℳ.mem output target ∧
          ℳ.PairMember 𝕀 input output function := by
    intro input hInput
    rcases hTotal input hInput with ⟨output, hOutput⟩
    exact ⟨output, hTarget input output hInput hOutput, (hPairMember input output).mpr ⟨hInput, hOutput⟩⟩
  exact ⟨function, ⟨⟨hSetFunction, hDomain, hIntoTarget⟩, hPairMember⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Powerless
