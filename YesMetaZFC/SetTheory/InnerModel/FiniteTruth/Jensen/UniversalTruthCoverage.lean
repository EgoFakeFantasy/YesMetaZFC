import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1Compiler

/-! # 通用真值表的一条固定源行覆盖整个 Jensen 层

固定源不读取外部谓词 A；其输出与完整见证都取输入。只编译一次源，随后让
实际参数图遍历层内所有输入，得到同一索引行对整个层的成员覆盖。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 原矩阵的槽依次是 w、y、x、A；保护槽 A 不出现。 -/
def universalCover_s : S1_binary 1 where
  matrix := {
    body := .conj (Formula.extensionalEq (.bound 1) (.bound 2))
      (Formula.extensionalEq .newest (.bound 2))
    delta0 := .conj (.atom _ _ _) (.atom _ _ _) }

theorem universalCover_predicate_l :
    PredicateDelta0 (⟨3,by omega⟩ : Fin 4) universalCover_s.matrix.body := by
  apply predicateUseCheck_sound_l universalCover_s.matrix.delta0 (⟨3,by omega⟩ : Fin 4)
  rfl

theorem universalCover_matrix_l (hE : Extensional M) (η : Env M 1) (x y w : M.Domain) :
    Formula.satisfies (((η.push x).push y).push w) universalCover_s.matrix.body ↔
      y = x ∧ w = x := by
  simp only [universalCover_s,Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE] <;> rfl

theorem universalCover_within_l (hE : Extensional M) (η : Env M 1) {C x : M.Domain}
    (hxC : M.mem x C) : Within_d universalCover_s η x x C :=
  ⟨x,hxC,(universalCover_matrix_l hE η x x x).mpr ⟨rfl,rfl⟩⟩

/-- 保留自由变量环境，仅将 A 作为这个固定源的唯一参数。 -/
def universalCover_env_l (ρ : Env M 2) : Env M 1 :=
  ⟨fun _ => ρ.bound 0,ρ.free⟩

theorem universalCover_indexed_env_l (ρ : Env M 2) :
    indexedSource_env_l (universalCover_env_l ρ) (ρ.bound 1) = ρ := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))),rfl⟩

theorem universalCover_values_l (η : Env M 1) (x empty : M.Domain) :
    (fun j : Fin 2 => if j = sigma1SourceSlot_l 0 then empty else (η.push x).bound j) =
      Fin.cases x (fun _ : Fin 1 => empty) := by
  funext j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun h => Fin.elim0 h) i) j
  · rfl
  · rfl

/-- 同一 c、长度 2 和第 0 槽先于 x 选定；每个输入使用真正层内参数图。 -/
theorem jh_universalTruthTable_fullCoverage_l (hZF : M.Models ZF) {α C T : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (amenable : AmenableSet_d C (ρ.bound 0)) (table : UniversalTruthTable_d ρ C T) :
    ∃ c k empty, M.mem c (ρ.bound 1) ∧ M.mem c C ∧
      Num_d 2 k ∧ M.mem k C ∧ Num_d 0 empty ∧ M.mem empty C ∧
      ∀ x, M.mem x C → ∃ X params input,
        M.mem X C ∧ M.TransitiveSet X ∧ M.mem params C ∧ M.mem input C ∧
        Fn0_d k X params ∧ SourceParameter_d (Fin.cases x (fun _ : Fin 1 => empty)) params ∧
        M.mem input T ∧ KPair_d M input c params ∧ Rd_entry_d empty x params := by
  obtain ⟨e,k,empty,c,result⟩ := jh_indexedSigma1_sourceCompile_l hZF (p := 0)
    universalCover_s universalCover_predicate_l hα h hω hωC
  refine ⟨c,k,empty,result.body.index_natural,result.body.index_mem,
    result.body.normalized.count,result.body.normalized.count_mem,
    result.body.normalized.zero,result.body.normalized.empty_mem,?_⟩
  intro x hxC
  let η := universalCover_env_l ρ
  obtain ⟨X,params,input,hXC,hx,hparamsC,hinC,fn,corr,pair,_⟩ :=
    result.realizes_l hZF hα h hω η hxC (fun i : Fin 0 => Fin.elim0 i)
  have existsSource : ∃ y, M.mem y C ∧ Within_d universalCover_s η x y C :=
    ⟨x,hxC,universalCover_within_l hZF.1 η hxC⟩
  obtain ⟨y,hyC,chosen,_,_⟩ :=
    result.local_total_l hZF hα h hω hωC η amenable hinC fn corr pair existsSource
  change Within_d indexedPredicateWitness_s
    (indexedSource_env_l (universalCover_env_l ρ) (ρ.bound 1)) input y C at chosen
  rw [universalCover_indexed_env_l] at chosen
  have table' : RestrictedTruthTable_d indexedPredicateWitness_s ρ (ρ.bound 1) C C T := table
  have hit := (table'.pair_l result.body.index_natural hparamsC pair).mpr ⟨y,hyC,chosen⟩
  have compact : SourceParameter_d (Fin.cases x (fun _ : Fin 1 => empty)) params := by
    simpa only [universalCover_values_l] using corr
  obtain ⟨i,hi,entry⟩ := compact 0
  have eqi := num_unique_l hZF.1 hi result.body.normalized.zero
  have firstEntry : Rd_entry_d empty x params := eqi ▸ entry
  exact ⟨X,params,input,hXC,hx,hparamsC,hinC,fn,compact,hit,pair,firstEntry⟩

/-- 固定一条索引行后，表成员的实际参数图包含 C 的每个成员。 -/
theorem jh_universalTruthTable_coverage_l (hZF : M.Models ZF) {α C T : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 2)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C)
    (amenable : AmenableSet_d C (ρ.bound 0)) (table : UniversalTruthTable_d ρ C T) :
    ∃ c, M.mem c (ρ.bound 1) ∧ M.mem c C ∧
      ∀ x, M.mem x C → ∃ input params i,
        M.mem input T ∧ KPair_d M input c params ∧ Rd_entry_d i x params := by
  obtain ⟨c,k,empty,hc,hcC,_,_,_,_,cover⟩ :=
    jh_universalTruthTable_fullCoverage_l hZF hα h ρ hω hωC amenable table
  refine ⟨c,hc,hcC,?_⟩
  intro x hx
  obtain ⟨X,params,input,_,_,_,_,_,_,hit,pair,entry⟩ := cover x hx
  exact ⟨input,params,empty,hit,pair,entry⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
