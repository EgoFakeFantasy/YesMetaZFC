import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruthHistory

/-! # 同层完整有限空间表的内部归纳

表长 r 的空间表保存所有 i<r 的实际完整赋值空间。归纳每步只追加已经证明
位于该层的 X^r；归纳谓词为原对象公式，并由背景分离提供实际归纳集。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def localSpaceTable_m {d} (C r X : Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest C.weaken) (spaceTable_m r.weaken X.weaken .newest))
derive_free_closed localSpaceTable_m

theorem localSpaceTable_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (C r X : Term d) :
    Formula.satisfies ρ (localSpaceTable_m C r X) ↔
      ∃ S, M.mem S (C.eval ρ) ∧ SpaceTable_d (kp_pair_l hKP) (r.eval ρ) (X.eval ρ) S := by
  simp only [localSpaceTable_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, spaceTable_sat_l hKP,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 点态的同层完整有限空间，经实际内部归纳装配为同层整张表。 -/
theorem rd_spaceTables_l (hZF : M.Models ZF) {C ω X : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (spaces : ∀ r, M.mem r ω → ∃ E, M.mem E C ∧ M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E r X) :
    ∀ r, M.mem r ω → ∃ S, M.mem S C ∧ SpaceTable_d (kp_pair_l (ZF.modelsKP hZF)) r X S := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  let ρ : Env M 2 := ⟨Fin.cases C (fun _ => X), fun _ => C⟩
  let φ : UnarySchema 2 := { body := localSpaceTable_m (.bound 1) .newest (.bound 2) }
  have sat r : φ.denote ρ r ↔ ∃ S, M.mem S C ∧ SpaceTable_d I r X S := by
    simp only [φ, UnarySchema.denote, localSpaceTable_sat_l hKP]
    rfl
  apply hω.induction (fun r => ∃ S, M.mem S C ∧ SpaceTable_d I r X S)
  · obtain ⟨D,hD⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D,fun r => (hD r).trans (and_congr_right fun _ => sat r)⟩
  · intro e he
    have heC : M.mem e C := hC .diff ω ω ω hωC hωC hωC e
      (fun p => iff_of_false (he p) (fun h => h.2 h.1))
    exact ⟨e,heC,Structure.IsSequenceOfLength.empty I he,
      fun i A ⟨p,_,hp⟩ => (he p hp).elim⟩
  · intro r hr ih s hrs
    obtain ⟨S,hSC,hS⟩ := ih
    obtain ⟨E,hEC,hE⟩ := spaces r hr
    have hrC := hc ω hωC r hr
    obtain ⟨K,hKC,snoc⟩ := rd_snoc_exists_l hKP hC hSC hrC hEC
    have hs := KP.successor_isOrdinal hKP (hω.members_areOrdinals hZF r hr) hrs
    obtain ⟨_,entries⟩ := (snoc_iff_entries_l I hS.1.2.1.1).mp snoc
    refine ⟨K,hKC,snoc_sequence_l hKP hs hrs hS.1 snoc,?_⟩
    intro i A hA
    rcases (entries i A).mp hA with old | ⟨rfl,rfl⟩
    · exact hS.2 i A old
    · exact hE

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
