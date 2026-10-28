import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentSpaceCertificateSyntax

/-! # 完整赋值空间有界证书的可靠性

用实际原公式支持内部 ω 归纳。每行已核验的函数给出可靠性，零行与对全部旧函数、
全部新值的追加闭包给出完整性；不把宿主标准有限长度当作内部长度。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def spaceSound_m {d} (r s X Z S : Term d) : Formula 1 d :=
  .imp (.mem r s) (Formula.forallMem Z (.imp (rd_entry0_m r.weaken .newest S.weaken)
    (Formula.isFunctionSpace kpair_convention_l .newest r.weaken X.weaken)))
derive_free_closed spaceSound_m

theorem spaceSound_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r s X Z S : Term d) :
    Formula.satisfies ρ (spaceSound_m r s X Z S) ↔
      (M.mem (r.eval ρ) (s.eval ρ) → ∀ A, M.mem A (Z.eval ρ) → Rd_entry_d (r.eval ρ) A (S.eval ρ) →
        M.IsFunctionSpace (kp_pair_l hKP) A (r.eval ρ) (X.eval ρ)) := by
  simp only [spaceSound_m, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l hKP) hKP.1,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]

/-- 有界证书确实覆盖全部内部有限赋值，不仅是一个更新闭包子集。 -/
theorem assignmentSpaceCert_sound_l (hZF : M.Models ZF) {ω n X e s Z S E : M.Domain}
    (hω : M.IsOmega ω) (cert : AssignmentSpaceCert_d ω n X e s Z S E) :
    M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  let P (r : M.Domain) := M.mem r s → ∀ A, M.mem A Z → Rd_entry_d r A S → M.IsFunctionSpace I A r X
  let ρ : Env M 4 := ⟨Fin.cases S (Fin.cases Z (Fin.cases X (fun _ => s))), fun _ => s⟩
  let φ : UnarySchema 4 := { body := spaceSound_m .newest (.bound 4) (.bound 3) (.bound 2) (.bound 1) }
  have sat r : φ.denote ρ r ↔ P r := by
    simp only [φ, UnarySchema.denote, spaceSound_sat_l hKP]
    rfl
  have all : ∀ r, M.mem r ω → P r := by
    apply hω.induction P
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨D, fun r => (hD r).trans (and_congr_right fun _ => sat r)⟩
    · intro e0 he0 heS A hAZ hEA
      have eq0 := hZF.1.eq_of_same_members e0 e (fun p => iff_of_false (he0 p) (cert.zero p))
      subst e0
      have singleton : M.IsSingletonOf A e := by
        intro f
        constructor
        · intro hf
          have empty : ∀ p, ¬ M.mem p f := by
            intro p hp
            obtain ⟨i, hi, x, _, _⟩ := (cert.typed e heS A hAZ hEA f hf).1 p hp
            exact cert.zero i hi
          exact hZF.1.eq_of_same_members f e (fun p => iff_of_false (empty p) (cert.zero p))
        · intro eq
          exact eq.symm ▸ cert.base A hAZ hEA
      exact empty_functionSpace_l hKP cert.zero singleton
    · intro r hr ih t hrt htS A hAZ hAt
      have hn := hω.members_areOrdinals hZF n cert.finite
      have hrn : M.mem r n := by
        rcases (cert.successor t).mp htS with htn | eq
        · exact hn.transitive t htn r hrt.predecessor_mem
        · have et := hZF.1.eq_of_same_members t n eq
          exact et ▸ hrt.predecessor_mem
      have hrS := (cert.successor r).mpr (Or.inl hrn)
      obtain ⟨B, hBZ, hBr⟩ := cert.table.2.1 r hrS
      have fullB := ih hrS B hBZ hBr
      intro g
      constructor
      · exact fun hg => fn0_function_l hKP (cert.typed t htS A hAZ hAt g hg)
      · intro hg
        obtain ⟨f, x, hf, hx, snoc⟩ := function_snoc_exists_l I hZF hrt hg
        obtain ⟨q, hqA, check⟩ := cert.step r hrn t htS hrt B hBZ hBr A hAZ hAt f ((fullB f).mpr hf) x hx
        have eq := hZF.1.eq_of_same_members q g (fun p =>
          ((snocCheck_correct_l hKP).mp check p).trans (snoc p).symm)
        exact eq ▸ hqA
  exact all n cert.finite cert.successor.predecessor_mem E (cert.table.bound_l cert.output).2 cert.output

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
