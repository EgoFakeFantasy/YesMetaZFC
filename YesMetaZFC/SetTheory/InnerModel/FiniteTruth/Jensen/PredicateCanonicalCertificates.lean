import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateFormulaCertificates

/-! # 同一规范 Σ₁ 选择器保持指定集合谓词的专用出现 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

private theorem bound_apart_l {d} {i j : Fin d} (ne : i.val ≠ j.val) :
    (Term.bound i : Term d) ≠ .bound j := fun eq => ne (congrArg Fin.val (Definitional.Term.bound.inj eq))

theorem pairedMatrix_predicate_l {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    PredicateDelta0 (⟨2,by omega⟩ : Fin (p+3)) (pairedMatrix φ).body := by
  unfold pairedMatrix
  refine .existsMem _ _ (by apply bound_apart_l; change (0 : Nat) ≠ 2; decide) <|
    .existsMem _ _ (by apply bound_apart_l; change (0 : Nat) ≠ 3; decide) <|
      .existsMem _ _ (by apply bound_apart_l; change (1 : Nat) ≠ 4; decide) <| .conj ?_ ?_
  · exact predicate_kpair0_l _ _ _ _ (by apply bound_apart_l; change (3 : Nat) ≠ 5; decide) (by apply bound_apart_l; change (1 : Nat) ≠ 5; decide) (by apply bound_apart_l; change (0 : Nat) ≠ 5; decide)
  · refine predicate_matrix_l φ useCert _ _ ?_ ?_ _ _ _ ?_ ?_ ?_
    · rfl
    · intro i ne eq
      apply ne
      apply Fin.ext
      have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
      change i.val+5 = 5 at vals
      change i.val = 0
      omega
    · apply bound_apart_l; change (4 : Nat) ≠ 5; decide
    · apply bound_apart_l; change (1 : Nat) ≠ 5; decide
    · apply bound_apart_l; change (0 : Nat) ≠ 5; decide

theorem leastWitness_predicate_l {p} (φ : Delta0BinarySchema (p+1))
    (useCert : PredicateDelta0 (⟨2,by omega⟩ : Fin (p+3)) φ.body) :
    PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) (leastWitness_s φ).matrix.body := by
  unfold leastWitness_s
  refine .existsMem _ _ (by apply bound_apart_l; change (0 : Nat) ≠ 3; decide) <|
    .existsMem _ _ (by apply bound_apart_l; change (1 : Nat) ≠ 4; decide) <| .conj ?_ (.conj ?_ ?_)
  · refine ordinary_matrix_predicate_l js_initial_s _ Fin.elim0 (fun i => Fin.elim0 i) _ _ _ ?_ ?_ ?_
    · apply bound_apart_l; change (3 : Nat) ≠ 5; decide
    · apply bound_apart_l; change (1 : Nat) ≠ 5; decide
    · apply bound_apart_l; change (0 : Nat) ≠ 5; decide
  · refine predicate_binary_pred_l φ.toBinarySchema useCert _ _ ?_ ?_ _ _ ?_ ?_
    · rfl
    · intro i ne eq
      apply ne
      apply Fin.ext
      have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
      change i.val+5 = 5 at vals
      change i.val = 0
      omega
    · apply bound_apart_l; change (4 : Nat) ≠ 5; decide
    · apply bound_apart_l; change (3 : Nat) ≠ 5; decide
  · refine .forallMem _ _ (by apply bound_apart_l; change (1 : Nat) ≠ 5; decide) (.neg ?_)
    refine predicate_binary_pred_l φ.toBinarySchema useCert _ _ ?_ ?_ _ _ ?_ ?_
    · rfl
    · intro i ne eq
      apply ne
      apply Fin.ext
      have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
      change i.val+6 = 6 at vals
      change i.val = 0
      omega
    · apply bound_apart_l; change (5 : Nat) ≠ 6; decide
    · apply bound_apart_l; change (0 : Nat) ≠ 6; decide

theorem firstProjection_predicate_l (p : Nat) :
    PredicateDelta0 (⟨2,by omega⟩ : Fin (p+3)) (firstProjection (p+1)).body := by
  unfold firstProjection
  refine .existsMem _ _ (by apply bound_apart_l; change (1 : Nat) ≠ 2; decide) <|
    .existsMem _ _ (by apply bound_apart_l; change (0 : Nat) ≠ 3; decide) ?_
  exact predicate_kpair0_l _ _ _ _ (by apply bound_apart_l; change (3 : Nat) ≠ 4; decide) (by apply bound_apart_l; change (2 : Nat) ≠ 4; decide) (by apply bound_apart_l; change (0 : Nat) ≠ 4; decide)

theorem of_delta0_predicate_l {p} (φ : Delta0BinarySchema (p+1))
    (useCert : PredicateDelta0 (⟨2,by omega⟩ : Fin (p+3)) φ.body) :
    PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) (S1_binary.of_delta0 φ).matrix.body := useCert.weaken_l

theorem comp_predicate_l {p} (φ ψ : S1_binary (p+1))
    (first : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body)
    (second : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) ψ.matrix.body) :
    PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) (φ.comp ψ).matrix.body := by
  unfold S1_binary.comp
  refine .existsMem _ _ (by apply bound_apart_l; change (0 : Nat) ≠ 3; decide) <|
    .existsMem _ _ (by apply bound_apart_l; change (1 : Nat) ≠ 4; decide) <|
      .existsMem _ _ (by apply bound_apart_l; change (2 : Nat) ≠ 5; decide) <| .conj ?_ ?_
  · refine predicate_matrix_l φ first _ _ ?_ ?_ _ _ _ ?_ ?_ ?_
    · rfl
    · intro i ne eq
      apply ne
      apply Fin.ext
      have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
      change i.val+6 = 6 at vals
      change i.val = 0
      omega
    · apply bound_apart_l; change (5 : Nat) ≠ 6; decide
    · apply bound_apart_l; change (2 : Nat) ≠ 6; decide
    · apply bound_apart_l; change (1 : Nat) ≠ 6; decide
  · refine predicate_matrix_l ψ second _ _ ?_ ?_ _ _ _ ?_ ?_ ?_
    · rfl
    · intro i ne eq
      apply ne
      apply Fin.ext
      have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
      change i.val+6 = 6 at vals
      change i.val = 0
      omega
    · apply bound_apart_l; change (2 : Nat) ≠ 6; decide
    · apply bound_apart_l; change (4 : Nat) ≠ 6; decide
    · apply bound_apart_l; change (0 : Nat) ≠ 6; decide

theorem canonicalPick_predicate_l {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) (canonicalPick_s φ).matrix.body :=
  comp_predicate_l _ _ (leastWitness_predicate_l _ (pairedMatrix_predicate_l φ useCert))
    (of_delta0_predicate_l _ (firstProjection_predicate_l p))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
