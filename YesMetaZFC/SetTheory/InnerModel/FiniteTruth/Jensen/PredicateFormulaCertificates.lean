import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateSubstitution

/-! # 原配对与原谓词实例化的专用出现证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project

theorem predicate_newest_apart_l {d} (a : Fin d) : (Term.newest : Term (d+1)) ≠ .bound a.succ := by
  intro eq
  have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
  change (0 : Nat) = a.val+1 at vals
  omega

theorem predicate_extensionalEq_l {d} (a : Fin d) (x y : Term d)
    (hx : x ≠ .bound a) (hy : y ≠ .bound a) : PredicateDelta0 a (Formula.extensionalEq x y) := by
  apply PredicateDelta0.atom
  intro i
  exact Fin.cases hx (fun j => Fin.cases hy (fun z => Fin.elim0 z) j) i

theorem predicate_pair0_l {d} (a : Fin d) (p x y : Term d)
    (hp : p ≠ .bound a) (hx : x ≠ .bound a) (hy : y ≠ .bound a) : PredicateDelta0 a (pair0_m p x y) := by
  unfold pair0_m
  exact .conj (.mem _ _ _ hx hp) <| .conj (.mem _ _ _ hy hp) <|
    .forallMem a p hp <| .disj
      (predicate_extensionalEq_l a.succ .newest x.weaken (predicate_newest_apart_l a) (predicate_weaken_apart_l hx))
      (predicate_extensionalEq_l a.succ .newest y.weaken (predicate_newest_apart_l a) (predicate_weaken_apart_l hy))

theorem predicate_kpair0_l {d} (a : Fin d) (p x y : Term d)
    (hp : p ≠ .bound a) (hx : x ≠ .bound a) (hy : y ≠ .bound a) : PredicateDelta0 a (kpair0_m p x y) := by
  have old : (Term.bound 1 : Term (d+2)) ≠ .bound a.succ.succ := by
    intro eq
    have vals := congrArg Fin.val (Definitional.Term.bound.inj eq)
    change (1 : Nat) = a.val+2 at vals
    omega
  have newest := predicate_newest_apart_l a.succ
  have px := predicate_weaken_apart_l (predicate_weaken_apart_l hx)
  have py := predicate_weaken_apart_l (predicate_weaken_apart_l hy)
  have pp := predicate_weaken_apart_l (predicate_weaken_apart_l hp)
  unfold kpair0_m
  exact .existsMem a p hp <| .existsMem a.succ p.weaken (predicate_weaken_apart_l hp) <|
    .conj (predicate_pair0_l a.succ.succ (.bound 1) x.weaken.weaken x.weaken.weaken old px px) <|
      .conj (predicate_pair0_l a.succ.succ .newest x.weaken.weaken y.weaken.weaken newest px py)
        (predicate_pair0_l a.succ.succ p.weaken.weaken (.bound 1) .newest pp old newest)

theorem predicate_binary_pred_l {p d} (φ : BinarySchema (p+1))
    (useCert : PredicateDelta0 (2 : Fin (p+3)) φ.body) (a : Fin d)
    (e : Fin (p+1) → Term d) (protectedSlot : e 0 = .bound a)
    (ordinary : ∀ i, i ≠ 0 → e i ≠ .bound a) (x y : Term d)
    (hx : x ≠ .bound a) (hy : y ≠ .bound a) : PredicateDelta0 a (binary_pred_m φ e x y) := by
  unfold binary_pred_m pred_m
  apply useCert.bind_l _ protectedSlot
  intro i
  exact Fin.cases (fun _ => hy) (fun j => Fin.cases (fun _ => hx)
    (fun k ne => ordinary k (fun eq => ne (congrArg (fun z : Fin (p+1) => z.succ.succ) eq))) j) i

theorem predicate_matrix_l {p d} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (3 : Fin (p+4)) φ.matrix.body) (a : Fin d)
    (e : Fin (p+1) → Term d) (protectedSlot : e 0 = .bound a)
    (ordinary : ∀ i, i ≠ 0 → e i ≠ .bound a) (x y w : Term d)
    (hx : x ≠ .bound a) (hy : y ≠ .bound a) (hw : w ≠ .bound a) : PredicateDelta0 a (φ.matrix_m e x y w) := by
  unfold S1_binary.matrix_m binary_pred_m pred_m
  apply useCert.bind_l _ protectedSlot
  intro i
  exact Fin.cases (fun _ => hw) (fun j => Fin.cases (fun _ => hy)
    (fun k => Fin.cases (fun _ => hx) (fun z ne => ordinary z
      (fun eq => ne (congrArg (fun v : Fin (p+1) => v.succ.succ.succ) eq))) k) j) i

theorem ordinary_matrix_predicate_l {p d} (φ : S1_binary p) (a : Fin d)
    (e : Fin p → Term d) (ordinary : ∀ i, e i ≠ .bound a) (x y w : Term d)
    (hx : x ≠ .bound a) (hy : y ≠ .bound a) (hw : w ≠ .bound a) : PredicateDelta0 a (φ.matrix_m e x y w) := by
  unfold S1_binary.matrix_m binary_pred_m pred_m
  apply delta0_predicate_bind_l φ.matrix.delta0 a
  intro i
  exact Fin.cases hw (fun j => Fin.cases hy (fun k => Fin.cases hx ordinary k) j) i

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
