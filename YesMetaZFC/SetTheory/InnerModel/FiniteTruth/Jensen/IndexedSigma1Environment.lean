import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedPredicateWitness
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.NicePredicateCompiler

/-! # 固定原 Σ₁ 源到配对有界 body 的真实环境运输 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def sigma1SourceSlot_l (p : Nat) : Fin (p+2) := ⟨1,by omega⟩

def indexedSource_env_l {p} (ρ : Env M (p+1)) (ω : M.Domain) : Env M 2 :=
  ⟨Fin.cases (ρ.bound 0) (fun _ => ω),ρ.free⟩

theorem sigma1Source_predicate_l {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    PredicateDelta0 (sigma1SourceSlot_l p).succ (pairedMatrix φ).body :=
  pairedMatrix_predicate_l φ useCert

theorem indexedSource_env_push_l {p} (ρ : Env M (p+1)) (ω x : M.Domain) :
    predicateSkolem_env_l (sigma1SourceSlot_l p) ω (ρ.push x) = indexedSource_env_l ρ ω := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)),rfl⟩

theorem indexedSource_ordinary_l {p C x} (ρ : Env M (p+1)) (hx : M.mem x C)
    (ordinary : ∀ i : Fin p, M.mem (ρ.bound i.succ) C) :
    ∀ j : Fin (p+2), j ≠ sigma1SourceSlot_l p → M.mem ((ρ.push x).bound j) C := by
  intro j
  refine Fin.cases (fun _ => hx) (fun i hi => ?_) j
  exact Fin.cases (fun h => (h rfl).elim) (fun t _ => ordinary t) i hi

theorem pairedSource_body_sat_l (hE : Extensional M) {p} (φ : S1_binary (p+1))
    (ρ : Env M (p+1)) (x z : M.Domain) :
    Formula.satisfies ((ρ.push x).push z) (pairedMatrix φ).body ↔
      ∃ y w, KPair_d M z y w ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body :=
  pairedMatrix_sat_l hE φ ρ x z

theorem source_within_of_pair_l {C : M.Domain} (trans : M.TransitiveSet C)
    {p} (φ : S1_binary (p+1)) (ρ : Env M (p+1)) {x z y w : M.Domain}
    (hzC : M.mem z C) (pair : KPair_d M z y w)
    (matrix : Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) : Within_d φ ρ x y C :=
  ⟨w,(po_pair_bound_l trans hzC pair).2,matrix⟩

theorem jh_pairedSource_exists_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) {p} (φ : S1_binary (p+1))
    (ρ : Env M (p+1)) (x : M.Domain) {y : M.Domain} (hyC : M.mem y C) (source : Within_d φ ρ x y C) :
    ∃ z, M.mem z C ∧ Formula.satisfies ((ρ.push x).push z) (pairedMatrix φ).body := by
  obtain ⟨w,hwC,matrix⟩ := source
  obtain ⟨z,pair⟩ := (kp_pair_l (ZF.modelsKP hZF)).total y w
  have hzC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .opair y w y hyC hwC hyC z (rd_opair_value_l hZF.1 pair)
  exact ⟨z,hzC,(pairedSource_body_sat_l hZF.1 φ ρ x z).mpr ⟨y,w,pair,matrix⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
