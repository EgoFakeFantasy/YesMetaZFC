import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalSigma1

/-! # 规范选取在原 J 层中的对象定理

固定 Σ₁ 模板在给定传递集合内的解释由有界见证公式表示。参数的层内性
逐个写进对象公式，最终结果回到原 ZF 的推导核。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

def Within_d {n} (φ : S1_binary n) (ρ : Env M n) (x y C : M.Domain) : Prop :=
  ∃ w, M.mem w C ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body

/-- 给定层容器后，原 Σ₁ 关系的层内解释有实际 Δ₀ 表示。 -/
def within_m {n d} (φ : S1_binary n) (e : Fin n → Term d) (x y C : Term d) : Formula 1 d :=
  Formula.existsMem C (φ.matrix_m (fun i => (e i).weaken) x.weaken y.weaken .newest)

@[simp] theorem within_closed_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (x y C : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hx : x.freeSupport = []) (hy : y.freeSupport = [])
    (hC : C.freeSupport = []) : (within_m φ e x y C).FreeClosed := by
  simp -implicitDefEqProofs [within_m, he, hx, hy, hC]

theorem within_delta_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (x y C : Term d) :
    (within_m φ e x y C).IsDelta0 :=
  .existsMem _ (φ.matrix.delta0.bind_l _)

theorem within_sat_l {n d} (φ : S1_binary n) (ρ : Env M d)
    (e : Fin n → Term d) (x y C : Term d) :
    Formula.satisfies ρ (within_m φ e x y C) ↔
      Within_d φ (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M n) (x.eval ρ) (y.eval ρ) (C.eval ρ) := by
  simp only [within_m, Within_d, Formula.satisfies_existsMem_iff, S1_binary.matrix_sat_l,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem within_env_l {n} (φ : S1_binary n) (ρ η : Env M n) (he : ρ.bound = η.bound)
    (x y C : M.Domain) : Within_d φ ρ x y C ↔ Within_d φ η x y C := by
  apply exists_congr
  intro w
  apply and_congr_right
  intro _
  exact Formula.closed_env_l _ φ.matrix.freeClosed
    (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => congrFun he i)))))

/-- 有界见证公式恰好解释给定传递层内的原 Σ₁ 图。 -/
theorem within_local_l {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) {n} (φ : S1_binary n)
    (ρ : Env (rt_model_l C hn) n) (x y : (rt_model_l C hn).Domain) :
    φ.schema.denote ρ x y ↔ Within_d φ (image_env_l Subtype.val ρ) x.val y.val C := by
  rw [S1_binary.sat_l]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.val, w.property, (s1_matrix_local_l hc hn φ ρ x y w).mp hw⟩
  · rintro ⟨w, hwC, hw⟩
    exact ⟨⟨w, hwC⟩, (s1_matrix_local_l hc hn φ ρ x y ⟨w, hwC⟩).mpr hw⟩

/-- 用环境中的实际对象陈述层内规范选取，便于对象公式直接调用。 -/
theorem jh_canonicalPick_bounded_function_l (hM : M.Models KPi) {a C : M.Domain}
    (ha : M.IsOrdinal a) (h : Jh_value_d a C) {n} (φ : S1_binary n) (ρ : Env M n)
    (hp : ∀ i, M.mem (ρ.bound i) C) {x : M.Domain} (hx : M.mem x C)
    (he : ∃ y, M.mem y C ∧ Within_d φ ρ x y C) :
    ∃ z, M.mem z C ∧ Within_d (canonicalPick_s φ) ρ x z C ∧ Within_d φ ρ x z C ∧
      ∀ v, M.mem v C → Within_d (canonicalPick_s φ) ρ x v C → v = z := by
  let hn : Nonempty {x : M.Domain // M.mem x C} := ⟨⟨x, hx⟩⟩
  let ρC : Env (rt_model_l C hn) n := ⟨fun i => ⟨ρ.bound i, hp i⟩, fun _ => ⟨x, hx⟩⟩
  let η := image_env_l Subtype.val ρC
  let xC : (rt_model_l C hn).Domain := ⟨x, hx⟩
  have lift (ψ : S1_binary n) (y : (rt_model_l C hn).Domain) :
      ψ.schema.denote ρC xC y ↔ Within_d ψ ρ x y.val C :=
    (within_local_l (jh_value_transitive_l hM h) hn ψ ρC xC y).trans
      (within_env_l ψ ρ η rfl x y.val C).symm
  obtain ⟨y, hyC, hy⟩ := he
  have hExists : ∃ y, φ.schema.denote ρC xC y := ⟨⟨y, hyC⟩, (lift φ ⟨y, hyC⟩).mpr hy⟩
  obtain ⟨z, hz, hu⟩ := jh_canonicalPick_function_l hM ha h hn φ ρC xC hExists
  refine ⟨z.val, z.property, (lift (canonicalPick_s φ) z).mp hz,
    (lift φ z).mp (jh_canonicalPick_sound_l hM ha h hn φ ρC hz), ?_⟩
  intro v hvC hv
  exact congrArg Subtype.val (hu ⟨v, hvC⟩ ((lift (canonicalPick_s φ) ⟨v, hvC⟩).mpr hv))

private def paramsIn_m {d} : {n : Nat} → (Fin n → Term d) → Term d → Formula 1 d
  | 0, _, _ => .truth
  | _ + 1, e, C => .conj (.mem (e 0) C) (paramsIn_m (fun i => e i.succ) C)

@[simp] private theorem paramsIn_closed_l {n d} (e : Fin n → Term d) (C : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hC : C.freeSupport = []) :
    (paramsIn_m e C).FreeClosed := by
  induction n with
  | zero => simp only [paramsIn_m, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
  | succ n ih =>
    simp only [paramsIn_m, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
    exact ⟨⟨he 0, hC⟩, ih (fun i => e i.succ) (fun i => he i.succ)⟩

private theorem paramsIn_sat_l {n d} (e : Fin n → Term d) (C : Term d) (ρ : Env M d) :
    Formula.satisfies ρ (paramsIn_m e C) ↔ ∀ i, M.mem ((e i).eval ρ) (C.eval ρ) := by
  induction n with
  | zero => simp only [paramsIn_m, Formula.satisfies_truth_iff, Fin.forall_fin_zero]
  | succ n ih =>
    rw [paramsIn_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

private def layerParams (n offset : Nat) : Fin n → Term (n + offset) :=
  fun i => .bound ⟨i.val + offset, by omega⟩

private def localPickBody {n} (φ : S1_binary n) : Formula 1 n :=
  .forallE <| .forallE <| .imp (KP.ord0_m (.bound 1)) <|
    .imp (jh_value_m (.bound 1) .newest) <| Formula.forallMem .newest <|
      .imp (paramsIn_m (layerParams n 3) (.bound 1)) <|
        .imp (Formula.existsMem (.bound 1)
          (within_m φ (layerParams n 4) (.bound 1) .newest (.bound 2))) <|
          Formula.existsMem (.bound 1) <|
            .conj (within_m (canonicalPick_s φ) (layerParams n 4) (.bound 1) .newest (.bound 2)) <|
              .conj (within_m φ (layerParams n 4) (.bound 1) .newest (.bound 2)) <|
                Formula.forallMem (.bound 2) <|
                  .imp (within_m (canonicalPick_s φ) (layerParams n 5) (.bound 2) .newest (.bound 3))
                    (Formula.extensionalEq .newest (.bound 1))

/-- 任意原 J 层中，原 Σ₁ 关系的非空纤维都有唯一规范输出。 -/
def canonicalPickLocal {n} (φ : S1_binary n) : Sentence :=
  Sentence.forallClosure (localPickBody φ)
    (by simp -implicitDefEqProofs [localPickBody,
      YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, layerParams])

theorem canonicalPickLocal_models {n} (φ : S1_binary n)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalPickLocal φ) := by
  intro f
  change Formula.satisfies (⟨Fin.elim0, f⟩ : Env M 0)
    (Formula.forallClosure n (localPickBody φ))
  apply (Formula.satisfies_forallClosure_iff f (localPickBody φ)).mpr
  intro b
  let ρ : Env M n := ⟨b, f⟩
  change Formula.satisfies ρ (localPickBody φ)
  simp only [localPickBody, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF), jh_value_sat_l, paramsIn_sat_l, within_sat_l,
    Formula.satisfies_extensionalEq_iff_eq hZF.1]
  intro a C ha hC x hx hp he
  change ∃ z, M.mem z C ∧ Within_d (canonicalPick_s φ) ρ x z C ∧ Within_d φ ρ x z C ∧
    ∀ v, M.mem v C → Within_d (canonicalPick_s φ) ρ x v C → v = z
  exact jh_canonicalPick_bounded_function_l (ZF.models_kpi_l hZF) ha hC φ ρ hp hx he

/-- 固定模板的整个单层规范选取结论已回到原 ZF 推导核。 -/
theorem canonicalPickLocal_derives {n} (φ : S1_binary n) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPickLocal φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalPickLocal_models φ M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
