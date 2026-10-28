import YesMetaZFC.SetTheory.InnerModel.Rudimentary.SetImage

/-! # 同层的有界分离集合族

固定 Δ₀ 模板的所有参数纤维通过实际真值表和 F₈ 一次收集。参数族是模型内部
的集合；构造不要求所在 rud 闭包满足 Collection 或 Power Set。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

/-- 参数元组在背景中的环境；自由变量不参与固定的闭合模板。 -/
def familyEnv {U : M.Domain} {n} (e : Rt_env U n) : Env M (n + 1) :=
  ⟨fun i => (e i).val, fun _ => U⟩

/-- 对原参数族中的全部元组，实际构造其分离集组成的同层集合。 -/
theorem rd_separation_family_l (hKP : M.Models KP) {C U P : M.Domain}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) (hP : M.mem P C) {n}
    (valid : ∀ p, M.mem p P → ∃ e : Rt_env U n, Rt_tuple_d (fun i => (e i).val) p)
    (φ : Delta0UnarySchema (n + 1)) :
    ∃ Y, M.mem Y C ∧ ∀ Z, M.mem Z Y ↔
      ∃ e : Rt_env U n, (∃ p, M.mem p P ∧ Rt_tuple_d (fun i => (e i).val) p) ∧
        ∀ x, M.mem x Z ↔ M.mem x U ∧ φ.toUnarySchema.denote (familyEnv e) x := by
  obtain ⟨R, hRC, hR⟩ := rt_delta_l hKP hC hU hu hn φ.body φ.freeClosed φ.delta0 id
  obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .fibers hRC hP hRC
  have fiber (e : Rt_env U n) {p Z : M.Domain} (hp : Rt_tuple_d (fun i => (e i).val) p) :
      Rd_fiber_d R p Z ↔ ∀ x, M.mem x Z ↔
        M.mem x U ∧ φ.toUnarySchema.denote (familyEnv e) x := by
    apply (hR.fiber_l hKP e hp).trans
    apply forall_congr'
    intro x
    apply iff_congr Iff.rfl
    have env (hx : M.mem x U) :
        Formula.satisfies
          (⟨fun i => (Fin.cases (motive := fun _ : Fin (n + 2) => {z : M.Domain // M.mem z U}) ⟨x, hx⟩ e i).val, fun _ => x⟩ : Env M (n + 2)) φ.body ↔
            φ.toUnarySchema.denote (familyEnv e) x :=
      Formula.closed_env_l _ φ.freeClosed (funext (Fin.cases rfl (fun _ => rfl)))
    exact ⟨fun ⟨hx, hφ⟩ => ⟨hx, (env hx).mp hφ⟩,
      fun ⟨hx, hφ⟩ => ⟨hx, (env hx).mpr hφ⟩⟩
  refine ⟨Y, hYC, fun Z => (hY Z).trans ?_⟩
  constructor
  · rintro ⟨p, hp, hz⟩
    obtain ⟨e, he⟩ := valid p hp
    exact ⟨e, ⟨p, hp, he⟩, (fiber e he).mp hz⟩
  · rintro ⟨e, ⟨p, hp, he⟩, hz⟩
    exact ⟨p, hp, (fiber e he).mpr hz⟩

/-- 全参数立方体给出的分离集合族也有同层传递界。 -/
theorem rd_separation_family_bound_l (hKP : M.Models KP) {C U : M.Domain}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    (hn : Nonempty {x : M.Domain // M.mem x U}) {n} (φ : Delta0UnarySchema (n + 1)) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset U T ∧
      ∀ e : Rt_env U n, ∃ Z, M.mem Z T ∧
        ∀ x, M.mem x Z ↔ M.mem x U ∧ φ.toUnarySchema.denote (familyEnv e) x := by
  obtain ⟨P, hPC, hP⟩ := rt_power_l hKP hC hU n
  obtain ⟨Y, hYC, hY⟩ := rd_separation_family_l hKP hC hU hu hn hPC
    (fun p hp => ((hP p).mp hp).imp (fun _ h => h.1)) φ
  obtain ⟨T, hTC, hT⟩ := hC.union_l hKP hU hYC
  have old x hx := (hT x).mpr (Or.inl hx)
  refine ⟨T, hTC, ?_, old, ?_⟩
  · intro Z hZT x hxZ
    rcases (hT Z).mp hZT with hZU | hZY
    · exact old x (hu Z hZU x hxZ)
    · obtain ⟨_, _, hz⟩ := (hY Z).mp hZY
      exact old x ((hz x).mp hxZ).1
  · intro e
    obtain ⟨p, hp⟩ := rt_tuple_exists_l hKP (fun i => (e i).val)
    have exists_slice : ∃ Z, ∀ x, M.mem x Z ↔
        M.mem x U ∧ φ.toUnarySchema.denote (familyEnv e) x := by
      obtain ⟨Z, hz⟩ := KP.separation_exists_d hKP φ (familyEnv e) U
      exact ⟨Z, hz⟩
    obtain ⟨Z, hz⟩ := exists_slice
    exact ⟨Z, (hT Z).mpr (Or.inr ((hY Z).mpr ⟨e, ⟨p, (hP p).mpr ⟨e, hp, trivial⟩, hp⟩, hz⟩)), hz⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
