import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.SeparationFamily
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteFunctionSnoc

/-! # rud 闭包中的有限赋值空间后继

通过固定有界模板的实际参数纤维族，一次生成全部追加图。这里不使用所在层
的幂集或收集公理；定义域及后继都是模型内部的集合。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal

open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel

universe u
variable {M : SetTheory.Structure.{u}}

private def snocMatrix : Delta0UnarySchema 3 where
  body := .disj (.mem .newest (.bound 1)) (kpair0_m .newest (.bound 2) (.bound 3))
  delta0 := .disj (.mem _ _) (kpair0_delta_l ..)

private theorem snocMatrix_sat_l (hE : Extensional M) (ρ : Env M 3) (v : M.Domain) :
    snocMatrix.toUnarySchema.denote ρ v ↔
      M.mem v (ρ.bound 0) ∨ KPair_d M v (ρ.bound 1) (ρ.bound 2) := by
  simp only [snocMatrix, UnarySchema.denote, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, kpair0_sat_l hE]
  rfl

/-- 后继赋值空间是同层的实际集合，而非假设有内部收集所得。 -/
theorem rd_functionSpace_succ_l (hZF : M.Models ZF) {C A E X n s : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C) (hA : M.mem A C) (ha : M.TransitiveSet A)
    (hEA : M.mem E A) (hXA : M.mem X A) (hnA : M.mem n A)
    (hn : M.IsOrdinal n) (hs : M.IsOrdinal s) (hns : M.SuccessorOf s n)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E n X) :
    ∃ Y, M.mem Y C ∧ M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) Y s X := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  obtain ⟨U, hUC, hu, au, pairs⟩ := rd_kpair_bound_l hKP hC hA ha
  have nU := au n hnA
  have fU (f : M.Domain) (hf : M.mem f E) := au f (ha E hEA f hf)
  have xU (x : M.Domain) (hx : M.mem x X) := au x (ha X hXA x hx)
  obtain ⟨N, hNC, hN⟩ := hC.exists_l hKP .pair (hc A hA n hnA) (hc A hA n hnA) (hc A hA n hnA)
  obtain ⟨Q, hQC, hQ⟩ := hC.exists_l hKP .prod hNC (hc A hA X hXA) hNC
  obtain ⟨P, hPC, hP⟩ := hC.exists_l hKP .prod (hc A hA E hEA) hQC hQC
  let params (f : M.Domain) (hf : M.mem f E) (x : M.Domain) (hx : M.mem x X) : Rt_env U 2 :=
    Fin.cases ⟨f, fU f hf⟩ (Fin.cases ⟨n, nU⟩ (fun _ => ⟨x, xU x hx⟩))
  have decode {p : M.Domain} (hpP : M.mem p P) :
      ∃ f x, ∃ hf : M.mem f E, ∃ hx : M.mem x X,
        Rt_tuple_d (fun i => (params f hf x hx i).val) p := by
    obtain ⟨f, q, hfE, hqQ, hp⟩ := (hP p).mp hpP
    obtain ⟨m, x, hmN, hxX, hq⟩ := (hQ q).mp hqQ
    have eq : m = n := ((hN m).mp hmN).elim id id
    subst m
    exact ⟨f, x, hfE, hxX, q, hp, x, hq, rfl⟩
  have valid p (hp : M.mem p P) : ∃ e : Rt_env U 2, Rt_tuple_d (fun i => (e i).val) p := by
    obtain ⟨f, x, hf, hx, he⟩ := decode hp
    exact ⟨params f hf x hx, he⟩
  obtain ⟨Y, hYC, hY⟩ := rd_separation_family_l hKP hC hUC hu ⟨⟨n, nU⟩⟩ hPC valid snocMatrix
  have slice (f : M.Domain) (hf : M.mem f E) (x : M.Domain) (hx : M.mem x X) (Z : M.Domain) :
      (∀ v, M.mem v Z ↔ M.mem v U ∧ snocMatrix.toUnarySchema.denote (familyEnv (params f hf x hx)) v) ↔
        Snoc_d I f n x Z := by
    have pred (v : M.Domain) : snocMatrix.toUnarySchema.denote (familyEnv (params f hf x hx)) v ↔
        M.mem v f ∨ KPair_d M v n x := snocMatrix_sat_l hKP.1 _ v
    have bound (v : M.Domain) (hv : M.mem v f ∨ KPair_d M v n x) : M.mem v U :=
      hv.elim (fun h => au v (ha f (ha E hEA f hf) v h))
        (fun h => pairs n x v hnA (ha X hXA x hx) h)
    constructor
    · intro h v
      exact (h v).trans ((and_congr_right fun _ => pred v).trans
        ⟨And.right, fun h => ⟨bound v h, h⟩⟩)
    · intro h v
      exact (h v).trans ⟨fun hd => ⟨bound v hd, (pred v).mpr hd⟩, fun hd => (pred v).mp hd.2⟩
  refine ⟨Y, hYC, fun Z => ?_⟩
  constructor
  · intro hzY
    obtain ⟨e, ⟨p, hpP, hep⟩, hsep⟩ := (hY Z).mp hzY
    obtain ⟨f, x, hfE, hxX, htuple⟩ := decode hpP
    have eq := rt_env_inj_l hep htuple
    subst e
    exact ((slice f hfE x hxX Z).mp hsep).function_l I hKP hn hs hns ((hE f).mp hfE) hxX
  · intro hz
    obtain ⟨f, x, hf, hx, hsnoc⟩ := function_snoc_exists_l I hZF hns hz
    have hfE := (hE f).mpr hf
    obtain ⟨q, hq⟩ := I.total n x
    obtain ⟨p, hp⟩ := I.total f q
    have hqQ : M.mem q Q := (hQ q).mpr ⟨n, x, (hN n).mpr (Or.inl rfl), hx, hq⟩
    have hpP : M.mem p P := (hP p).mpr ⟨f, q, hfE, hqQ, hp⟩
    exact (hY Z).mpr ⟨params f hfE x hx, ⟨p, hpP, q, hp, x, hq, rfl⟩,
      (slice f hfE x hx Z).mpr hsnoc⟩

/-- 已在同层的函数空间有同层传递容器；只需定义域和值域已有共同界。 -/
theorem rd_functionSpace_enclosed_l (hKP : M.Models KP) {C A E D X : M.Domain}
    (hC : Rd_closed_d C) (hA : M.mem A C) (ha : M.TransitiveSet A) (hE : M.mem E C)
    (hD : M.MemberSubset D A) (hX : M.MemberSubset X A)
    (he : M.IsFunctionSpace (kp_pair_l hKP) E D X) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.mem E T := by
  obtain ⟨U, hUC, hu, _, pairs⟩ := rd_kpair_bound_l hKP hC hA ha
  obtain ⟨B, hBC, hB⟩ := hC.union_l hKP hUC hE
  have old x hx := (hB x).mpr (Or.inl hx)
  have hb : M.TransitiveSet B := by
    intro f hf p hp
    rcases (hB f).mp hf with hfU | hfE
    · exact old p (hu f hfU p hp)
    · have hfn := (he f).mp hfE
      obtain ⟨i, x, hpx⟩ := hfn.1.1 p hp
      exact old p (pairs i x p (hD i (hfn.input_mem_of_pairMember ⟨p, hpx, hp⟩))
        (hX x (hfn.output_mem_of_pairMember ⟨p, hpx, hp⟩)) hpx)
  obtain ⟨T, hTC, ht, _, hET⟩ := rd_bounded_enclosed_l hKP hC hBC hb hE
    (fun f hf => (hB f).mpr (Or.inr hf))
  exact ⟨T, hTC, ht, hET⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
