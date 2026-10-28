import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PredicateLocalization

/-! # 集合编码的 amenable 谓词在原 J 层内的实际有界分离

只对一个外部固定原公式实例取证；不假设 C 满足 KP 或 Collection。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_member_amenable_l (hZF : M.Models ZF) {α C A : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hAC : M.mem A C) : AmenableSet_d C A := by
  let hKP := ZF.modelsKP hZF
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) hC
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα hC
  refine ⟨fun z hz => trans A hAC z hz,fun X hXC => ?_⟩
  obtain ⟨D,hDC,diff⟩ := rud.exists_l hKP .diff hXC hAC hXC
  obtain ⟨Y,hYC,inter⟩ := rud.exists_l hKP .diff hXC hDC hXC
  refine ⟨Y,hYC,fun z => ?_⟩
  rw [inter z]
  change (M.mem z X ∧ ¬M.mem z D) ↔ _
  rw [diff z]
  change (M.mem z X ∧ ¬(M.mem z X ∧ ¬M.mem z A)) ↔ _
  exact ⟨fun ⟨hx,hn⟩ => ⟨hx,Classical.byContradiction (fun na => hn ⟨hx,na⟩)⟩,
    fun ⟨hx,ha⟩ => ⟨hx,fun bad => bad.2 ha⟩⟩

theorem jh_amenable_delta0_separation_l (hZF : M.Models ZF) {α C A X : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (amenable : AmenableSet_d C A) (hXC : M.mem X C)
    {p} (φ : UnarySchema (p+1)) (useCert : PredicateDelta0 (1 : Fin (p+2)) φ.body)
    (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) C) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.denote (ρ.push A) x := by
  let hKP := ZF.modelsKP hZF
  let hM := ZF.models_kpi_l hZF
  have rud := jh_value_closed_l hM hα hC
  have all : ∀ z, z ∈ X :: List.ofFn ρ.bound → M.mem z C := by
    intro z hz
    rcases List.mem_cons.mp hz with eq | old
    · exact eq ▸ hXC
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp old
      exact hρ i
  obtain ⟨P,hPC,cover⟩ := rd_finiteTruth_cover_l hKP rud hXC (X :: List.ofFn ρ.bound) all
  obtain ⟨U,hUC,trans,hPU⟩ := jh_local_enclosure_l hM hα hC P hPC
  have hXU := trans P hPU X (cover X (List.mem_cons_self ..))
  have params i : M.mem (ρ.bound i) U := trans P hPU (ρ.bound i)
    (cover _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  obtain ⟨B,hBC,trace⟩ := amenable.2 U hUC
  let bounded : Delta0UnarySchema (p+1) := ⟨φ,useCert.delta0_l⟩
  obtain ⟨Y,hYC,sep⟩ := jh_delta0_separation_l hZF hα hC hXC bounded (ρ.push B) (Fin.cases hBC hρ)
  refine ⟨Y,hYC,fun x => ?_⟩
  exact (sep x).trans ⟨fun ⟨hx,good⟩ => ⟨hx,(predicateUnary_localize_l φ useCert ρ trans hXU params trace hx).mpr good⟩,
    fun ⟨hx,good⟩ => ⟨hx,(predicateUnary_localize_l φ useCert ρ trans hXU params trace hx).mp good⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
