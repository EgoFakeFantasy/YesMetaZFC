import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.FiniteTruthHistory
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FiniteTruth
import YesMetaZFC.SetTheory.InnerModel.Separation.Bounded

/-! # 原 J 层内给定集合上的实际 Δ₀ 分离

以固定源模板的有限参数列和原同层传递包络提供上游所需共同界。
不是全复杂度 Separation，也未预设目标层 KP。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_delta0_separation_l (hZF : M.Models ZF) {α C X : M.Domain}
    (hα : M.IsOrdinal α) (hC : Jh_value_d α C) (hXC : M.mem X C)
    {n} (φ : Delta0UnarySchema n) (ρ : Env M n) (hρ : ∀ i, M.mem (ρ.bound i) C) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  let hKP := ZF.modelsKP hZF
  let hM := ZF.models_kpi_l hZF
  have closed := jh_value_closed_l hM hα hC
  have all : ∀ x, x ∈ X :: List.ofFn ρ.bound → M.mem x C := by
    intro x hx
    rcases List.mem_cons.mp hx with eq | old
    · exact eq ▸ hXC
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp old
      exact hρ i
  obtain ⟨P,hPC,cover⟩ := rd_finiteTruth_cover_l hKP closed hXC (X :: List.ofFn ρ.bound) all
  obtain ⟨U,hUC,trans,hPU⟩ := jh_local_enclosure_l hM hα hC P hPC
  have hXU := trans P hPU X (cover X (List.mem_cons_self ..))
  have params i : M.mem (ρ.bound i) U := trans P hPU (ρ.bound i)
    (cover _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  exact rd_separation_l hKP closed (jh_value_transitive_l hM hC) hUC trans φ ρ params hXU

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
