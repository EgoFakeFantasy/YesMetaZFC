import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.InstructionNumber

/-! # 全部内部程序行的规范自然数列

用实际对象公式逐行替换；行数保持任意内部自然数，不作外部标准性假设。
编码列唯一且反映原程序图；尚未给出此编号公式的小层有界核验证书。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}
variable (I : 𝒞.Interpretation M)

def NumberedRows_d (ω L F G : M.Domain) : Prop := M.IsSetFunctionFromTo I G L ω ∧
  ∀ i z, M.PairMember I i z G ↔ M.mem i L ∧ ∃ c, M.PairMember I i c F ∧ QuadNumber_d I c z

def numberedRows_m {d} (ω L F G : Term d) : Formula 1 d :=
  .conj (Formula.isFunctionFromTo 𝒞 G L ω) <|
    .forallE <| .forallE <|
      .iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken) <|
        .conj (.mem (.bound 1) L.weaken.weaken) <| .existsE <|
          .conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest F.weaken.weaken.weaken)
            (quadNumber_m (𝒞 := 𝒞) .newest (.bound 1))
derive_free_closed numberedRows_m

theorem numberedRows_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L F G : Term d) :
    Formula.satisfies ρ (numberedRows_m (𝒞 := 𝒞) ω L F G) ↔
      NumberedRows_d I (ω.eval ρ) (L.eval ρ) (F.eval ρ) (G.eval ρ) := by
  simp only [numberedRows_m,NumberedRows_d,Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,
    quadNumber_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

theorem NumberedRows_d.unique_l (hE : Extensional M) {ω L F G H : M.Domain}
    (h : NumberedRows_d I ω L F G) (g : NumberedRows_d I ω L F H) : G = H :=
  h.1.1.1.eq_of_pairMember_iff hE g.1.1.1 (fun i z => (h.2 i z).trans (g.2 i z).symm)

theorem NumberedRows_d.source_unique_l (hZF : M.Models ZF) {ω L K F H G : M.Domain}
    (hf : M.IsSequenceOfLength I F L) (hh : M.IsSequenceOfLength I H K)
    (h : NumberedRows_d I ω L F G) (g : NumberedRows_d I ω K H G) : F = H := by
  have eq := h.1.2.1.eq hZF.1 g.1.2.1; subst K
  have transfer {F H : M.Domain} (hf : M.IsSequenceOfLength I F L)
      (h : NumberedRows_d I ω L F G) (g : NumberedRows_d I ω L H G) {i c}
      (hic : M.PairMember I i c F) : M.PairMember I i c H := by
    have hi := (hf.2.2 i).mpr ⟨c,hic⟩
    obtain ⟨z,_,hz⟩ := h.1.2.2 i hi
    obtain ⟨_,c',hic',hc⟩ := (h.2 i z).mp hz
    have eq := hf.2.1.2 i c c' hic hic'; subst c'
    obtain ⟨_,d,hid,hd⟩ := (g.2 i z).mp hz
    exact (quadNumber_injective_l I hZF hc hd).symm ▸ hid
  exact hf.2.1.1.eq_of_pairMember_iff hZF.1 hh.2.1.1
    (fun _ _ => ⟨transfer hf h g,transfer hh g h⟩)

/-- 原合法程序的每行都可同时编号，得到真实内部有限自然数列。 -/
theorem numberedRows_exists_l (hZF : M.Models ZF) {T ω n L F : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F) :
    ∃ G, NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hf := fn0_function_l (ZF.modelsKP hZF) valid.graph
  have total i (hi : M.mem i L) c (hic : M.PairMember I i c F) :
      ∃ z, M.mem z ω ∧ QuadNumber_d I c z :=
    bnode_number_exists_l hZF hω valid.variables (hω.transitive hZF L valid.finite i hi)
      (valid.at_l hic).2.2
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj
    (Formula.orderedPairMem kpair_convention_l (.bound 2) .newest (.bound 3))
    (quadNumber_m (𝒞 := kpair_convention_l) .newest (.bound 1))) }
  have sat i z : φ.denote ρ i z ↔ ∃ c, M.PairMember I i c F ∧ QuadNumber_d I c z := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I,quadNumber_sat_l I hZF.1]
    rfl
  obtain ⟨G,hg,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := L) (target := ω) (by
    intro i hi
    obtain ⟨c,_,hic⟩ := hf.2.2 i hi
    obtain ⟨z,_,hz⟩ := total i hi c hic
    exact ⟨z,(sat i z).mpr ⟨c,hic,hz⟩⟩) (by
      intro i _ z w hz hw
      obtain ⟨c,hc,hz⟩ := (sat i z).mp hz
      obtain ⟨d,hd,hw⟩ := (sat i w).mp hw
      have eq := hf.1.2 i c d hc hd; subst d
      exact quadNumber_unique_l I hZF hz hw) (by
        intro i z hi hz
        obtain ⟨c,hc,hz⟩ := (sat i z).mp hz
        obtain ⟨w,hw,hc'⟩ := total i hi c hc
        exact (quadNumber_unique_l I hZF hz hc').symm ▸ hw)
  exact ⟨G,hg,fun i z => (he i z).trans (and_congr_right fun _ => sat i z)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
