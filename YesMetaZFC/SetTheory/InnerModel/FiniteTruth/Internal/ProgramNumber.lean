import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedRows

/-! # 原合法程序与根的规范自然数编号和唯一解码

编号同时记录内部变量数、真实程序图和根行。语法容器只用于合法性检查，
不参与编号，故扩张容器不改变代码。下面尚不声称编号图为局部 Σ₁。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}
variable (I : 𝒞.Interpretation M)

def ProgramNumber_d (ω n L F r e : M.Domain) : Prop :=
  M.mem n ω ∧ M.mem L ω ∧ M.mem r L ∧ M.IsSequenceOfLength I F L ∧
    ∃ G c d, NumberedRows_d I ω L F G ∧ Oc_seq_d I ω G c ∧ Oc_pair_d I n c d ∧ Oc_pair_d I d r e

def programNumber_m {d} (ω n L F r e : Term d) : Formula 1 d :=
  .conj (.mem n ω) <| .conj (.mem L ω) <| .conj (.mem r L) <|
    .conj (Formula.isSequenceOfLength 𝒞 F L) <| .existsE <| .existsE <| .existsE <|
      .conj (numberedRows_m (𝒞 := 𝒞) ω.weaken.weaken.weaken L.weaken.weaken.weaken F.weaken.weaken.weaken (.bound 2)) <|
        .conj (oc_seq_m (𝒞 := 𝒞) ω.weaken.weaken.weaken (.bound 2) (.bound 1)) <|
          .conj (oc_pair_m (𝒞 := 𝒞) n.weaken.weaken.weaken (.bound 1) .newest)
            (oc_pair_m (𝒞 := 𝒞) .newest r.weaken.weaken.weaken e.weaken.weaken.weaken)
derive_free_closed programNumber_m

theorem programNumber_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n L F r e : Term d) :
    Formula.satisfies ρ (programNumber_m (𝒞 := 𝒞) ω n L F r e) ↔
      ProgramNumber_d I (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (r.eval ρ) (e.eval ρ) := by
  simp only [programNumber_m,ProgramNumber_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_isSequenceOfLength_iff I hE,Formula.satisfies_exists_iff,
    numberedRows_sat_l I hE,oc_seq_sat_l I hE,oc_pair_sat_l I hE,Definitional.Term.eval_weaken]
  rfl

theorem ProgramNumber_d.natural_l (hZF : M.Models ZF) {ω n L F r e : M.Domain}
    (hω : M.IsOmega ω) (h : ProgramNumber_d I ω n L F r e) : M.mem e ω := by
  obtain ⟨hn,hL,hr,_,G,c,d,rows,seq,pair,last⟩ := h
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  have hd := oc_pair_natural_l I hZF hω hn hc pair
  exact oc_pair_natural_l I hZF hω hd (hω.transitive hZF L hL r hr) last

theorem ProgramNumber_d.unique_l (hZF : M.Models ZF) {ω n L F r e e' : M.Domain}
    (h : ProgramNumber_d I ω n L F r e) (g : ProgramNumber_d I ω n L F r e') : e = e' := by
  obtain ⟨_,_,_,_,G,c,d,rows,seq,pair,last⟩ := h
  obtain ⟨_,_,_,_,H,c',d',rows',seq',pair',last'⟩ := g
  have eq := rows.unique_l I hZF.1 rows'; subst H
  have eq := oc_seq_unique_l I hZF seq seq'; subst c'
  have eq := oc_pair_unique_l I hZF pair pair'; subst d'
  exact oc_pair_unique_l I hZF last last'

/-- 同一自然数码准确确定变量数、长度、原程序图和根；不重新选择解释程序。 -/
theorem ProgramNumber_d.injective_l (hZF : M.Models ZF) {ω n L F r n' L' F' r' e : M.Domain}
    (hω : M.IsOmega ω) (h : ProgramNumber_d I ω n L F r e)
    (g : ProgramNumber_d I ω n' L' F' r' e) : n = n' ∧ L = L' ∧ F = F' ∧ r = r' := by
  obtain ⟨_,_,_,hf,G,c,d,rows,seq,pair,last⟩ := h
  obtain ⟨_,_,_,hf',H,c',d',rows',seq',pair',last'⟩ := g
  obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF last last'
  obtain ⟨rfl,rfl⟩ := oc_pair_injective_l I hZF pair pair'
  have eq := oc_seq_injective_l I hZF hω seq seq'; subst H
  have len := rows.1.2.1.eq hZF.1 rows'.1.2.1
  exact ⟨rfl,len,rows.source_unique_l I hZF hf hf' rows',rfl⟩

/-- 编译器的任何合法内部程序及其给定根都有唯一的内部自然数编号。 -/
theorem programNumber_exists_l (hZF : M.Models ZF) {T ω n L F r : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F) (hr : M.mem r L) :
    ∃ e, M.mem e ω ∧ ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨G,rows⟩ := numberedRows_exists_l hZF hω valid
  have ordinalRows : M.IsOrdinalValuedSequence I G L :=
    ⟨⟨valid.ordinal,rows.1.1,rows.1.2.1⟩,fun _ _ z hz => hω.members_areOrdinals hZF z (rows.1.output_mem_of_pairMember hz)⟩
  obtain ⟨c,seq⟩ := oc_seq_exists_l I hZF valid.finite ordinalRows
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  obtain ⟨d,pair⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF n valid.variables) (hω.members_areOrdinals hZF c hc)
  have hd := oc_pair_natural_l I hZF hω valid.variables hc pair
  obtain ⟨e,last⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF d hd) (valid.ordinal.mem hr)
  have hf := fn0_function_l (ZF.modelsKP hZF) valid.graph
  exact ⟨e,oc_pair_natural_l I hZF hω hd (hω.transitive hZF L valid.finite r hr) last,
    valid.variables,valid.finite,hr,⟨valid.ordinal,hf.1,hf.2.1⟩,G,c,d,rows,seq,pair,last⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
