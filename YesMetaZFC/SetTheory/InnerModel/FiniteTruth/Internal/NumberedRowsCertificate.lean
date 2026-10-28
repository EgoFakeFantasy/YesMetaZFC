import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.QuadSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedRows

/-! # 原逐行编号的完整有界证书

输入程序和输出自然数列的完整函数图同时核验；每个内部行必须有与该行
两个实际条目对应的原四字段配对证书，不能只检查若干选定行。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def NumberedRowCheck_d (T ω F G r W : M.Domain) : Prop :=
  ∃ c, M.mem c T ∧ ∃ z, M.mem z ω ∧ Rd_entry_d r c F ∧ Rd_entry_d r z G ∧ QuadCheck_d ω c z W

def numberedRowCheck_m {d} (T ω F G r W : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem ω.weaken <|
    .conj (rd_entry0_m r.weaken.weaken (.bound 1) F.weaken.weaken) <|
      .conj (rd_entry0_m r.weaken.weaken .newest G.weaken.weaken)
        (quadCheck_m ω.weaken.weaken (.bound 1) .newest W.weaken.weaken)
derive_free_closed numberedRowCheck_m

theorem numberedRowCheck_delta_l {d} (T ω F G r W : Term d) : (numberedRowCheck_m T ω F G r W).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (quadCheck_delta_l ..))))

theorem numberedRowCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω F G r W : Term d) :
    Formula.satisfies ρ (numberedRowCheck_m T ω F G r W) ↔
      NumberedRowCheck_d (T.eval ρ) (ω.eval ρ) (F.eval ρ) (G.eval ρ) (r.eval ρ) (W.eval ρ) := by
  simp only [numberedRowCheck_m,NumberedRowCheck_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hKP.1,quadCheck_sat_l hKP,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

def numberedRowCheck_s : BinarySchema 4 := {
  body := numberedRowCheck_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
def numberedRowCheck_env_l (T ω F G : M.Domain) : Env M 4 :=
  ⟨Fin.cases G (Fin.cases F (Fin.cases ω (fun _ => T))),fun _ => ω⟩

theorem numberedRowCheck_schema_sat_l (hKP : M.Models KP) (T ω F G r W : M.Domain) :
    numberedRowCheck_s.denote (numberedRowCheck_env_l T ω F G) r W ↔ NumberedRowCheck_d T ω F G r W := by
  simp only [numberedRowCheck_s,BinarySchema.denote,numberedRowCheck_sat_l hKP]
  rfl

def RowsNumberCheck_d (T ω n L F G V : M.Domain) : Prop :=
  BoundedFormula_d T ω n L F ∧ Fn0_d L ω G ∧
    ∀ r, M.mem r L → ∃ W, M.mem W V ∧ NumberedRowCheck_d T ω F G r W

def rowsNumberCheck_m {d} (T ω n L F G V : Term d) : Formula 1 d :=
  .conj (boundedFormula_m T ω n L F) <| .conj (fn0_m L ω G) <|
    Formula.forallMem L <| Formula.existsMem V.weaken <|
      numberedRowCheck_m T.weaken.weaken ω.weaken.weaken F.weaken.weaken G.weaken.weaken (.bound 1) .newest
derive_free_closed rowsNumberCheck_m

theorem rowsNumberCheck_delta_l {d} (T ω n L F G V : Term d) : (rowsNumberCheck_m T ω n L F G V).IsDelta0 :=
  .conj (boundedFormula_delta_l ..) (.conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (numberedRowCheck_delta_l ..))))

theorem rowsNumberCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n L F G V : Term d) :
    Formula.satisfies ρ (rowsNumberCheck_m T ω n L F G V) ↔
      RowsNumberCheck_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (G.eval ρ) (V.eval ρ) := by
  simp only [rowsNumberCheck_m,RowsNumberCheck_d,Formula.satisfies_conj_iff,boundedFormula_sat_l hKP,
    fn0_sat_l hKP.1,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,numberedRowCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem rowsNumberCheck_sound_l (hZF : M.Models ZF) {T ω n L F G V : M.Domain}
    (cert : RowsNumberCheck_d T ω n L F G V) : BoundedFormula_d T ω n L F ∧
      NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ff := fn0_function_l (ZF.modelsKP hZF) cert.1.graph
  have gg := fn0_function_l (ZF.modelsKP hZF) cert.2.1
  refine ⟨cert.1,gg,fun r z => ?_⟩
  constructor
  · intro hrz
    have hr := gg.input_mem_of_pairMember hrz
    obtain ⟨W,_,c,_,y,_,hrc,hry,qcert⟩ := cert.2.2 r hr
    have eq := gg.1.2 r y z hry hrz
    exact ⟨hr,c,hrc,eq ▸ (quadCheck_sound_l hZF qcert).2⟩
  · rintro ⟨hr,c,hrc,code⟩
    obtain ⟨W,_,d,_,y,_,hrd,hry,qcert⟩ := cert.2.2 r hr
    have eq := ff.1.2 r c d hrc hrd
    subst d
    have eqzy := quadNumber_unique_l I hZF code (quadCheck_sound_l hZF qcert).2
    exact eqzy ▸ hry

theorem numberedRowCheck_exists_l (hZF : M.Models ZF) {T ω n L F G r : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (rows : NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G) (hr : M.mem r L) :
    ∃ W, NumberedRowCheck_d T ω F G r W := by
  obtain ⟨z,hz,hrz⟩ := rows.1.2.2 r hr
  obtain ⟨_,c,hrc,code⟩ := (rows.2 r z).mp hrz
  have input := bnode_naturalQuad_l hZF hω valid.variables (hω.transitive hZF L valid.finite r hr) (valid.at_l hrc).2.2
  obtain ⟨W,cert⟩ := quadCheck_exists_l hZF hω input code
  exact ⟨W,c,(valid.graph.bound_l hrc).2,z,hz,hrc,hrz,cert⟩

theorem rowsNumberCheck_exists_l (hZF : M.Models ZF) {T ω n L F G : M.Domain}
    (hω : M.IsOmega ω) (valid : BoundedFormula_d T ω n L F)
    (rows : NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G) :
    ∃ V, RowsNumberCheck_d T ω n L F G V := by
  let ρ := numberedRowCheck_env_l T ω F G
  obtain ⟨V,cover⟩ := ZF.collection_exists_d hZF numberedRowCheck_s ρ L (by
    intro r hr
    obtain ⟨W,cert⟩ := numberedRowCheck_exists_l hZF hω valid rows hr
    exact ⟨W,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mpr cert⟩)
  exact ⟨V,valid,fn0_of_function_l (ZF.modelsKP hZF) rows.1,fun r hr =>
    (cover r hr).imp fun W hW => ⟨hW.1,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mp hW.2⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
