import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateProgramNumberExists
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedRowsCertificate

/-! # 五类程序逐行编号的完整原有界证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PRowsNumberCheck_d (T ω n L F G V : M.Domain) : Prop :=
  PBoundedFormula_d T ω n L F ∧ Fn0_d L ω G ∧
    ∀ r, M.mem r L → ∃ W, M.mem W V ∧ NumberedRowCheck_d T ω F G r W

def prowsNumberCheck_m {d} (T ω n L F G V : Term d) : Formula 1 d :=
  .conj (pboundedFormula_m T ω n L F) <| .conj (fn0_m L ω G) <|
    Formula.forallMem L <| Formula.existsMem V.weaken <|
      numberedRowCheck_m T.weaken.weaken ω.weaken.weaken F.weaken.weaken G.weaken.weaken (.bound 1) .newest
derive_free_closed prowsNumberCheck_m

theorem prowsNumberCheck_delta_l {d} (T ω n L F G V : Term d) : (prowsNumberCheck_m T ω n L F G V).IsDelta0 :=
  .conj (pboundedFormula_delta_l ..) (.conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (numberedRowCheck_delta_l ..))))

theorem prowsNumberCheck_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (T ω n L F G V : Term d) :
    Formula.satisfies ρ (prowsNumberCheck_m T ω n L F G V) ↔
      PRowsNumberCheck_d (T.eval ρ) (ω.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ) (G.eval ρ) (V.eval ρ) := by
  simp only [prowsNumberCheck_m,PRowsNumberCheck_d,Formula.satisfies_conj_iff,pboundedFormula_sat_l hKP,
    fn0_sat_l hKP.1,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,numberedRowCheck_sat_l hKP,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem prowsNumberCheck_sound_l (hZF : M.Models ZF) {T ω n L F G V : M.Domain}
    (cert : PRowsNumberCheck_d T ω n L F G V) : PBoundedFormula_d T ω n L F ∧
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

theorem pnumberedRowCheck_exists_l (hZF : M.Models ZF) {T ω n L F G r : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (rows : NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G) (hr : M.mem r L) :
    ∃ W, NumberedRowCheck_d T ω F G r W := by
  obtain ⟨z,hz,hrz⟩ := rows.1.2.2 r hr
  obtain ⟨_,c,hrc,code⟩ := (rows.2 r z).mp hrz
  have input := pnode_naturalQuad_l hZF hω valid.variables (hω.transitive hZF L valid.finite r hr) (valid.at_l hrc).2.2
  obtain ⟨W,cert⟩ := quadCheck_exists_l hZF hω input code
  exact ⟨W,c,(valid.graph.bound_l hrc).2,z,hz,hrc,hrz,cert⟩

theorem prowsNumberCheck_exists_l (hZF : M.Models ZF) {T ω n L F G : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F)
    (rows : NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G) :
    ∃ V, PRowsNumberCheck_d T ω n L F G V := by
  let ρ := numberedRowCheck_env_l T ω F G
  obtain ⟨V,cover⟩ := ZF.collection_exists_d hZF numberedRowCheck_s ρ L (by
    intro r hr
    obtain ⟨W,cert⟩ := pnumberedRowCheck_exists_l hZF hω valid rows hr
    exact ⟨W,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mpr cert⟩)
  exact ⟨V,valid,fn0_of_function_l (ZF.modelsKP hZF) rows.1,fun r hr =>
    (cover r hr).imp fun W hW => ⟨hW.1,(numberedRowCheck_schema_sat_l (ZF.modelsKP hZF) T ω F G r W).mp hW.2⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
