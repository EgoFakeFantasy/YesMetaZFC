import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.NumberedTruthSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.AssignmentRealization

/-! # 带原数码、参数赋值与见证槽的统一见证证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 输入是原三元组 (e,(f,i))；更新实际赋值的给定槽，不改变原程序。 -/
def WitnessFiber_d (I : kpair_convention_l.Interpretation M) (ω input y : M.Domain) : Prop :=
  ∃ T n L F r X e f i g, Rd_triple_d input e f i ∧ M.TransitiveSet X ∧
    BoundedFormula_d T ω n L F ∧ ProgramNumber_d I ω n L F r e ∧ M.mem i n ∧
    M.IsSetFunctionFromTo I f n X ∧ M.mem y X ∧ Senv_update_d I f i y g ∧ FiniteTruth_d true T ω n X F L r g

def WitnessFiberCheck_d (ω input y T n L F r X e f i g P Q : M.Domain) : Prop :=
  Rd_triple_d input e f i ∧ M.mem i n ∧ M.mem y X ∧ Fn0_d n X f ∧ Fn0_d n X g ∧
    (∀ j, M.mem j n → ∀ z, M.mem z X →
      (Rd_entry_d j z g ↔ (j = i ∧ z = y) ∨ (j ≠ i ∧ Rd_entry_d j z f))) ∧
    NumberedTruthCheck_d true ω e g T n L F r X P Q

def witnessFiberCheck_m {k} (ω input y T n L F r X e f i g P Q : Term k) : Formula 1 k :=
  .conj (rd_triple0_m input e f i) <| .conj (.mem i n) <| .conj (.mem y X) <|
    .conj (fn0_m n X f) <| .conj (fn0_m n X g) <| .conj (updateCheck_m n X f i y g)
      (numberedTruthCheck_m true ω e g T n L F r X P Q)
derive_free_closed witnessFiberCheck_m

theorem witnessFiberCheck_delta_l {k} (ω input y T n L F r X e f i g P Q : Term k) :
    (witnessFiberCheck_m ω input y T n L F r X e f i g P Q).IsDelta0 :=
  .conj (rd_triple0_delta_l ..) (.conj (.mem _ _) (.conj (.mem _ _) (.conj (fn0_delta_l ..)
    (.conj (fn0_delta_l ..) (.conj (updateCheck_delta_l ..) (numberedTruthCheck_delta_l ..))))))

theorem witnessFiberCheck_sat_l (hKP : M.Models KP) {k} (ρ : Env M k) (ω input y T n L F r X e f i g P Q : Term k) :
    Formula.satisfies ρ (witnessFiberCheck_m ω input y T n L F r X e f i g P Q) ↔
      WitnessFiberCheck_d (ω.eval ρ) (input.eval ρ) (y.eval ρ) (T.eval ρ) (n.eval ρ) (L.eval ρ) (F.eval ρ)
        (r.eval ρ) (X.eval ρ) (e.eval ρ) (f.eval ρ) (i.eval ρ) (g.eval ρ) (P.eval ρ) (Q.eval ρ) := by
  simp only [witnessFiberCheck_m,WitnessFiberCheck_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    rd_triple0_sat_l hKP.1,fn0_sat_l hKP.1,updateCheck_sat_l hKP,numberedTruthCheck_sat_l hKP]
  rfl

/-- 恢复给定证书的原参数，而不重新选择解码或求值域。 -/
theorem numberedTruthCheck_components_l (hZF : M.Models ZF) {ω e f T n L F r X P Q : M.Domain}
    (hω : M.IsOmega ω) (cert : NumberedTruthCheck_d true ω e f T n L F r X P Q) :
    M.TransitiveSet X ∧ BoundedFormula_d T ω n L F ∧
      ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e ∧ FiniteTruth_d true T ω n X F L r f := by
  obtain ⟨hx,⟨G,_,c,_,d,_,R,_,Q',_,p,_,q,_,pcert⟩,⟨a,_,s,_,Z,_,S,_,E,_,V,_,H,_,tcert⟩⟩ := cert
  obtain ⟨valid,code⟩ := programCheck_sound_l hZF hω pcert
  exact ⟨hx,valid,code,a,s,Z,S,E,V,H,tcert⟩

theorem numberedTruthCheck_for_l (hZF : M.Models ZF) {ω e f T n L F r X : M.Domain}
    (hω : M.IsOmega ω) (hx : M.TransitiveSet X) (valid : BoundedFormula_d T ω n L F)
    (code : ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e)
    (truth : FiniteTruth_d true T ω n X F L r f) : ∃ P Q, NumberedTruthCheck_d true ω e f T n L F r X P Q := by
  obtain ⟨a,s,Z,S,E,V,H,tcert⟩ := truth
  obtain ⟨G,c,d,R,Q',p,q,pcert⟩ := programCheck_exists_l hZF hω valid code
  obtain ⟨P,hP⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [G,c,d,R,Q',p,q]
  obtain ⟨Q,hQ⟩ := finiteTruth_cover_l (ZF.modelsKP hZF) [a,s,Z,S,E,V,H]
  exact ⟨P,Q,hx,⟨G,hP G (by simp),c,hP c (by simp),d,hP d (by simp),R,hP R (by simp),Q',hP Q' (by simp),
    p,hP p (by simp),q,hP q (by simp),pcert⟩,
    ⟨a,hQ a (by simp),s,hQ s (by simp),Z,hQ Z (by simp),S,hQ S (by simp),E,hQ E (by simp),
      V,hQ V (by simp),H,hQ H (by simp),tcert⟩⟩

theorem witnessFiberCheck_sound_l (hZF : M.Models ZF) {ω input y T n L F r X e f i g P Q : M.Domain}
    (hω : M.IsOmega ω) (cert : WitnessFiberCheck_d ω input y T n L F r X e f i g P Q) :
    WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) ω input y := by
  obtain ⟨packet,hi,hy,hf,hg,update,truth⟩ := cert
  obtain ⟨hx,valid,code,answer⟩ := numberedTruthCheck_components_l hZF hω truth
  have ff := fn0_function_l (ZF.modelsKP hZF) hf
  have gg := fn0_function_l (ZF.modelsKP hZF) hg
  have upd := (updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF)) ff gg hi hy).mp update
  exact ⟨T,n,L,F,r,X,e,f,i,g,packet,hx,valid,code,hi,ff,hy,upd,answer⟩

theorem witnessFiberCheck_exists_l (hZF : M.Models ZF) {ω input y : M.Domain}
    (hω : M.IsOmega ω) (fiber : WitnessFiber_d (kp_pair_l (ZF.modelsKP hZF)) ω input y) :
    ∃ T n L F r X e f i g P Q, WitnessFiberCheck_d ω input y T n L F r X e f i g P Q := by
  obtain ⟨T,n,L,F,r,X,e,f,i,g,packet,hx,valid,code,hi,hf,hy,update,answer⟩ := fiber
  have hg := update.function_l (kp_pair_l (ZF.modelsKP hZF)) hf hi hy
  obtain ⟨P,Q,truth⟩ := numberedTruthCheck_for_l hZF hω hx valid code answer
  exact ⟨T,n,L,F,r,X,e,f,i,g,P,Q,packet,hi,hy,fn0_of_function_l (ZF.modelsKP hZF) hf,
    fn0_of_function_l (ZF.modelsKP hZF) hg,(updateCheck_correct_l (kp_pair_l (ZF.modelsKP hZF)) hf hg hi hy).mpr update,truth⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
