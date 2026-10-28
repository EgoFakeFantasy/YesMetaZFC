import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthCertificate
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedTruthLocalStep

/-! # 实际层内谓词参数的真值一步构造

外部 A 的情形随后由实际迹 B=A∩X∈层运输；本模块只处理 B 的层内预算。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

def PtruthRow_d (T A n X E F r H f : M.Domain) : Prop :=
  ∃ c, M.mem c T ∧ Rd_entry_d r c F ∧ PtruthNode_d T A n X E H c f

def ptruthRow_m {d} (T A n X E F r H f : Term d) : Formula 1 d :=
  Formula.existsMem T <| .conj (rd_entry0_m r.weaken .newest F.weaken)
    (ptruthNode_m T.weaken A.weaken n.weaken X.weaken E.weaken H.weaken .newest f.weaken)

@[simp] theorem ptruthRow_closed_l {d} (T A n X E F r H f : Term d)
    (hT : T.freeSupport = []) (hA : A.freeSupport = []) (hn : n.freeSupport = []) (hX : X.freeSupport = [])
    (hE : E.freeSupport = []) (hF : F.freeSupport = []) (hr : r.freeSupport = [])
    (hH : H.freeSupport = []) (hf : f.freeSupport = []) : (ptruthRow_m T A n X E F r H f).FreeClosed := by
  simp -implicitDefEqProofs [ptruthRow_m,Definitional.Formula.FreeClosed,hT,hA,hn,hX,hE,hF,hr,hH,hf]

theorem ptruthRow_delta_l {d} (T A n X E F r H f : Term d) : (ptruthRow_m T A n X E F r H f).IsDelta0 :=
  .existsMem _ (.conj (rd_entry0_delta_l ..) (ptruthNode_delta_l ..))

theorem ptruthRow_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T A n X E F r H f : Term d) :
    Formula.satisfies ρ (ptruthRow_m T A n X E F r H f) ↔
      PtruthRow_d (T.eval ρ) (A.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (F.eval ρ) (r.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [ptruthRow_m,PtruthRow_d,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,ptruthNode_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem ptruthAt_row_l (hKP : M.Models KP) {T A n X E F r H f : M.Domain}
    (bound : ∀ i c, Rd_entry_d i c F → M.mem c T) (domain : Bdomain_d r H) :
    PtruthAt_d T A n X E F H f ↔ PtruthRow_d T A n X E F r H f := by
  constructor
  · rintro ⟨k,c,hk,entry,node⟩
    have eq := (show M.IsDomainOf (kp_pair_l hKP) k H from hk).eq hKP.1 domain
    subst k
    exact ⟨c,bound r c entry,entry,node⟩
  · rintro ⟨c,_,entry,node⟩
    exact ⟨r,c,domain,entry,node⟩

theorem rd_ptruthStep_exists_l (hKP : M.Models KP) {C T A n X E F r H : M.Domain}
    (rud : Rd_closed_d C) (trans : M.TransitiveSet C)
    (cover : ∀ x, M.mem x C → ∃ U, M.mem U C ∧ M.TransitiveSet U ∧ M.mem x U)
    (hTC : M.mem T C) (hAC : M.mem A C) (hnC : M.mem n C) (hXC : M.mem X C) (hEC : M.mem E C)
    (hFC : M.mem F C) (hrC : M.mem r C) (hHC : M.mem H C)
    (bound : ∀ i c, Rd_entry_d i c F → M.mem c T) (domain : Bdomain_d r H) :
    ∃ Y, M.mem Y C ∧ PtruthStep_d T A n X E F H Y := by
  let ρ := ((ptruth_env_l T A n X E F).push r).push H
  let φ : Delta0UnarySchema 8 := {
    body := ptruthRow_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    delta0 := ptruthRow_delta_l .. }
  have params : ∀ i, M.mem (ρ.bound i) C := Fin.cases hHC (Fin.cases hrC (Fin.cases hFC (Fin.cases hEC
    (Fin.cases hXC (Fin.cases hnC (Fin.cases hAC (fun _ => hTC)))))))
  obtain ⟨Y,hYC,sep⟩ := rd_locally_enclosed_separation_l hKP rud trans cover φ ρ params hEC
  have row f : φ.toUnarySchema.denote ρ f ↔ PtruthRow_d T A n X E F r H f := by
    simp only [φ,UnarySchema.denote,ptruthRow_sat_l hKP.1]
    rfl
  exact ⟨Y,hYC,fun f => (sep f).trans (and_congr_right fun _ =>
    (row f).trans (ptruthAt_row_l hKP bound domain).symm)⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
