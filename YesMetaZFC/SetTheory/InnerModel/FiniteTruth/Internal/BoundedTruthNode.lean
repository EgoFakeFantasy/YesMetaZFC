import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.BoundedFormulaCode

/-! # 内部有界程序的统一真值节点

旧真值集由历史图中的实际有序对有界读取，不要求预先属于语法容器。
全部变量编号、子行编号和赋值均为模型中的对象；本层不使用宿主公式递归。
-/

namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Bhit_d (H r f : M.Domain) : Prop := ∃ A, Rd_entry_d r A H ∧ M.mem f A

def bhit_m {d} (H r f : Term d) : Formula 1 d :=
  Formula.existsMem H <| Formula.existsMem .newest <| Formula.existsMem .newest <|
    .conj (kpair0_m (.bound 2) r.weaken.weaken.weaken .newest) (.mem f.weaken.weaken.weaken .newest)
derive_free_closed bhit_m

theorem bhit_delta_l {d} (H r f : Term d) : (bhit_m H r f).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.mem _ _))))

theorem bhit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H r f : Term d) :
    Formula.satisfies ρ (bhit_m H r f) ↔ Bhit_d (H.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [bhit_m, Bhit_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Formula.satisfies_mem_iff,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  constructor
  · rintro ⟨p, hp, t, _, A, _, hpa, hf⟩
    exact ⟨A, ⟨p, hpa, hp⟩, hf⟩
  · rintro ⟨A, ⟨p, hpa, hp⟩, hf⟩
    obtain ⟨t, ht, hAt⟩ := (kpair_union_l M hpa A).mpr (Or.inr rfl)
    exact ⟨p, hp, t, ht, A, hAt, hpa, hf⟩

theorem Bhit_d.value_l {H r A f : M.Domain}
    (funct : ∀ i B C, Rd_entry_d i B H → Rd_entry_d i C H → B = C)
    (hr : Rd_entry_d r A H) : Bhit_d H r f ↔ M.mem f A := by
  constructor
  · rintro ⟨B, hb, hf⟩
    exact funct r B A hb hr ▸ hf
  · exact fun hf => ⟨A, hr, hf⟩

def Bupdate_d (n X f i x g : M.Domain) : Prop :=
  ∀ j, M.mem j n → ∀ y, M.mem y X →
    (Rd_entry_d j y g ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ Rd_entry_d j y f))

theorem bupdate_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n X f i x g : Term d) :
    Formula.satisfies ρ (updateCheck_m n X f i x g) ↔
      Bupdate_d (n.eval ρ) (X.eval ρ) (f.eval ρ) (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [updateCheck_m, Bupdate_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE,
    YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem bupdate_correct_l (hKP : M.Models KP) {n X f i x g : M.Domain}
    (hf : M.IsSetFunctionFromTo (kp_pair_l hKP) f n X)
    (hg : M.IsSetFunctionFromTo (kp_pair_l hKP) g n X) (hi : M.mem i n) (hx : M.mem x X) :
    Bupdate_d n X f i x g ↔ Senv_update_d (kp_pair_l hKP) f i x g :=
  (show Bupdate_d n X f i x g ↔ UpdateCheck_d (kp_pair_l hKP) n X f i x g from Iff.rfl).trans
    (updateCheck_correct_l (kp_pair_l hKP) hf hg hi hx)

def Barg_d (tag : Nat) (n X E H f i j k : M.Domain) : Prop :=
  match tag with
  | 0 => ∃ a, M.mem a X ∧ ∃ b, M.mem b X ∧ Rd_entry_d i a f ∧ Rd_entry_d j b f ∧ M.mem a b
  | 1 => ∃ a, M.mem a X ∧ Rd_entry_d i a f ∧ Rd_entry_d j a f
  | 2 => ¬ (Bhit_d H i f ∨ Bhit_d H j f)
  | _ => ∃ a, M.mem a X ∧ Rd_entry_d j a f ∧ ∃ x, M.mem x X ∧ M.mem x a ∧
      ∃ g, M.mem g E ∧ Bupdate_d n X f i x g ∧ Bhit_d H k g

def barg_m (tag : Nat) {d} (n X E H f i j k : Term d) : Formula 1 d :=
  match tag with
  | 0 => Formula.existsMem X (Formula.existsMem X.weaken
      (.conj (rd_entry0_m i.weaken.weaken (.bound 1) f.weaken.weaken)
        (.conj (rd_entry0_m j.weaken.weaken .newest f.weaken.weaken) (.mem (.bound 1) .newest))))
  | 1 => Formula.existsMem X (.conj (rd_entry0_m i.weaken .newest f.weaken)
      (rd_entry0_m j.weaken .newest f.weaken))
  | 2 => .neg (.disj (bhit_m H i f) (bhit_m H j f))
  | _ => Formula.existsMem X (.conj (rd_entry0_m j.weaken .newest f.weaken)
      (Formula.existsMem X.weaken (.conj (.mem .newest (.bound 1))
        (Formula.existsMem E.weaken.weaken
          (.conj (updateCheck_m n.weaken.weaken.weaken X.weaken.weaken.weaken f.weaken.weaken.weaken
            i.weaken.weaken.weaken (.bound 1) .newest)
            (bhit_m H.weaken.weaken.weaken k.weaken.weaken.weaken .newest))))))

@[simp] theorem barg_closed_l (tag : Nat) {d} (n X E H f i j k : Term d)
    (hn : n.freeSupport = []) (hX : X.freeSupport = []) (hE : E.freeSupport = [])
    (hH : H.freeSupport = []) (hf : f.freeSupport = []) (hi : i.freeSupport = [])
    (hj : j.freeSupport = []) (hk : k.freeSupport = []) : (barg_m tag n X E H f i j k).FreeClosed := by
  rcases tag with _ | (_ | (_ | tag)) <;>
    simp -implicitDefEqProofs [barg_m, YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed, hn, hX, hE, hH, hf, hi, hj, hk]

theorem barg_delta_l (tag : Nat) {d} (n X E H f i j k : Term d) :
    (barg_m tag n X E H f i j k).IsDelta0 := by
  rcases tag with _ | (_ | (_ | tag))
  · exact .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _))))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))
  · exact .neg (.disj (bhit_delta_l ..) (bhit_delta_l ..))
  · exact .existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (.conj (.mem _ _)
      (.existsMem _ (.conj (updateCheck_delta_l ..) (bhit_delta_l ..))))))

theorem barg_sat_l (hE : Extensional M) (tag : Nat) {d} (ρ : Env M d) (n X E H f i j k : Term d) :
    Formula.satisfies ρ (barg_m tag n X E H f i j k) ↔
      Barg_d tag (n.eval ρ) (X.eval ρ) (E.eval ρ) (H.eval ρ) (f.eval ρ) (i.eval ρ) (j.eval ρ) (k.eval ρ) := by
  rcases tag with _ | (_ | (_ | tag)) <;>
    simp only [barg_m, Barg_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE, bhit_sat_l hE, bupdate_sat_l hE,
      YesMetaZFC.SetTheory.Definitional.Term.eval_weaken, YesMetaZFC.SetTheory.Definitional.Term.eval_newest] <;> rfl

def BtruthNode_d (T n X E H c f : M.Domain) : Prop :=
  ∃ tag : Fin 4, ∃ i, M.mem i T ∧ ∃ j, M.mem j T ∧ ∃ k, M.mem k T ∧
    Bop_d T tag.val c i j k ∧ Barg_d tag.val n X E H f i j k

private def btruthCase_m (tag : Nat) {d} (T n X E H c f : Term d) : Formula 1 d :=
  Formula.existsMem T <| Formula.existsMem T.weaken <| Formula.existsMem T.weaken.weaken <|
    .conj (bop_m T.weaken.weaken.weaken tag c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
      (barg_m tag n.weaken.weaken.weaken X.weaken.weaken.weaken E.weaken.weaken.weaken H.weaken.weaken.weaken
        f.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
derive_free_closed btruthCase_m

def btruthNode_m {d} (T n X E H c f : Term d) : Formula 1 d :=
  .disj (btruthCase_m 0 T n X E H c f) (.disj (btruthCase_m 1 T n X E H c f)
    (.disj (btruthCase_m 2 T n X E H c f) (btruthCase_m 3 T n X E H c f)))
derive_free_closed btruthNode_m

theorem btruthNode_delta_l {d} (T n X E H c f : Term d) : (btruthNode_m T n X E H c f).IsDelta0 := by
  have one (tag : Nat) : (btruthCase_m tag T n X E H c f).IsDelta0 :=
    .existsMem _ (.existsMem _ (.existsMem _ (.conj (bop_delta_l ..) (barg_delta_l ..))))
  exact .disj (one 0) (.disj (one 1) (.disj (one 2) (one 3)))

theorem btruthNode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T n X E H c f : Term d) :
    Formula.satisfies ρ (btruthNode_m T n X E H c f) ↔
      BtruthNode_d (T.eval ρ) (n.eval ρ) (X.eval ρ) (E.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [btruthNode_m, BtruthNode_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false,
    btruthCase_m, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    bop_sat_l hE, barg_sat_l hE, YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    YesMetaZFC.SetTheory.Definitional.Term.eval_newest]
  rfl

theorem btruthNode_decode_l (hKP : M.Models KP) {T n X E H c f i j k : M.Domain}
    (tag : Fin 4) (hi : M.mem i T) (hj : M.mem j T) (hk : M.mem k T)
    (hc : Bop_d T tag.val c i j k) : BtruthNode_d T n X E H c f ↔ Barg_d tag.val n X E H f i j k := by
  constructor
  · rintro ⟨other, a, _, b, _, d, _, hd, harg⟩
    obtain ⟨eq, rfl, rfl, rfl⟩ := bop_injective_l hKP hc hd
    have eqTag : tag = other := Fin.ext eq
    subst other
    exact harg
  · exact fun h => ⟨tag, i, hi, j, hj, k, hk, hc, h⟩

/-- 任意内部传递层中，一步求值的完整有界语义准确对应；不要求小层满足 KP。 -/
theorem btruthNode_local_l (hE : Extensional M) {C : M.Domain} (hc : M.TransitiveSet C)
    (hn : Nonempty {x : M.Domain // M.mem x C})
    (T n X E H c f : (rt_model_l C hn).Domain) :
    BtruthNode_d T n X E H c f ↔ BtruthNode_d T.val n.val X.val E.val H.val c.val f.val := by
  let ρ : Env (rt_model_l C hn) 7 :=
    ⟨Fin.cases T (Fin.cases n (Fin.cases X (Fin.cases E (Fin.cases H (Fin.cases c (fun _ => f)))))),
      fun _ => T⟩
  exact (btruthNode_sat_l (rt_model_ext_l hE hc hn) ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)).symm.trans
    ((rt_model_delta_l hc hn (btruthNode_delta_l _ _ _ _ _ _ _) ρ).trans
      (btruthNode_sat_l hE (image_env_l Subtype.val ρ)
        (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6)))

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
