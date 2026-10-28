import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.RegisterFrame

/-! # 嵌套 binder 的寄存器布局不变式

纯有限索引映射记录当前源变量的位置；next 以上的槽尚未被该源上下文占用。
新 binder 使用 next 并压到栈顶，原源变量沿 Fin.succ 保持原槽。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

structure RegisterLayout_d {width d : Nat} (next : Nat) (indices : Fin d → Fin width) : Prop where
  below : ∀ i, (indices i).val < next
  injective : Function.Injective indices

def layoutPrefix_l {d width} (room : d ≤ width) (i : Fin d) : Fin width := ⟨i.val,by omega⟩

theorem layoutPrefix_safe_l {d width} (room : d ≤ width) : RegisterLayout_d d (layoutPrefix_l room) := by
  refine ⟨fun i => i.isLt,?_⟩
  intro i j eq
  exact Fin.ext (congrArg (fun x : Fin width => x.val) eq)

def layoutPush_l {width d} (next : Nat) (indices : Fin d → Fin width) (room : next < width) : Fin (d+1) → Fin width :=
  Fin.cases ⟨next,room⟩ indices

theorem RegisterLayout_d.push_l {width d next} {indices : Fin d → Fin width}
    (safe : RegisterLayout_d next indices) (room : next < width) :
    RegisterLayout_d (next+1) (layoutPush_l next indices room) := by
  refine ⟨?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change next < next+1
      omega
    · change (indices i).val < next+1
      have hi := safe.below i
      omega
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        rfl
      · intro h
        have he := congrArg (fun x : Fin width => x.val) h
        change next = (indices j).val at he
        have hj := safe.below j
        omega
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        have he := congrArg (fun x : Fin width => x.val) h
        change (indices i).val = next at he
        have hi := safe.below i
        omega
      · intro h
        exact congrArg Fin.succ (safe.injective h)

def layoutValues_l {width d} (slots : Fin width → M.Domain) (indices : Fin d → Fin width) : Fin d → M.Domain :=
  fun i => slots (indices i)

theorem layoutValues_push_l {width d next} (slots : Fin width → M.Domain) (indices : Fin d → Fin width)
    (room : next < width) :
    layoutValues_l slots (layoutPush_l next indices room) =
      Fin.cases (slots ⟨next,room⟩) (layoutValues_l slots indices) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem RegisterLayout_d.values_injective_l (hKP : M.Models KP) {width d next n}
    {slots : Fin width → M.Domain} {indices : Fin d → Fin width}
    (safe : RegisterLayout_d next indices) (frame : RegisterFrame_d width n slots) :
    Function.Injective (layoutValues_l slots indices) := by
  intro i j eq
  exact safe.injective (frame.injective_l hKP eq)

/-- 当前计数器给出的实际数码与全部活跃源变量不同。 -/
theorem RegisterLayout_d.fresh_l (hKP : M.Models KP) {width d next n}
    {slots : Fin width → M.Domain} {indices : Fin d → Fin width}
    (safe : RegisterLayout_d next indices) (frame : RegisterFrame_d width n slots) (room : next < width) :
    ∀ i, layoutValues_l slots indices i ≠ slots ⟨next,room⟩ := by
  intro i eq
  have he := congrArg (fun x : Fin width => x.val) (frame.injective_l hKP eq)
  change (indices i).val = next at he
  have hi := safe.below i
  omega

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
