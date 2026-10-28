import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PredicateTruthPrefix

/-! # 谓词程序中原四类指令的准确解码 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem ptruthNode_oldOpcode_l (hKP : M.Models KP) {T A n X E H c i j k f : M.Domain} {tag : Nat}
    (small : tag < 4) (code : Bop_d T tag c i j k) :
    PtruthNode_d T A n X E H c f ↔ BtruthNode_d T n X E H c f := by
  have noQuery : ¬ PredicateQuery_d T A X c f := by
    rintro ⟨a,_,b,_,d,_,other,_⟩
    have eq := (bop_injective_l hKP code other).1
    omega
  exact ⟨fun hit => hit.elim id (fun query => (noQuery query).elim),Or.inl⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
