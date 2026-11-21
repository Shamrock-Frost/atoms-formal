import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ZeroObject
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinOp

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

noncomputable def coconeOp {K X : SSet.{u}} (c : join K Δ[0] ⟶ X) : join Δ[0] K.op ⟶ X.op :=
  joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op) ≫ (joinOpIso K Δ[0]).inv ≫ opFunctor.map c

theorem joinInclRight_comp_coconeOp {K X : SSet.{u}} (c : join K Δ[0] ⟶ X) :
    joinInclRight Δ[0] K.op ≫ coconeOp c = opFunctor.map (joinInclLeft K Δ[0] ≫ c) := by
  have e : joinInclRight (Δ[0] : SSet.{u}).op K.op ≫ (joinOpIso K Δ[0]).inv =
      opFunctor.map (joinInclLeft K Δ[0]) :=
    (Iso.comp_inv_eq _).2 (opFunctor_map_joinInclLeft_comp_joinOpIso_hom K Δ[0]).symm
  rw [coconeOp, joinInclRight_comp_joinMap_assoc, Category.id_comp, reassoc_of% e,
    Functor.map_comp]

private lemma isFinal_sliceObjEquiv_symm_congr {K X : SSet.{u}} {a b : K ⟶ X} (h : a = b)
    (g : join Δ[0] K ⟶ X) (ha : joinInclRight Δ[0] K ≫ g = a)
    (hb : joinInclRight Δ[0] K ≫ g = b) :
    IsFinal ((sliceObjEquiv K (Under.mk a) 0).symm ⟨g, ha⟩) ↔
      IsFinal ((sliceObjEquiv K (Under.mk b) 0).symm ⟨g, hb⟩) := by
  subst h
  rfl

theorem isInitialObject_coslice_iff_isFinal_slice {K X : SSet.{u}} (c : join K Δ[0] ⟶ X) :
    IsInitialObject ((cosliceObjEquiv K (Under.mk (joinInclLeft K Δ[0] ≫ c)) 0).symm ⟨c, rfl⟩) ↔
      IsFinal ((sliceObjEquiv K.op (Under.mk (joinInclRight Δ[0] K.op ≫ coconeOp c)) 0).symm
        ⟨coconeOp c, rfl⟩) := by
  let t := Under.mk (joinInclLeft K Δ[0] ≫ c)
  let v := (cosliceObjEquiv K t 0).symm ⟨c, rfl⟩
  have hv : ((cosliceOpIso K).hom.app t).app _ (opObjEquiv.symm v) =
      (sliceObjEquiv K.op ((Under.post opFunctor).obj t) 0).symm
        ⟨coconeOp c, joinInclRight_comp_coconeOp c⟩ :=
    (Equiv.eq_symm_apply _).2 (Subtype.ext (sliceObjEquiv_cosliceOpIso_hom_app_app_coe t 0 v))
  refine (isFinal_iso_hom_app_iff ((cosliceOpIso K).app t) (opObjEquiv.symm v)).symm.trans ?_
  rw [Iso.app_hom, hv]
  exact isFinal_sliceObjEquiv_symm_congr (joinInclRight_comp_coconeOp c).symm _ _ _

end SSet
