import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ColimitCocone
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.CosliceProjection
import Atoms.Homotopical.Simplicial.JoyalOp
import Atoms.Homotopical.Simplicial.SliceFinal

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

open modelCategoryJoyal

theorem isInitialObject_iff_of_trivialFibration {E B : SSet.{u}} [E.Quasicategory]
    [B.Quasicategory] {p : E ⟶ B} (hp : modelCategoryQuillen.I.rlp p) (x : E _⦋0⦌) :
    IsInitialObject (p.app _ x) ↔ IsInitialObject x :=
  have := weakEquivalence_of_rlp_I hp
  isInitialObject_iff_of_weakEquivalence p x

theorem isInitialObject_coslice_iff_trivialFibration_sliceRes {K X : SSet.{u}} [X.Quasicategory]
    (c : join K Δ[0] ⟶ X) :
    IsInitialObject ((cosliceObjEquiv K (Under.mk (joinInclLeft K Δ[0] ≫ c)) 0).symm ⟨c, rfl⟩) ↔
      modelCategoryQuillen.I.rlp (sliceRes (joinInclRight Δ[0] K.op) (Under.mk (coconeOp c))) :=
  (isInitialObject_coslice_iff_isFinal_slice c).trans
    (isFinal_iff_trivialFibration_sliceRes (coconeOp c))

theorem rlp_I_sliceπ_iff_of_iso {B B' Z : SSet.{u}} [Z.Quasicategory] (g : B' ≅ B)
    (e : B ⟶ Z) {f : B' ⟶ Z} (hf : g.hom ≫ e = f) :
    modelCategoryQuillen.I.rlp (sliceπ (Under.mk f)) ↔
      modelCategoryQuillen.I.rlp (sliceπ (Under.mk e)) := by
  subst hf
  have hiso : ∀ {S S' : SSet.{u}} (k : S' ≅ S) (f : S ⟶ Z),
      modelCategoryQuillen.I.rlp (sliceRes k.hom (Under.mk f)) := fun k f ↦
    trivialFibration_sliceRes (llp_of_isIso _ _) f
  have hcongr : ∀ {f f' : B ⟶ Z}, f = f' → modelCategoryQuillen.I.rlp (sliceπ (Under.mk f')) →
      modelCategoryQuillen.I.rlp (sliceπ (Under.mk f)) := by
    rintro f _ rfl h
    exact h
  constructor
  · intro h
    rw [← sliceRes_sliceπ g.hom (Under.mk e)]
    exact comp_mem _ _ _ (hiso g e) h
  · intro h
    rw [← sliceRes_sliceπ g.inv (Under.mk (g.hom ≫ e))]
    exact comp_mem _ _ _ (hiso g.symm (g.hom ≫ e)) (hcongr (g.inv_hom_id_assoc e) h)

theorem isInitialObject_iff_trivialFibration_cosliceπ {X : SSet.{u}} [X.Quasicategory]
    (x : X _⦋0⦌) :
    IsInitialObject x ↔
      modelCategoryQuillen.I.rlp (cosliceπ (Under.mk (yonedaEquiv.symm x))) := by
  refine (isFinal_iff_trivialFibration_sliceAtπ (X := X.op) _).trans ?_
  refine (rlp_I_sliceπ_iff_of_iso (stdSimplex.opIso ⦋0⦌).symm
    (opFunctor.map (yonedaEquiv.symm x)) (yonedaEquiv_symm_opObjEquiv_symm x).symm).trans ?_
  refine Iff.trans ?_ (rlp_I_opFunctor_map_iff (cosliceπ (Under.mk (yonedaEquiv.symm x))))
  rw [← cosliceOpIso_hom_app_comp_sliceπ]
  exact ((modelCategoryQuillen.I.rlp).cancel_left_of_respectsIso
    ((cosliceOpIso Δ[0]).app (Under.mk (yonedaEquiv.symm x))).hom _).symm

theorem modelCategoryJoyal.isInitialObject_coslice_map_iff {K X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (F : X ⟶ Y) [WeakEquivalence F] (d : K ⟶ X)
    (w : ((coslice K).obj (Under.mk d)) _⦋0⦌) :
    IsInitialObject
        (((coslice K).map (Under.homMk F rfl : Under.mk d ⟶ Under.mk (d ≫ F))).app _ w) ↔
      IsInitialObject w := by
  have : WeakEquivalence (opFunctor.map F) := (weakEquivalence_opFunctor_map_iff F).2 ‹_›
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    ((cosliceOpIso K).hom.naturality (Under.homMk F rfl : Under.mk d ⟶ Under.mk (d ≫ F))) _)
    (opObjEquiv.symm w)
  exact (isFinal_iso_hom_app_iff ((cosliceOpIso K).app _) _).symm.trans
    ((congrArg IsFinal h).to_iff.trans
      ((isFinal_slice_map_iff (opFunctor.map F) (opFunctor.map d) _).trans
        (isFinal_iso_hom_app_iff ((cosliceOpIso K).app (Under.mk d)) _)))

end SSet
