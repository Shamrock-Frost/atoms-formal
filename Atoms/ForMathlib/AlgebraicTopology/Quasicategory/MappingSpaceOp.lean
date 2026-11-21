import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe u

namespace SSet

instance monoidalClosedFunctor_opFunctor : MonoidalClosedFunctor opFunctor.{u} :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts opFunctor.{u}
    opEquivalence.{u}.toAdjunction

noncomputable def ihomOpIso (K X : SSet.{u}) : ((ihom K).obj X).op ≅ (ihom K.op).obj X.op :=
  asIso ((expComparison opFunctor.{u} K).natTrans.app X)

lemma ihomOpIso_hom_evalVertex {K X : SSet.{u}} (a : K _⦋0⦌) :
    (ihomOpIso K X).hom ≫ evalVertex (opObjEquiv.symm a) X.op =
      opFunctor.map (evalVertex a X) := by
  rw [comp_evalVertex, ihomOpIso, asIso_hom, uncurry_expComparison, evalVertex,
    Functor.map_comp, ← Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq]
  ext1
  · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, lift_fst,
      ← Functor.map_comp, lift_fst, Functor.map_comp, yonedaEquiv_symm_opObjEquiv_symm,
      ← Category.assoc]
    exact congrArg (· ≫ opFunctor.map (yonedaEquiv.symm a))
      ((cancel_mono (stdSimplex.opIso ⦋0⦌).hom).1 (stdSimplex.isTerminalObj₀.hom_ext _ _))
  · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, lift_snd,
      ← Functor.map_comp, lift_snd, CategoryTheory.Functor.map_id]

lemma stdSimplex.opIso_inv_app_obj₀Equiv_symm {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.opIso.{u} ⦋n⦌).inv.app _ (stdSimplex.obj₀Equiv.symm i) =
      opObjEquiv.symm (stdSimplex.obj₀Equiv.symm i.rev) := by
  apply opObjEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact stdSimplex.ext _ _ fun j ↦ rfl

noncomputable def ihomStdSimplexOneOpIso (X : SSet.{u}) :
    ((ihom Δ[1]).obj X).op ≅ (ihom Δ[1]).obj X.op :=
  ihomOpIso Δ[1] X ≪≫
    { hom := (pre (stdSimplex.opIso ⦋1⦌).inv).app X.op
      inv := (pre (stdSimplex.opIso ⦋1⦌).hom).app X.op
      hom_inv_id := by rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]; rfl
      inv_hom_id := by rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]; rfl }

lemma ihomStdSimplexOneOpIso_hom_evalVertex (X : SSet.{u}) (i : Fin 2) :
    (ihomStdSimplexOneOpIso X).hom ≫ evalVertex (stdSimplex.obj₀Equiv.symm i) X.op =
      opFunctor.map (evalVertex (stdSimplex.obj₀Equiv.symm i.rev) X) := by
  rw [ihomStdSimplexOneOpIso, Iso.trans_hom, Category.assoc, pre_app_comp_evalVertex,
    stdSimplex.opIso_inv_app_obj₀Equiv_symm, ihomOpIso_hom_evalVertex]

private noncomputable def opTensorSwapIso (X : SSet.{u}) : (X ⊗ X).op ≅ X.op ⊗ X.op :=
  prodComparisonIso opFunctor.{u} X X ≪≫ β_ X.op X.op

private lemma opTensorSwapIso_hom_fst (X : SSet.{u}) :
    (opTensorSwapIso X).hom ≫ fst X.op X.op = opFunctor.map (snd X X) := by
  rw [opTensorSwapIso, Iso.trans_hom, Category.assoc, CartesianMonoidalCategory.braiding_hom_fst,
    prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd]

private lemma opTensorSwapIso_hom_snd (X : SSet.{u}) :
    (opTensorSwapIso X).hom ≫ snd X.op X.op = opFunctor.map (fst X X) := by
  rw [opTensorSwapIso, Iso.trans_hom, Category.assoc, CartesianMonoidalCategory.braiding_hom_snd,
    prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst]

theorem isPullback_op_mappingSpace (X : SSet.{u}) (x y : X _⦋0⦌) :
    IsPullback
      (opFunctor.map (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫ (ihomStdSimplexOneOpIso X).hom)
      (opFunctor.map (pullback.snd _ _ : mappingSpace X x y ⟶ _) ≫ (stdSimplex.opIso ⦋0⦌).hom)
      (ihomStdSimplexOneEval X.op)
      (lift (yonedaEquiv.symm (opObjEquiv.symm y)) (yonedaEquiv.symm (opObjEquiv.symm x))) := by
  refine (isPullback_op_pullback (ihomStdSimplexOneEval X)
    (lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)) (stdSimplex.opIso ⦋0⦌) _ rfl).of_iso
    (Iso.refl _) (ihomStdSimplexOneOpIso X) (Iso.refl _) (opTensorSwapIso X)
    (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm) ?_ ?_
  · ext1
    · rw [Category.assoc, opTensorSwapIso_hom_fst, ← Functor.map_comp, Category.assoc]
      simp only [ihomStdSimplexOneEval, lift_fst, lift_snd]
      exact (ihomStdSimplexOneOpIso_hom_evalVertex X 0).symm
    · rw [Category.assoc, opTensorSwapIso_hom_snd, ← Functor.map_comp, Category.assoc]
      simp only [ihomStdSimplexOneEval, lift_fst, lift_snd]
      exact (ihomStdSimplexOneOpIso_hom_evalVertex X 1).symm
  · rw [Iso.refl_hom, Category.id_comp]
    ext1
    · rw [Category.assoc, Category.assoc, opTensorSwapIso_hom_fst, ← Functor.map_comp, lift_snd,
        lift_fst, yonedaEquiv_symm_opObjEquiv_symm]
    · rw [Category.assoc, Category.assoc, opTensorSwapIso_hom_snd, ← Functor.map_comp, lift_fst,
        lift_snd, yonedaEquiv_symm_opObjEquiv_symm]

noncomputable def mappingSpaceOpIso (X : SSet.{u}) (x y : X _⦋0⦌) :
    (mappingSpace X x y).op ≅ mappingSpace X.op (opObjEquiv.symm y) (opObjEquiv.symm x) :=
  (isPullback_op_mappingSpace X x y).isoPullback

end SSet
