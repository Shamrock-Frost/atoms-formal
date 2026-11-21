import Atoms.Diagrammatic.Joyal.GrayTensor
import Atoms.Diagrammatic.Subdivision.Quillen
import Atoms.Homotopical.Simplicial.KanProduct

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open DiagSet.modelCategoryCisinski in
private theorem kanWeak_sd_map_counit_app {X : DiagSet.{u}} (hX : IsHornFibrant X) :
    kanWeak (DiagSet.sd.map (sSetDiagSetAdj.counit.app X)) :=
  (DiagSet.kanWeak_sd_map_iff _).2
    ((weakEquivalence_iff _).1 (weakEquivalence_sSetDiagSetAdj_counit_app_kan X hX))

private theorem kanWeak_prodComparison_toDiagSet_sd (K L : SSet.{u}) :
    kanWeak (prodComparison (SSet.toDiagSet ⋙ DiagSet.sd) K L) := by
  refine (kanWeak.arrow_mk_iso_iff (Arrow.isoMk (DiagSet.toDiagSetCompSdIso.app (K ⨯ L))
    (prod.mapIso (DiagSet.toDiagSetCompSdIso.app K) (DiagSet.toDiagSetCompSdIso.app L)) ?_)).2
    (kanWeak_prodComparison_sd K L)
  exact (prodComparison_natural_of_natTrans (A := K) (B := L) DiagSet.toDiagSetCompSdIso.hom)

theorem kanWeak_prodComparison_sd_of_isHornFibrant {X Y : DiagSet.{u}} (hX : IsHornFibrant X)
    (hY : IsHornFibrant Y) : kanWeak (prodComparison DiagSet.sd X Y) := by
  let α : DiagSet.toSSet ⋙ SSet.toDiagSet ⋙ DiagSet.sd ⟶ DiagSet.sd.{u} :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight sSetDiagSetAdj.{u}.counit DiagSet.sd ≫
      (Functor.leftUnitor _).hom
  have hα {Z : DiagSet.{u}} (hZ : IsHornFibrant Z) : kanWeak (α.app Z) := by
    simpa [α] using kanWeak_sd_map_counit_app hZ
  have e := prodComparison_natural_of_natTrans (A := X) (B := Y) α
  rw [prodComparison_comp DiagSet.toSSet (SSet.toDiagSet ⋙ DiagSet.sd)] at e
  have := sSetDiagSetAdj.{u}.rightAdjoint_preservesLimits
  have hi : kanWeak ((SSet.toDiagSet ⋙ DiagSet.sd).map (prodComparison DiagSet.toSSet X Y)) :=
    isALocalizer_kanWeak.isomorphisms_le _ (isomorphisms.infer_property _)
  refine kanWeak.of_precomp _ (prodComparison DiagSet.sd X Y)
    (hα (isHornFibrant_prod hX hY)) ?_
  rw [e, Category.assoc]
  exact kanWeak.comp_mem _ _ hi (kanWeak.comp_mem _ _ (kanWeak_prodComparison_toDiagSet_sd _ _)
    (kanWeak_prod_map (hα hX) (hα hY)))

theorem infinityEquivalences_grayTensorToProd (X Y : DiagSet.{u}) (hX : IsHornFibrant X)
    (hY : IsHornFibrant Y) : infinityEquivalences (grayTensorToProd X Y) := by
  have hΦ : faceNerve.map (grayTensorToProd X Y) ≫ prodComparison faceNerve X Y =
      faceNerveGrayTensorIso.hom.app (X, Y) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp, grayTensorToProd, prod.lift_fst]
      exact (faceNerveGrayTensorIso_hom_app_fst X Y).symm
    · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp, grayTensorToProd, prod.lift_snd]
      exact (faceNerveGrayTensorIso_hom_app_snd X Y).symm
  have e : (faceNerve ⋙ MarkedPresheaf.forget).map (grayTensorToProd X Y) ≫
      prodComparison (faceNerve ⋙ MarkedPresheaf.forget) X Y =
      MarkedPresheaf.forget.map (faceNerveGrayTensorIso.hom.app (X, Y)) ≫
        prodComparison MarkedPresheaf.forget (faceNerve.obj X) (faceNerve.obj Y) := by
    rw [prodComparison_comp, Functor.comp_map, ← Functor.map_comp_assoc, hΦ]
    rfl
  have hρ : kanWeak (prodComparison (faceNerve ⋙ MarkedPresheaf.forget) X Y) :=
    kanWeak_prodComparison_sd_of_isHornFibrant hX hY
  have hc : IsIso (prodComparison MarkedPresheaf.forget (faceNerve.obj X) (faceNerve.obj Y)) :=
    inferInstance
  have hi : kanWeak (MarkedPresheaf.forget.map (faceNerveGrayTensorIso.hom.app (X, Y)) ≫
      prodComparison MarkedPresheaf.forget (faceNerve.obj X) (faceNerve.obj Y)) :=
    isALocalizer_kanWeak.isomorphisms_le _ (IsIso.comp_isIso' inferInstance hc)
  exact (DiagSet.kanWeak_sd_map_iff _).1
    (kanWeak.of_postcomp ((faceNerve ⋙ MarkedPresheaf.forget).map (grayTensorToProd X Y)) _ hρ
      (e ▸ hi))

open DiagSet.modelCategoryCisinski in
theorem infinityEquivalences_grayTensorBifunctor_map_comp_grayTensorToProd
    {A A' B B' : DiagSet.{u}} (a : A ⟶ A') (b : B ⟶ B') (ha : infinityEquivalences a)
    (hb : infinityEquivalences b) (hA' : IsHornFibrant A') (hB' : IsHornFibrant B') :
    infinityEquivalences (grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B')) ≫
      grayTensorToProd A' B') := by
  have : WeakEquivalence a := (weakEquivalence_iff a).2 ha
  have : WeakEquivalence b := (weakEquivalence_iff b).2 hb
  have := weakEquivalence_grayTensorBifunctor_map a b
  have : WeakEquivalence (grayTensorToProd A' B') :=
    (weakEquivalence_iff _).2 (infinityEquivalences_grayTensorToProd A' B' hA' hB')
  exact (weakEquivalence_iff (grayTensorBifunctor.map ((a, b) : (A, B) ⟶ (A', B')) ≫
    grayTensorToProd A' B')).1 inferInstance

end Atoms.Diagrammatic
