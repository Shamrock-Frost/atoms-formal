import Atoms.Diagrammatic.HomotopyCategoryInvariance
import Atoms.Diagrammatic.MappingFrameComparison
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.QuillenEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem DiagSet.mappingSpaceMap_comp_mappingSpaceIsoRelativeMappingSpace_hom (F : X ⟶ Y)
    (x y : X.Vertex) :
    X.mappingSpaceMap F x y ≫
        (DiagSet.mappingSpaceIsoRelativeMappingSpace (x.map F) (y.map F)).hom =
      (DiagSet.mappingSpaceIsoRelativeMappingSpace x y).hom ≫
        (relativeMappingSpaceFunctor intervalBoundaryι).map (DiagSet.bipointMap F x y) := by
  refine (relativeMappingSpaceHomEquiv _ _ _).injective (Subtype.ext ?_)
  have h₁ := DiagSet.relativeMappingSpaceHomEquiv_mappingSpaceIsoRelativeMappingSpace
    (x.map F) (y.map F) (X.mappingSpaceMap F x y)
  have h₂ := DiagSet.mappingSpaceHomEquiv_mappingSpaceMap F x y (𝟙 _)
  have h₃ := relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfEq intervalBoundaryι
    (DiagSet.bipointMap F x y).right (Under.w (DiagSet.bipointMap F x y))
    (DiagSet.mappingSpaceIsoRelativeMappingSpace x y).hom
  have h₄ := DiagSet.relativeMappingSpaceHomEquiv_mappingSpaceIsoRelativeMappingSpace x y (𝟙 _)
  rw [Category.id_comp] at h₂ h₄
  exact h₁.trans (h₂.trans ((congrArg (· ≫ F) h₄).symm.trans h₃.symm))

section Kan

open SSet.modelCategoryQuillen

private theorem weakEquivalence_toSSet_map_iff_of_isFibrant {G H : DiagSet.{u}}
    (hG : IsFibrant ((DiagSet.toInfty 0).obj G)) (hH : IsFibrant ((DiagSet.toInfty 0).obj H))
    (g : G ⟶ H) :
    WeakEquivalence (DiagSet.toSSet.map g) ↔ WeakEquivalence ((DiagSet.toInfty 0).map g) := by
  have (K : SSet.{u}) : IsCofibrant K := cofibration_of_mono _
  exact isQuillenEquivalence_sSetDiagSetAdjZero.{u}.weakEquivalence_map_iff
    ((DiagSet.toInfty 0).map g)

private theorem isFullyFaithful_iff_kanWeak (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) :
    DiagSet.IsFullyFaithful F ↔
      ∀ x y : X.Vertex, kanWeak (DiagSet.toSSet.map (X.mappingSpaceMap F x y)) := by
  refine forall₂_congr fun x y => ?_
  let B : Under ((DiagSet.toInfty 1).obj pointPair.{u}) := X.bipoint x y
  let B' : Under ((DiagSet.toInfty 1).obj pointPair.{u}) := Y.bipoint (x.map F) (y.map F)
  have hB : IsFibrant B := (isFibrant_under_iff _ B).2 ((isFibrant_infty_iff 1 X).2 hX)
  have hB' : IsFibrant B' := (isFibrant_under_iff _ B').2 ((isFibrant_infty_iff 1 Y).2 hY)
  let φ : B ⟶ B' := DiagSet.bipointMap F x y
  have e₁ := weakEquivalence_toSSet_map_iff_of_isFibrant
    (isFibrant_bipointedHom (p := X.bipoint x y) hX)
    (isFibrant_bipointedHom (p := Y.bipoint (x.map F) (y.map F)) hY)
    (bipointedHom.map (DiagSet.bipointMap F x y))
  have e₂ := weakEquivalence_bipointedHom_map_iff_relativeMappingSpace_map (hP := hB)
    (hP' := hB') φ
  let i := DiagSet.toSSet.mapIso (DiagSet.mappingSpaceIsoRelativeMappingSpace x y)
  let i' := DiagSet.toSSet.mapIso
    (DiagSet.mappingSpaceIsoRelativeMappingSpace (x.map F) (y.map F))
  have sq : DiagSet.toSSet.map (X.mappingSpaceMap F x y) ≫ i'.hom =
      i.hom ≫ DiagSet.toSSet.map ((relativeMappingSpaceFunctor intervalBoundaryι).map φ) :=
    (DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map
        (DiagSet.mappingSpaceMap_comp_mappingSpaceIsoRelativeMappingSpace_hom F x y)).trans
        (DiagSet.toSSet.map_comp _ _))
  have hi : WeakEquivalence i.hom := inferInstance
  have hi' : WeakEquivalence i'.hom := inferInstance
  have e₃ := (weakEquivalence_postcomp_iff (DiagSet.toSSet.map (X.mappingSpaceMap F x y))
    i'.hom).symm.trans ((iff_of_eq (congrArg (WeakEquivalence ·) sq)).trans
      (weakEquivalence_precomp_iff i.hom _))
  exact e₁.symm.trans (e₂.trans (e₃.symm.trans (weakEquivalence_iff _)))

end Kan

section Joyal

open SSet.modelCategoryJoyal

theorem DiagSet.isFullyFaithful_iff_toSSet (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) :
    DiagSet.IsFullyFaithful F ↔ SSet.IsFullyFaithful (DiagSet.toSSet.map F) := by
  refine (isFullyFaithful_iff_kanWeak hX hY F).trans ?_
  refine Iff.trans (forall_congr' fun x => forall_congr' fun y => ?_)
    ((X.vertexEquivSSet.forall_congr_right (q := fun a => ∀ b, WeakEquivalence
      (SSet.mappingSpaceMap (DiagSet.toSSet.map F) a b))).trans
      (forall_congr' fun a => X.vertexEquivSSet.forall_congr_right
        (q := fun b => WeakEquivalence (SSet.mappingSpaceMap (DiagSet.toSSet.map F) a b))))
  have := kanComplex_toSSet_mappingSpace hX x y
  have := kanComplex_toSSet_mappingSpace hY (x.map F) (y.map F)
  exact (joyal_weakEquivalences_iff_kanWeak _).symm.trans ((weakEquivalence_iff _).symm.trans
    (weakEquivalence_toSSet_map_mappingSpaceMap_iff hX hY F x y))

end Joyal

theorem DiagSet.isEssentiallySurjective_iff_toSSet (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) :
    DiagSet.IsEssentiallySurjective F ↔
      (SSet.hoFunctor.map (DiagSet.toSSet.map F)).toFunctor.EssSurj := by
  rw [DiagSet.isEssentiallySurjective_iff_essSurj hX hY]
  have h := homotopyCategoryEquivalence_inverse_comp_homotopyFunctor hX hY F
  constructor
  · intro hF
    have : ((SSet.hoFunctor.map (DiagSet.toSSet.map F)).toFunctor ⋙
        (homotopyCategoryEquivalence hY).inverse).EssSurj := by
      rw [← h]
      infer_instance
    exact Functor.essSurj_of_comp_fully_faithful _ (homotopyCategoryEquivalence hY).inverse
  · intro hF
    have : ((homotopyCategoryEquivalence hX).inverse ⋙ homotopyFunctor hX.1 hY.1 F).EssSurj := by
      rw [h]
      infer_instance
    exact ⟨fun b ↦ ⟨_, ⟨((homotopyCategoryEquivalence hX).inverse ⋙
      homotopyFunctor hX.1 hY.1 F).objObjPreimageIso b⟩⟩⟩

section Joyal

open SSet.modelCategoryJoyal

theorem DiagSet.weakEquivalence_iff_isFullyFaithful_and_isEssentiallySurjective
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map F) ↔
      DiagSet.IsFullyFaithful F ∧ DiagSet.IsEssentiallySurjective F := by
  have hXf : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have hYf : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : SSet.Quasicategory (DiagSet.toSSet.obj X) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X) hXf
  have : SSet.Quasicategory (DiagSet.toSSet.obj Y) :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj Y) hYf
  have (K : SSet.{u}) : IsCofibrant K := by
    rw [isCofibrant_iff, cofibration_iff]
    exact MorphismProperty.monomorphisms.infer_property _
  have e : WeakEquivalence (DiagSet.toSSet.map F) ↔
      WeakEquivalence ((DiagSet.toInfty 1).map F) :=
    isQuillenEquivalence_sSetDiagSetAdj.{u}.weakEquivalence_map_iff ((DiagSet.toInfty 1).map F)
  rw [DiagSet.isFullyFaithful_iff_toSSet hX hY, DiagSet.isEssentiallySurjective_iff_toSSet hX hY,
    ← weakEquivalence_iff_isFullyFaithful_and_essSurj]
  exact e.symm

end Joyal

end Atoms.Diagrammatic
