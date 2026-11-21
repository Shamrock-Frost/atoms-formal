import Atoms.Diagrammatic.FullyFaithful
import Atoms.Diagrammatic.MappingComponents
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpaceMap
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpacePiZero

open CategoryTheory

universe u

namespace Atoms.Diagrammatic

private noncomputable def simplicialMappingSpaceComponentsEquiv
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    SSet.π₀ (SSet.mappingSpace (DiagSet.toSSet.obj X)
      (X.vertexEquivSSet x) (X.vertexEquivSSet y)) ≃
      (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj
        (DiagSet.toSSet.obj X)) (X.vertexEquivSSet x) ⟶
        SSet.Truncated.HomotopyCategory.mk (X.vertexEquivSSet y)) := by
  letI : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X)
      ((isFibrant_infty_iff 1 X).2 hX)
  exact SSet.π₀MappingSpaceEquiv _ _ _

noncomputable def mappingSpaceπ₀Comparison {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) ≃
      SSet.π₀ (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :=
  (X.mappingSpaceπ₀Equiv hX x y).trans
    ((homotopyCategoryEquivalence hX).fullyFaithfulInverse.homEquiv.symm.trans
      (simplicialMappingSpaceComponentsEquiv hX x y).symm)

private theorem mappingSpaceπ₀Comparison_hom {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex)
    (a : SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)) :
    (homotopyCategoryEquivalence hX).inverse.map
      (simplicialMappingSpaceComponentsEquiv hX x y (mappingSpaceπ₀Comparison hX x y a)) =
        X.mappingSpaceπ₀Equiv hX x y a := by
  exact (congrArg (homotopyCategoryEquivalence hX).inverse.map
    ((simplicialMappingSpaceComponentsEquiv hX x y).apply_symm_apply _)).trans
      ((homotopyCategoryEquivalence hX).fullyFaithfulInverse.homEquiv.apply_symm_apply _)

theorem mappingSpaceπ₀Comparison_mk {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) (e : X.Edge x y) :
    mappingSpaceπ₀Comparison hX x y
      (SSet.π₀.mk (DiagSet.vertexEquivSSet _ ((X.mappingSpaceVerticesEquiv x y).symm e))) =
        SSet.π₀.mk ((SSet.mappingSpaceVerticesEquiv _ _ _).symm (X.edgeEquivSSet e)) := by
  apply (simplicialMappingSpaceComponentsEquiv hX x y).injective
  apply (homotopyCategoryEquivalence hX).inverse.map_injective
  rw [mappingSpaceπ₀Comparison_hom, DiagSet.mappingSpaceπ₀Equiv_mk]
  change _ = (homotopyCategoryEquivalence hX).inverse.map
    (SSet.Truncated.HomotopyCategory.homMk
      (SSet.mappingSpaceVerticesEquiv _ _ _
        ((SSet.mappingSpaceVerticesEquiv _ _ _).symm (X.edgeEquivSSet e))).toTruncated)
  rw [Equiv.apply_symm_apply, homotopyCategoryEquivalence_inverse_map_homMk,
    Equiv.symm_apply_apply]

theorem mappingSpaceπ₀Comparison_homotopyCategory {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex)
    (a : SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)) :
    letI : (DiagSet.toSSet.obj X).Quasicategory :=
      quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X)
        ((isFibrant_infty_iff 1 X).2 hX)
    (homotopyCategoryEquivalence hX).inverse.map
      (SSet.π₀MappingSpaceEquiv _ _ _ (mappingSpaceπ₀Comparison hX x y a)) =
        X.mappingSpaceπ₀Equiv hX x y a :=
  mappingSpaceπ₀Comparison_hom hX x y a

theorem mappingSpaceπ₀Comparison_mapπ₀ {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) (x y : X.Vertex)
    (a : SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor)) :
    mappingSpaceπ₀Comparison hY (x.map f) (y.map f)
      (SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) a) =
        SSet.mapπ₀ (SSet.mappingSpaceMap (DiagSet.toSSet.map f)
          (X.vertexEquivSSet x) (X.vertexEquivSSet y)) (mappingSpaceπ₀Comparison hX x y a) := by
  induction a with | mk w => ?_
  obtain ⟨e, rfl⟩ :=
    ((DiagSet.vertexEquivSSet _).symm.trans (X.mappingSpaceVerticesEquiv x y)).symm.surjective w
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [SSet.mapπ₀_mk, mappingSpaceπ₀Comparison_mk, SSet.mapπ₀_mk]
  have h : (DiagSet.toSSet.map (X.mappingSpaceMap f x y)).app _
      (DiagSet.vertexEquivSSet _ ((X.mappingSpaceVerticesEquiv x y).symm e)) =
      DiagSet.vertexEquivSSet _ ((Y.mappingSpaceVerticesEquiv _ _).symm (e.map f)) := by
    apply ((DiagSet.vertexEquivSSet _).symm.trans (Y.mappingSpaceVerticesEquiv _ _)).injective
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [← DiagSet.vertexEquivSSet_map, Equiv.symm_apply_apply]
    apply Y.edgeEquivSSet.injective
    rw [DiagSet.mappingSpaceVerticesEquiv_map, Equiv.apply_symm_apply, DiagSet.edgeEquivSSet_map]
  rw [h, mappingSpaceπ₀Comparison_mk]
  congr 1
  apply (SSet.mappingSpaceVerticesEquiv _ _ _).injective
  rw [Equiv.apply_symm_apply]
  have hn := SSet.mappingSpaceVerticesEquiv_map (DiagSet.toSSet.map f)
    (X.vertexEquivSSet x) (X.vertexEquivSSet y)
    ((SSet.mappingSpaceVerticesEquiv _ _ _).symm (X.edgeEquivSSet e))
  simp only [Equiv.apply_symm_apply] at hn
  rw [DiagSet.edgeEquivSSet_map]
  apply SSet.Edge.ext
  exact (congrArg SSet.Edge.edge hn).symm

theorem mappingSpaceπ₀Comparison_bipointedHom {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex)
    (a : SSet.π₀ (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)))) :
    letI : (DiagSet.toSSet.obj X).Quasicategory :=
      quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj X)
        ((isFibrant_infty_iff 1 X).2 hX)
    (homotopyCategoryEquivalence hX).inverse.map (SSet.π₀MappingSpaceEquiv _ _ _
      (mappingSpaceπ₀Comparison hX x y
        ((X.mappingSpaceπ₀Equiv hX x y).symm (X.bipointedHomπ₀Equiv hX x y a)))) =
      X.bipointedHomπ₀Equiv hX x y a :=
  (mappingSpaceπ₀Comparison_hom hX x y _).trans
    ((X.mappingSpaceπ₀Equiv hX x y).apply_symm_apply _)

noncomputable def bipointedHomMappingSpaceπ₀Comparison {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    SSet.π₀ (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y))) ≃
      SSet.π₀ (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :=
  (X.bipointedHomπ₀Equiv hX x y).trans
    ((X.mappingSpaceπ₀Equiv hX x y).symm.trans (mappingSpaceπ₀Comparison hX x y))

theorem bipointedHomMappingSpaceπ₀Comparison_mk {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) (e : X.Edge x y) :
    bipointedHomMappingSpaceπ₀Comparison hX x y (SSet.π₀.mk
      (DiagSet.vertexEquivSSet _ ((X.bipointedHomVerticesEquiv x y).symm e))) =
      SSet.π₀.mk ((SSet.mappingSpaceVerticesEquiv _ _ _).symm (X.edgeEquivSSet e)) := by
  change mappingSpaceπ₀Comparison hX x y
      ((X.mappingSpaceπ₀Equiv hX x y).symm
        (X.bipointedHomπ₀Equiv hX x y (SSet.π₀.mk
          (DiagSet.vertexEquivSSet _ ((X.bipointedHomVerticesEquiv x y).symm e))))) = _
  rw [DiagSet.bipointedHomπ₀Equiv_mk, ← DiagSet.mappingSpaceπ₀Equiv_mk hX x y e,
    Equiv.symm_apply_apply, mappingSpaceπ₀Comparison_mk]

theorem bipointedHomMappingSpaceπ₀Comparison_mapπ₀ {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (f : X ⟶ Y) (x y : X.Vertex)
    (a : SSet.π₀ (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)))) :
    bipointedHomMappingSpaceπ₀Comparison hY (x.map f) (y.map f)
      (SSet.mapπ₀ (DiagSet.toSSet.map (bipointedHom.map (DiagSet.bipointMap f x y))) a) =
      SSet.mapπ₀ (SSet.mappingSpaceMap (DiagSet.toSSet.map f)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y))
          (bipointedHomMappingSpaceπ₀Comparison hX x y a) := by
  let b := (X.mappingSpaceπ₀Equiv hX x y).symm (X.bipointedHomπ₀Equiv hX x y a)
  have hb : (Y.mappingSpaceπ₀Equiv hY (x.map f) (y.map f)).symm
      (Y.bipointedHomπ₀Equiv hY _ _
        (SSet.mapπ₀ (DiagSet.toSSet.map (bipointedHom.map (DiagSet.bipointMap f x y))) a)) =
      SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap f x y)) b := by
    apply (Y.mappingSpaceπ₀Equiv hY _ _).injective
    rw [Equiv.apply_symm_apply, DiagSet.mappingSpaceπ₀Equiv_mapπ₀ hX hY,
      DiagSet.bipointedHomπ₀Equiv_mapπ₀ hX hY]
    exact congrArg (homotopyFunctor hX.1 hY.1 f).map
      ((X.mappingSpaceπ₀Equiv hX x y).apply_symm_apply _).symm
  exact (congrArg (mappingSpaceπ₀Comparison hY _ _) hb).trans
    (mappingSpaceπ₀Comparison_mapπ₀ hX hY f x y b)

end Atoms.Diagrammatic
