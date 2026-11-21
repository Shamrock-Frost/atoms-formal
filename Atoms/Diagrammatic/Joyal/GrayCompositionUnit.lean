import Atoms.Diagrammatic.Joyal.GrayCompositionAssoc

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open Atoms.Shape Simplicial

universe u v w

namespace Atoms.Diagrammatic

section Restriction

variable {X : DiagSet.{u}}

theorem toDiagSet_map_stdSimplex_map_const {n : ℕ} (k : Fin (n + 1)) :
    (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋n⦌ k)) =
      isTerminalBallAtomPoint.from _ ≫
        Sigma.ι (fun _ : Fin (n + 1) => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι n := by
  rw [← cancel_mono (toDiagSetObjStdSimplexIso.{u} n).hom, Category.assoc,
    toDiagSet_map_stdSimplex_map_comp_hom, Iso.inv_hom_id_assoc, Category.assoc, Category.assoc,
    ι_graySimplexVerticesι_comp_hom, SimplexCategory.const_fac_thru_zero]
  exact (Functor.map_comp (simplexFunctor ⋙ uliftYoneda.{u}) _ _).trans
    (congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _))

theorem isEdgeRestriction_graySimplexFibreOneIso (x : Fin 2 → X.Vertex) :
    IsEdgeRestriction (graySimplexFibreOneIso X x).hom (𝟙 ⦋1⦌) := fun T t => by
  have e : SSet.stdSimplex.{u}.map (𝟙 ⦋1⦌) = 𝟙 _ := SSet.stdSimplex.map_id _
  rw [mappingSpaceHomEquiv_graySimplexFibreOneIso, e, CategoryTheory.Functor.map_id,
    Category.comp_id]

theorem isEdgeRestriction_from_comp_mappingSpaceId {n : ℕ} (x : Fin (n + 1) → X.Vertex)
    (k : Fin (n + 1)) :
    IsEdgeRestriction (isTerminalBallAtomPoint.from (legacyGraySimplexFibre X x) ≫
      X.mappingSpaceId (x k)) (SimplexCategory.const ⦋1⦌ ⦋n⦌ k) := fun T t => by
  rw [← Category.assoc, isTerminalBallAtomPoint.comp_from,
    DiagSet.mappingSpaceHomEquiv_mappingSpaceId, toDiagSet_map_stdSimplex_map_const,
    Functor.map_comp, Category.assoc,
    grayTensorLeft_map_ι_comp_of_comp_eq _ x (relativeMappingSpaceHomEquiv _ _ T t).2 k,
    ← Category.assoc ((grayTensorLeft T).map _), grayTensorLeft_map_grayTensorSnd,
    Category.assoc]

private theorem graySimplexFibreMap_σ_one_comp_graySegalMap (x : Fin 2 → X.Vertex) :
    graySimplexFibreMap X (SimplexCategory.σ 1) x ![x 0, x 1, x 1]
        (fun k => by fin_cases k <;> rfl) ≫ legacyGraySegalMap X _ ≫ (legacyGraySpineFibreTwoIso X
          _).hom =
      (graySimplexFibreOneIso X x).hom ≫
        prod.lift (𝟙 _) (isTerminalBallAtomPoint.from _ ≫ X.mappingSpaceId (x 1)) := by
  refine prod.hom_ext ?_ ?_
  · have e : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by decide
    have h := (isEdgeRestriction_graySpineFibreTwoIso_fst X ![x 0, x 1, x 1]).comp_assoc
      (SimplexCategory.σ 1) (x := x) (fun k => by fin_cases k <;> rfl)
    exact (h.eq_of_eq (isEdgeRestriction_graySimplexFibreOneIso x) e).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_fst _ _)).trans
        (Category.comp_id _))).symm
  · have e : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
        SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by decide
    have h := (isEdgeRestriction_graySpineFibreTwoIso_snd X ![x 0, x 1, x 1]).comp_assoc
      (SimplexCategory.σ 1) (x := x) (fun k => by fin_cases k <;> rfl)
    exact (h.eq_of_eq (isEdgeRestriction_from_comp_mappingSpaceId x 1) e).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_snd _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (isTerminalBallAtomPoint.comp_from _))))).symm

private theorem graySimplexFibreMap_σ_one_comp_grayLongEdge (x : Fin 2 → X.Vertex) :
    graySimplexFibreMap X (SimplexCategory.σ 1) x ![x 0, x 1, x 1]
        (fun k => by fin_cases k <;> rfl) ≫ grayLongEdge X _ =
      (graySimplexFibreOneIso X x).hom :=
  ((isEdgeRestriction_grayLongEdge X _).comp _ _).eq_of_eq
    (isEdgeRestriction_graySimplexFibreOneIso x) (by decide)

private theorem graySimplexFibreMap_σ_zero_comp_graySegalMap (x : Fin 2 → X.Vertex) :
    graySimplexFibreMap X (SimplexCategory.σ 0) x ![x 0, x 0, x 1]
        (fun k => by fin_cases k <;> rfl) ≫ legacyGraySegalMap X _ ≫ (legacyGraySpineFibreTwoIso X
          _).hom =
      (graySimplexFibreOneIso X x).hom ≫
        prod.lift (isTerminalBallAtomPoint.from _ ≫ X.mappingSpaceId (x 0)) (𝟙 _) := by
  refine prod.hom_ext ?_ ?_
  · have e : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
        SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 := by decide
    have h := (isEdgeRestriction_graySpineFibreTwoIso_fst X ![x 0, x 0, x 1]).comp_assoc
      (SimplexCategory.σ 0) (x := x) (fun k => by fin_cases k <;> rfl)
    exact (h.eq_of_eq (isEdgeRestriction_from_comp_mappingSpaceId x 0) e).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_fst _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (isTerminalBallAtomPoint.comp_from _))))).symm
  · have e : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by decide
    have h := (isEdgeRestriction_graySpineFibreTwoIso_snd X ![x 0, x 0, x 1]).comp_assoc
      (SimplexCategory.σ 0) (x := x) (fun k => by fin_cases k <;> rfl)
    exact (h.eq_of_eq (isEdgeRestriction_graySimplexFibreOneIso x) e).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_snd _ _)).trans
        (Category.comp_id _))).symm

private theorem graySimplexFibreMap_σ_zero_comp_grayLongEdge (x : Fin 2 → X.Vertex) :
    graySimplexFibreMap X (SimplexCategory.σ 0) x ![x 0, x 0, x 1]
        (fun k => by fin_cases k <;> rfl) ≫ grayLongEdge X _ =
      (graySimplexFibreOneIso X x).hom :=
  ((isEdgeRestriction_grayLongEdge X _).comp _ _).eq_of_eq
    (isEdgeRestriction_graySimplexFibreOneIso x) (by decide)

end Restriction

private theorem map_comp_grayComposition_eq_id {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {y : Fin 3 → X.Vertex} {E : DiagSet.{u}}
    (e : E ≅ (X.mappingSpace (y 0) (y 2)).toFunctor) (D : E ⟶ legacyGraySimplexFibre X y)
    (P : (X.mappingSpace (y 0) (y 2)).toFunctor ⟶
      (X.mappingSpace (y 0) (y 1)).toFunctor ⨯ (X.mappingSpace (y 1) (y 2)).toFunctor)
    (hs : D ≫ legacyGraySegalMap X y ≫ (legacyGraySpineFibreTwoIso X y).hom = e.hom ≫ P)
    (hl : D ≫ grayLongEdge X y = e.hom) :
    L.map ((DiagSet.toInfty 0).map P) ≫ grayComposition L hX y = 𝟙 _ := by
  refine (cancel_epi (L.map ((DiagSet.toInfty 0).map e.hom))).1 ?_
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← hs, Functor.map_comp,
    Functor.map_comp, Category.assoc, map_graySpineFibreTwo_comp_grayComposition,
    ← Functor.map_comp, ← Functor.map_comp, hl, Category.comp_id]

theorem grayComposition_id_right {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (x : Fin 2 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map (prod.lift (𝟙 (X.mappingSpace (x 0) (x 1)).toFunctor)
        (isTerminalBallAtomPoint.from _ ≫ X.mappingSpaceId (x 1)))) ≫
      grayComposition L hX ![x 0, x 1, x 1] = 𝟙 _ :=
  map_comp_grayComposition_eq_id L hX (y := ![x 0, x 1, x 1]) (graySimplexFibreOneIso X x) _ _
    (graySimplexFibreMap_σ_one_comp_graySegalMap x)
    (graySimplexFibreMap_σ_one_comp_grayLongEdge x)

theorem grayComposition_id_left {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (x : Fin 2 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map (prod.lift
        (isTerminalBallAtomPoint.from _ ≫ X.mappingSpaceId (x 0))
        (𝟙 (X.mappingSpace (x 0) (x 1)).toFunctor))) ≫
      grayComposition L hX ![x 0, x 0, x 1] = 𝟙 _ :=
  map_comp_grayComposition_eq_id L hX (y := ![x 0, x 0, x 1]) (graySimplexFibreOneIso X x) _ _
    (graySimplexFibreMap_σ_zero_comp_graySegalMap x)
    (graySimplexFibreMap_σ_zero_comp_grayLongEdge x)

end Atoms.Diagrammatic
