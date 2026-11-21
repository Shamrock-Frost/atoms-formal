import Atoms.Diagrammatic.Joyal.GrayCompositionAssoc

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Homotopical Atoms.Shape Simplicial

universe u v w

namespace Atoms.Diagrammatic

section Postcomp

variable {X Y : DiagSet.{u}} (p : X ⟶ Y)

theorem graySimplexVerticesHomEquiv_symm_comp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) :
    (graySimplexVerticesHomEquiv n X).symm x ≫ p =
      (graySimplexVerticesHomEquiv n Y).symm (fun i => (x i).map p) :=
  Sigma.hom_ext _ _ fun k => by
    rw [ι_graySimplexVerticesHomEquiv_symm_assoc, ι_graySimplexVerticesHomEquiv_symm,
      vertexHom_comp]

noncomputable def graySimplexFibrePostcomp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) :
    legacyGraySimplexFibre X x ⟶ legacyGraySimplexFibre Y (fun i => (x i).map p) :=
  relativeMappingSpaceMapOfEq _ p (graySimplexVerticesHomEquiv_symm_comp p x)

theorem relativeMappingSpaceHomEquiv_graySimplexFibrePostcomp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySimplexFibre X x) :
    (relativeMappingSpaceHomEquiv _ _ T (t ≫ graySimplexFibrePostcomp p x)).1 =
      (relativeMappingSpaceHomEquiv _ _ T t).1 ≫ p :=
  relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfEq _ p _ t

noncomputable def graySpineFibrePostcomp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) :
    legacyGraySpineFibre X x ⟶ legacyGraySpineFibre Y (fun i => (x i).map p) :=
  relativeMappingSpaceMapOfEq _ p (graySimplexVerticesHomEquiv_symm_comp p x)

theorem relativeMappingSpaceHomEquiv_graySpineFibrePostcomp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySpineFibre X x) :
    (relativeMappingSpaceHomEquiv _ _ T (t ≫ graySpineFibrePostcomp p x)).1 =
      (relativeMappingSpaceHomEquiv _ _ T t).1 ≫ p :=
  relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfEq _ p _ t

theorem graySegalMap_graySpineFibrePostcomp {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) :
    legacyGraySegalMap X x ≫ graySpineFibrePostcomp p x =
      graySimplexFibrePostcomp p x ≫ legacyGraySegalMap Y _ :=
  relativeMappingSpaceRestrict_mapOfEq _ _ p (graySimplexVerticesHomEquiv_symm_comp p x)

theorem graySpineFibreTwoIso_hom_prodMap_mappingSpaceMap
    (x : Fin 3 → X.Vertex) :
    (legacyGraySpineFibreTwoIso X x).hom ≫
        prod.map (X.mappingSpaceMap p (x 0) (x 1)) (X.mappingSpaceMap p (x 1) (x 2)) =
      graySpineFibrePostcomp p x ≫
        (legacyGraySpineFibreTwoIso Y (fun i => (x i).map p)).hom := by
  have h₂ := relativeMappingSpaceHomEquiv_graySpineFibrePostcomp p x (𝟙 _)
  rw [Category.id_comp] at h₂
  refine prod.hom_ext ((Y.mappingSpaceHomEquiv _ _ _).injective (Subtype.ext ?_))
    ((Y.mappingSpaceHomEquiv _ _ _).injective (Subtype.ext ?_))
  · have h₁ := mappingSpaceHomEquiv_graySpineFibreTwoIso_fst X x (𝟙 _)
    rw [Category.id_comp] at h₁
    rw [Category.assoc, Category.assoc, prod.map_fst, ← Category.assoc,
      DiagSet.mappingSpaceHomEquiv_mappingSpaceMap, h₁,
      mappingSpaceHomEquiv_graySpineFibreTwoIso_fst Y (fun i => (x i).map p),
      h₂, Category.assoc]
  · have h₁ := mappingSpaceHomEquiv_graySpineFibreTwoIso_snd X x (𝟙 _)
    rw [Category.id_comp] at h₁
    rw [Category.assoc, Category.assoc, prod.map_snd, ← Category.assoc,
      DiagSet.mappingSpaceHomEquiv_mappingSpaceMap, h₁,
      mappingSpaceHomEquiv_graySpineFibreTwoIso_snd Y (fun i => (x i).map p),
      h₂, Category.assoc]

theorem grayLongEdge_mappingSpaceMap (x : Fin 3 → X.Vertex) :
    grayLongEdge X x ≫ X.mappingSpaceMap p (x 0) (x 2) =
      graySimplexFibrePostcomp p x ≫
        grayLongEdge Y (fun i => (x i).map p) := by
  refine (Y.mappingSpaceHomEquiv _ _ _).injective (Subtype.ext ?_)
  have h₁ := mappingSpaceHomEquiv_grayLongEdge X x (𝟙 _)
  have h₂ := relativeMappingSpaceHomEquiv_graySimplexFibrePostcomp p x (𝟙 _)
  rw [Category.id_comp] at h₁ h₂
  rw [DiagSet.mappingSpaceHomEquiv_mappingSpaceMap, h₁,
    mappingSpaceHomEquiv_grayLongEdge Y (fun i => (x i).map p), h₂,
    Category.assoc]

end Postcomp

theorem grayComposition_naturality {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (p : X ⟶ Y)
    (x : Fin 3 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map (prod.map (X.mappingSpaceMap p (x 0) (x 1))
        (X.mappingSpaceMap p (x 1) (x 2)))) ≫
      grayComposition L hY (fun i => (x i).map p) =
    grayComposition L hX x ≫ L.map ((DiagSet.toInfty 0).map (X.mappingSpaceMap p (x 0) (x 2))) := by
  have hs := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_graySpineFibreTwo hX x)
  have : IsIso (L.map ((DiagSet.toInfty 0).map
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom))) :=
    Localization.inverts L (weakEquivalences _) _ ((weakEquivalence_iff _).1 hs)
  refine (cancel_epi (L.map ((DiagSet.toInfty 0).map
    (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom)))).1 ?_
  have sq : (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) ≫
      prod.map (X.mappingSpaceMap p (x 0) (x 1)) (X.mappingSpaceMap p (x 1) (x 2)) =
      graySimplexFibrePostcomp p x ≫ (legacyGraySegalMap Y (fun i => (x i).map p) ≫
        (legacyGraySpineFibreTwoIso Y (fun i => (x i).map p)).hom) := by
    rw [Category.assoc, graySpineFibreTwoIso_hom_prodMap_mappingSpaceMap, ← Category.assoc,
      graySegalMap_graySpineFibrePostcomp, Category.assoc]
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, sq,
    Functor.map_comp (DiagSet.toInfty 0), Functor.map_comp L, Category.assoc,
    map_graySpineFibreTwo_comp_grayComposition]
  conv_rhs => rw [← Category.assoc, map_graySpineFibreTwo_comp_grayComposition,
    ← Functor.map_comp, ← Functor.map_comp, grayLongEdge_mappingSpaceMap,
    Functor.map_comp (DiagSet.toInfty 0), Functor.map_comp L]

theorem homMk_comp_homMk_graySimplexEdge {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {n : ℕ}
    (x : Fin (n + 1) → X.Vertex)
    (t : (legacyGraySimplexFibre X x).Vertex) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    HomotopyCategory.homMk hX.1
        (X.mappingSpaceVerticesEquiv _ _ (t.map (graySimplexEdge X x i j hij))) ≫
      HomotopyCategory.homMk hX.1
        (X.mappingSpaceVerticesEquiv _ _ (t.map (graySimplexEdge X x j k hjk))) =
    HomotopyCategory.homMk hX.1
      (X.mappingSpaceVerticesEquiv _ _ (t.map (graySimplexEdge X x i k (hij.trans hjk)))) := by
  have hf {a b : Fin (n + 1)} (hab : a ≤ b) (φ : ⦋1⦌ ⟶ ⦋2⦌)
      (hφ : φ ≫ SimplexCategory.mkOfLeComp i j k hij hjk = SimplexCategory.mkOfLe a b hab) :
      (DiagSet.toSSet.obj X).map φ.op ((DiagSet.toSSet.obj X).map
          (SimplexCategory.mkOfLeComp i j k hij hjk).op (graySimplexFibreSimplex x t)) =
        (X.edgeEquivSSet (X.mappingSpaceVerticesEquiv _ _ ((DiagSet.vertexEquivSSet _).symm
          ((DiagSet.toSSet.map (graySimplexEdge X x a b hab)).app _ t)))).edge := by
    rw [mappingSpaceVerticesEquiv_edge_of_restriction _ _ t
      (mappingSpaceHomEquiv_graySimplexEdge X x a b hab _), ← hφ, op_comp,
      Functor.map_comp_apply]
  exact homMk_comp_homMk_of_compStruct hX (SSet.Edge.CompStruct.mk _
    (hf hij (SimplexCategory.δ 2) (SimplexCategory.Hom.ext_one_left _ _))
    (hf hjk (SimplexCategory.δ 0) (SimplexCategory.Hom.ext_one_left _ _))
    (hf (hij.trans hjk) (SimplexCategory.δ 1) (SimplexCategory.Hom.ext_one_left _ _)))

end Atoms.Diagrammatic
