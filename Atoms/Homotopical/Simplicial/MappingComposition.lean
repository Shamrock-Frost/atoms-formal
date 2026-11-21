import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SimplexFibre
import Atoms.Homotopical.Simplicial.KanQuillen

open CategoryTheory Limits MorphismProperty Simplicial

universe u v w

namespace Atoms.Homotopical

variable {H : Type v} [Category.{w} H] (L : SSet.{u} ⥤ H) [L.IsLocalization kanWeak]
  (X : SSet.{u}) [X.Quasicategory]

theorem kanWeak_simplexFibreSegalMap_comp {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) {Y : SSet.{u}}
    (e : SSet.spineFibre X x ≅ Y) : kanWeak (SSet.simplexFibreSegalMap X x ≫ e.hom) :=
  isALocalizer_kanWeak.rlp_monomorphisms_le _
    (SSet.rlp_monomorphisms_simplexFibreSegalMap_comp X x e)

noncomputable def mappingSpaceSpineComposition {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌) :
    L.obj (∏ᶜ fun i : Fin (n + 1) ↦ SSet.mappingSpace X (x i.castSucc) (x i.succ)) ⟶
      L.obj (SSet.mappingSpace X (x 0) (x (Fin.last _))) :=
  (Localization.isoOfHom L kanWeak _
      (kanWeak_simplexFibreSegalMap_comp X x (SSet.simplexFibreSpineIso X x))).inv ≫
    L.map (SSet.simplexFibreEdge X x 0 (Fin.last _) (Fin.zero_le _))

theorem map_simplexFibreSegalMap_comp_mappingSpaceSpineComposition {n : ℕ}
    (x : Fin (n + 2) → X _⦋0⦌) :
    L.map (SSet.simplexFibreSegalMap X x ≫ (SSet.simplexFibreSpineIso X x).hom) ≫
        mappingSpaceSpineComposition L X x =
      L.map (SSet.simplexFibreEdge X x 0 (Fin.last _) (Fin.zero_le _)) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

noncomputable def mappingSpaceComposition (x : Fin 3 → X _⦋0⦌) :
    L.obj (SSet.mappingSpace X (x 0) (x 1) ⨯ SSet.mappingSpace X (x 1) (x 2)) ⟶
      L.obj (SSet.mappingSpace X (x 0) (x 2)) :=
  (Localization.isoOfHom L kanWeak _
      (kanWeak_simplexFibreSegalMap_comp X x (SSet.simplexFibreSpineTwoIso X x))).inv ≫
    L.map (SSet.simplexFibreEdge X x 0 2 (by decide))

theorem map_simplexFibreSegalMap_comp_mappingSpaceComposition (x : Fin 3 → X _⦋0⦌) :
    L.map (SSet.simplexFibreSegalMap X x ≫ (SSet.simplexFibreSpineTwoIso X x).hom) ≫
        mappingSpaceComposition L X x =
      L.map (SSet.simplexFibreEdge X x 0 2 (by decide)) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

theorem map_prodLift_comp_mappingSpaceComposition (x : Fin 3 → X _⦋0⦌) :
    L.map (prod.lift (Pi.π _ 0) (Pi.π _ 1)) ≫ mappingSpaceComposition L X x =
      mappingSpaceSpineComposition L X x := by
  rw [← (Localization.isoOfHom L kanWeak _
    (kanWeak_simplexFibreSegalMap_comp X x (SSet.simplexFibreSpineIso X x))).cancel_iso_hom_left,
    Localization.isoOfHom_hom, map_simplexFibreSegalMap_comp_mappingSpaceSpineComposition,
    ← Functor.map_comp_assoc, Category.assoc, ← SSet.simplexFibreSpineTwoIso_hom,
    map_simplexFibreSegalMap_comp_mappingSpaceComposition]
  rfl

end Atoms.Homotopical
