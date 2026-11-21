import Atoms.Shape.GrayTensor
import Atoms.Shape.Horn

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

private theorem isRewritableSubmolecule_grayTensor (V U : Atom) {α : Bool}
    {W : LowerSet (grayProduct V.ogp U.ogp)}
    (hW : (grayProduct V.ogp U.ogp).IsRewritableSubmolecule W
      ((grayProduct V.ogp U.ogp).bdry ⊤ α)) :
    (Atom.grayTensor V U).ogp.IsRewritableSubmolecule (map (Atom.grayTensorIso V U).hom W)
      ((Atom.grayTensor V U).ogp.bdry ⊤ α) := by
  have h := (isRewritableSubmolecule_map_iff (Atom.grayTensorIso V U).hom W _).2 hW
  rwa [map_bdry, map_top_of_isIso] at h

private theorem hornSet_grayTensor (V U : Atom) {α : Bool}
    {W : LowerSet (grayProduct V.ogp U.ogp)}
    (hW : (grayProduct V.ogp U.ogp).IsRewritableSubmolecule W
      ((grayProduct V.ogp U.ogp).bdry ⊤ α)) :
    (isRewritableSubmolecule_grayTensor V U hW).hornSet
        (Atom.grayTensor V U).isMolecule (Atom.grayTensor V U).isAtom.isRound =
      map (Atom.grayTensorIso V U).hom
        (hW.hornSet (isMolecule_grayProduct V.isMolecule U.isMolecule)
          (isAtom_grayProduct V.isAtom U.isAtom).isRound) :=
  SetLike.coe_injective (by
    rw [IsSubmoleculeOf.coe_hornSet, coe_map, IsSubmoleculeOf.coe_hornSet,
      Set.image_sdiff IsInclusion.injective, image_interior, ← coe_map, map_bdryFull,
      map_top_of_isIso])

def HornData.grayTensorRight (h : HornData) (U : Atom) : HornData where
  atom := Atom.grayTensor h.atom U
  positive := by
    rw [Atom.dimension_grayTensor]
    exact Nat.lt_add_right _ h.positive
  side := h.side
  removed := map (Atom.grayTensorIso h.atom U).hom (h.removed ×ˢ (⊤ : LowerSet U.ogp))
  rewritable := isRewritableSubmolecule_grayTensor h.atom U
    (isRewritableSubmolecule_prod_left h.atom.isAtom U.isAtom h.rewritable)

def HornData.grayTensorLeft (U : Atom) (h : HornData) : HornData where
  atom := Atom.grayTensor U h.atom
  positive := by
    rw [Atom.dimension_grayTensor]
    exact Nat.lt_add_left _ h.positive
  side := xor U.dimension.bodd h.side
  removed := map (Atom.grayTensorIso U h.atom).hom ((⊤ : LowerSet U.ogp) ×ˢ h.removed)
  rewritable := isRewritableSubmolecule_grayTensor U h.atom
    (isRewritableSubmolecule_prod_right U.isAtom U.krullDim_eq_dimension h.atom.isAtom
      h.rewritable)

theorem hornSubset_grayTensorRight (h : HornData) (U : Atom) :
    hornSubset (h.grayTensorRight U) =
      map (Atom.grayTensorIso h.atom U).hom
        (hornSubset h ×ˢ (⊤ : LowerSet U.ogp) ⊔ (⊤ : LowerSet h.atom.ogp) ×ˢ U.ogp.bdryFull ⊤) :=
  (hornSet_grayTensor h.atom U _).trans
    (congrArg (map _) (hornSet_prod_left h.atom.isAtom U.isAtom h.rewritable))

theorem hornSubset_grayTensorLeft (U : Atom) (h : HornData) :
    hornSubset (HornData.grayTensorLeft U h) =
      map (Atom.grayTensorIso U h.atom).hom
        (U.ogp.bdryFull ⊤ ×ˢ (⊤ : LowerSet h.atom.ogp) ⊔ (⊤ : LowerSet U.ogp) ×ˢ hornSubset h) :=
  (hornSet_grayTensor U h.atom _).trans
    (congrArg (map _) (hornSet_prod_right U.isAtom U.krullDim_eq_dimension h.atom.isAtom
      h.rewritable))

end Atoms.Shape
