import Atoms.Shape.GrayCylinder
import Atoms.Shape.GrayTensorMonoidal

open CategoryTheory MonoidalCategory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

def cylAtomGrayTensorIso (U : Atom) : cylAtom U ≅ Atom.grayTensor (atomGlobe 1) U :=
  Atom.isoOfIso ((cylAtomIso U).symm ≪≫ whiskerRightIso (FiniteOGP.ofOGPIso (globe 1)) U.ogp ≪≫
    Atom.grayTensorIso (atomGlobe 1) U)

theorem cylAtomGrayTensorIso_hom_apply (U : Atom) (z : (cylAtom U).ogp) :
    (cylAtomGrayTensorIso U).hom z = (Atom.grayTensorIso (atomGlobe 1) U).hom
      ((FiniteOGP.ofOGPIso (globe 1)).hom ((cylAtomIso U).inv z).1, ((cylAtomIso U).inv z).2) :=
  rfl

theorem cylAtomGrayTensorIso_inv_apply (U : Atom) (z : (Atom.grayTensor (atomGlobe 1) U).ogp) :
    (cylAtomGrayTensorIso U).inv z = (cylAtomIso U).hom
      ((FiniteOGP.ofOGPIso (globe 1)).inv ((Atom.grayTensorIso (atomGlobe 1) U).inv z).1,
        ((Atom.grayTensorIso (atomGlobe 1) U).inv z).2) :=
  rfl

def grayCylinderIsoTensorLeft : grayCylinder ≅ MonoidalCategory.tensorLeft (atomGlobe 1) :=
  NatIso.ofComponents cylAtomGrayTensorIso fun {U V} f => by
    ext z
    change (cylAtomGrayTensorIso V).hom (grayCylinder.map f z) =
      Atom.grayTensorMap (𝟙 (atomGlobe 1)) f ((cylAtomGrayTensorIso U).hom z)
    rw [cylAtomGrayTensorIso_hom_apply, symm_grayCylinder_map_apply, Atom.grayTensorMap_apply,
      cylAtomGrayTensorIso_hom_apply, Iso.hom_inv_id_apply]
    rfl

theorem grayEndpoint_comp_grayCylinderIsoTensorLeft_hom (ε : Bool) :
    grayEndpoint ε ≫ grayCylinderIsoTensorLeft.hom =
      (leftUnitorNatIso Atom).inv ≫ (tensoringLeft Atom).map (atomGlobeVertex ε) := by
  ext U x
  change (cylAtomGrayTensorIso U).hom ((grayEndpoint ε).app U x) =
    Atom.grayTensorMap (atomGlobeVertex ε) (𝟙 U) ((Atom.grayTensorLeftUnitor U).inv x)
  rw [cylAtomGrayTensorIso_hom_apply, symm_grayEndpoint_apply, Atom.grayTensorMap_apply,
    Atom.grayTensorLeftUnitor_inv_apply, Iso.hom_inv_id_apply, atomGlobeVertex_apply,
    ConcreteCategory.id_apply]

theorem grayCylinderIsoTensorLeft_inv_comp_grayContraction :
    grayCylinderIsoTensorLeft.inv ≫ grayContraction =
      (tensoringLeft Atom).map (toAtomPoint (atomGlobe 1)) ≫ (leftUnitorNatIso Atom).hom := by
  ext U z
  change ((cylAtomIso U).inv ((cylAtomGrayTensorIso U).inv z)).2 =
    Atom.grayTensorSnd (atomGlobe 1) U z
  rw [cylAtomGrayTensorIso_inv_apply, Iso.hom_inv_id_apply, Atom.grayTensorSnd_apply]

end Atoms.Shape
