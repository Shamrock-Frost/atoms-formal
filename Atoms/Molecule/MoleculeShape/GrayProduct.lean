import Atoms.Molecule.Construction.GrayProductMolecule
import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Molecule.MoleculeShape.Basic

open CategoryTheory Order

namespace Atoms.Molecule.MoleculeShape

open OGP

def grayProduct (P Q : MoleculeShape) : MoleculeShape :=
  ofOGP (OGP.grayProduct P.ogp Q.ogp) (OGP.isMolecule_grayProduct P.isMolecule Q.isMolecule)

def grayProductIso (P Q : MoleculeShape) : OGP.grayProduct P.ogp Q.ogp ≅ (P.grayProduct Q).ogp :=
  FiniteOGP.ofOGPIso _

variable (P Q : MoleculeShape)

theorem dimension_grayProduct : (P.grayProduct Q).dimension = P.dimension + Q.dimension := by
  have h := dimension_ofOGP (OGP.grayProduct P.ogp Q.ogp)
    (OGP.isMolecule_grayProduct P.isMolecule Q.isMolecule)
  rw [krullDim_grayProduct P.krullDim_eq_dimension Q.krullDim_eq_dimension] at h
  exact_mod_cast h

theorem isRound_grayProduct {P Q : MoleculeShape} (hP : P.IsRound) (hQ : Q.IsRound) :
    (P.grayProduct Q).IsRound := by
  refine isRound_ofOGP _ _ ?_
  rw [← LowerSet.top_prod_top]
  exact isRound_prod hP hQ

variable {P Q} {P' Q' : MoleculeShape}

def grayProductMap (f : P.ogp ⟶ P'.ogp) (g : Q.ogp ⟶ Q'.ogp) :
    (P.grayProduct Q).ogp ⟶ (P'.grayProduct Q').ogp :=
  (P.grayProductIso Q).inv ≫ OGP.grayProductMap f g ≫ (P'.grayProductIso Q').hom

theorem grayProductMap_apply (f : P.ogp ⟶ P'.ogp) (g : Q.ogp ⟶ Q'.ogp)
    (p : (P.grayProduct Q).ogp) :
    grayProductMap f g p = (P'.grayProductIso Q').hom
      (f ((P.grayProductIso Q).inv p).1, g ((P.grayProductIso Q).inv p).2) :=
  rfl

instance instIsInclusionGrayProductMap (f : P.ogp ⟶ P'.ogp) (g : Q.ogp ⟶ Q'.ogp) [IsInclusion f]
    [IsInclusion g] :
    IsInclusion (grayProductMap f g) :=
  IsInclusion.comp _ _

theorem map_grayProductMap (f : P.ogp ⟶ P'.ogp) (g : Q.ogp ⟶ Q'.ogp) (S : LowerSet P.ogp)
    (T : LowerSet Q.ogp) :
    OGP.map (grayProductMap f g) (OGP.map (P.grayProductIso Q).hom (S ×ˢ T)) =
      OGP.map (P'.grayProductIso Q').hom (OGP.map f S ×ˢ OGP.map g T) := by
  refine SetLike.ext fun z => ?_
  simp only [OGP.mem_map, LowerSet.mem_prod, Prod.exists, grayProductMap_apply]
  constructor
  · rintro ⟨_, ⟨a, b, ⟨ha, hb⟩, rfl⟩, rfl⟩
    refine ⟨f a, g b, ⟨⟨a, ha, rfl⟩, b, hb, rfl⟩, ?_⟩
    rw [Iso.hom_inv_id_apply]
  · rintro ⟨_, _, ⟨⟨a, ha, rfl⟩, b, hb, rfl⟩, rfl⟩
    refine ⟨_, ⟨a, b, ⟨ha, hb⟩, rfl⟩, ?_⟩
    rw [Iso.hom_inv_id_apply]

theorem map_grayProductMap_top (f : P.ogp ⟶ P'.ogp) (g : Q.ogp ⟶ Q'.ogp) :
    OGP.map (grayProductMap f g) ⊤ =
      OGP.map (P'.grayProductIso Q').hom (OGP.map f ⊤ ×ˢ OGP.map g ⊤) := by
  rw [← map_grayProductMap, LowerSet.top_prod_top, map_top_of_isIso (P.grayProductIso Q).hom]

end Atoms.Molecule.MoleculeShape
