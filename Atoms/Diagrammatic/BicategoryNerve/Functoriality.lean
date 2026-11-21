import Atoms.Diagrammatic.BicategoryNerve.Composite

open CategoryTheory Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe w v u

namespace Atoms.Diagrammatic

variable {B C D : Type u} [Bicategory.{w, v} B] [Bicategory.{w, v} C] [Bicategory.{w, v} D]

def bicategoryNerveMap (F : StrictlyUnitaryPseudofunctor B C) :
    bicategoryNerve B ⟶ bicategoryNerve C where
  app _ := ↾fun ℓ => ⟨ℓ.1.map F.toPseudofunctor, ℓ.2.map F.toPseudofunctor⟩
  naturality _ _ _ := by
    ext ℓ
    exact Subtype.ext (Labelling.map_comap _ F ℓ.1)

theorem bicategoryNerveMap_app {U : Atom} (F : StrictlyUnitaryPseudofunctor B C)
    (ℓ : (bicategoryNerve B).obj (op U)) :
    ((bicategoryNerveMap F).app (op U) ℓ).1 = ℓ.1.map F.toPseudofunctor :=
  rfl

theorem bicategoryNerveMap_id :
    bicategoryNerveMap (StrictlyUnitaryPseudofunctor.id B) = 𝟙 (bicategoryNerve B) := by
  ext U ℓ
  exact Subtype.ext (Labelling.map_id ℓ.1)

theorem bicategoryNerveMap_comp (F : StrictlyUnitaryPseudofunctor B C)
    (G : StrictlyUnitaryPseudofunctor C D) :
    bicategoryNerveMap (F.comp G) = bicategoryNerveMap F ≫ bicategoryNerveMap G := by
  ext U ℓ
  exact Subtype.ext (Labelling.map_comp F.toPseudofunctor G.toPseudofunctor ℓ.1)

theorem bicategoryNerveHomEquiv_comp_bicategoryNerveMap (F : StrictlyUnitaryPseudofunctor B C)
    (P : RDCpx.{0}) [FinEnum P.obj.toOGP] [DecidableLE P.obj.toOGP]
    (φ : realize.{max u v w}.obj P ⟶ bicategoryNerve B) :
    (bicategoryNerveHomEquiv C P (φ ≫ bicategoryNerveMap F)).1 =
      (bicategoryNerveHomEquiv B P φ).1.map F.toPseudofunctor := by
  have h : φ ≫ bicategoryNerveMap F = (bicategoryNerveHomEquiv C P).symm
      ⟨(bicategoryNerveHomEquiv B P φ).1.map F.toPseudofunctor,
        (bicategoryNerveHomEquiv B P φ).2.map F.toPseudofunctor⟩ := by
    conv_lhs => rw [← (bicategoryNerveHomEquiv B P).left_inv φ]
    ext ⟨T⟩ ⟨c⟩
    exact Subtype.ext (Labelling.map_comap _ F _)
  rw [h, Equiv.apply_symm_apply]

namespace PastingDiagram

attribute [local instance high] FinEnum.instFintype

theorem nerveComposite_mapTo (F : StrictlyUnitaryPseudofunctor B C)
    (d : PastingDiagram (bicategoryNerve B)) (hd : d.dim ≤ 2) :
    (d.mapTo (bicategoryNerveMap F)).nerveComposite hd =
      (d.nerveComposite hd).map F.toPseudofunctor := by
  have hM : IsMoleculeIn d.shape.rdc.obj.toOGP ⊤ := d.shape.isMolecule
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le hM (d.krullDim_top_le hd)
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  rw [nerveComposite_eq_pathCell d hd hs ht hxs,
    nerveComposite_eq_pathCell (d.mapTo (bicategoryNerveMap F)) hd hs ht hxs]
  exact (congrArg (Labelling.pathCell hM hxs hs ht)
    (bicategoryNerveHomEquiv_comp_bicategoryNerveMap F d.shape.rdc d.map)).trans
      (Labelling.pathCell_map F.toPseudofunctor _ hM hxs hs ht)

end PastingDiagram

end Atoms.Diagrammatic
