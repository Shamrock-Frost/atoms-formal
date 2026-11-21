import Atoms.Diagrammatic.Horn.ModelStructure

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

def atomicHornInclusions : MorphismProperty DiagSet.{u} :=
  MorphismProperty.ofHoms fun h : AtomicHornData => hornInclusion h.toHornData

def IsAtomicHornFibrant (X : DiagSet.{u}) : Prop :=
  atomicHornInclusions.rlp (terminal.from X)

theorem atomicHornInclusions_le_hornInclusions :
    atomicHornInclusions.{u} ≤ hornInclusions := by
  rw [atomicHornInclusions, MorphismProperty.ofHoms_le_iff]
  intro h
  exact MorphismProperty.ofHoms.mk h.1

instance isSmall_atomicHornInclusions :
    MorphismProperty.IsSmall.{u} atomicHornInclusions.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem endpointBox_sphereInclusion_mem_saturation_atomicHornInclusions (ε : Bool) (U : Atom) :
    MorphismProperty.saturation.{u} atomicHornInclusions.{u}
      (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)) := by
  obtain ⟨e⟩ := endpointBox_sphereInclusion_iso ε U
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2
    (MorphismProperty.le_saturation atomicHornInclusions _
      (MorphismProperty.ofHoms.mk (⟨endpointHornData ε U, endpointHornData_isAtomic ε U⟩ :
        AtomicHornData)))

theorem bothBox_hornInclusion_mem_saturation_atomicHornInclusions (h : AtomicHornData) :
    MorphismProperty.saturation.{u} atomicHornInclusions.{u}
      (grayExactCylinder.{u}.bothBox (hornInclusion h.toHornData)) := by
  obtain ⟨e⟩ := bothBox_hornInclusion_iso h.toHornData
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2
    (MorphismProperty.le_saturation atomicHornInclusions _
      (MorphismProperty.ofHoms.mk (⟨cylinderHornData h.toHornData, cylinderHornData_isAtomic h⟩ :
        AtomicHornData)))

private theorem bothBox_mem_saturation_atomicHornInclusions {K X : DiagSet.{u}} (i : K ⟶ X)
    (hi : atomicHornInclusions i) :
    MorphismProperty.saturation.{u} atomicHornInclusions.{u} (grayExactCylinder.{u}.bothBox i) := by
  obtain ⟨H⟩ := hi
  exact bothBox_hornInclusion_mem_saturation_atomicHornInclusions H

theorem isAnodyneClass_saturation_atomicHornInclusions :
    HomotopicalAlgebra.IsAnodyneClass grayExactCylinder.{u} atomicHornInclusions
      (MorphismProperty.saturation.{u} atomicHornInclusions.{u}) :=
  isAnodyneClass_saturation_of_boxes atomicHornInclusions
    endpointBox_sphereInclusion_mem_saturation_atomicHornInclusions
    bothBox_mem_saturation_atomicHornInclusions

theorem anodyne_atomicHornInclusions :
    grayExactCylinder.{u}.anodyne atomicHornInclusions =
      MorphismProperty.saturation.{u} atomicHornInclusions.{u} :=
  anodyne_eq_saturation_of_boxes atomicHornInclusions
    endpointBox_sphereInclusion_mem_saturation_atomicHornInclusions
    bothBox_mem_saturation_atomicHornInclusions

theorem isFibrant_atomicHornInclusions_iff (X : DiagSet.{u}) :
    grayExactCylinder.{u}.IsFibrant atomicHornInclusions X ↔ IsAtomicHornFibrant X :=
  isFibrant_iff_rlp_of_boxes atomicHornInclusions
    endpointBox_sphereInclusion_mem_saturation_atomicHornInclusions
    bothBox_mem_saturation_atomicHornInclusions X

end Atoms.Diagrammatic
