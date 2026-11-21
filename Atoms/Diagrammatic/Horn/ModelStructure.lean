import Atoms.Diagrammatic.Horn.Basic

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

theorem isAnodyneClass_saturation_of_boxes (S : MorphismProperty DiagSet.{u})
    (hend : ∀ (ε : Bool) (U : Atom),
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)))
    (hboth : ∀ {K X : DiagSet.{u}} (i : K ⟶ X), S i →
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.bothBox i)) :
    HomotopicalAlgebra.IsAnodyneClass grayExactCylinder.{u} S
      (MorphismProperty.saturation.{u} S) where
  isSaturated := inferInstance
  generators_le := MorphismProperty.le_saturation _
  endpointBox_mem ε {_ _} i hi := by
    have := grayExactCylinder.{u}.isSaturated_endpointBox_preimage ε
      (MorphismProperty.saturation.{u} S)
    refine MorphismProperty.saturation_le.{u} sphereInclusions.{u}
      (NatTrans.leibnizPreimage (grayExactCylinder.{u}.endpoint ε)
        (MorphismProperty.saturation.{u} S)) (fun _ _ t ht ↦ ?_) i
      ((monomorphisms_eq_saturation_sphereInclusions ▸ hi : _))
    obtain ⟨U⟩ := ht
    exact hend ε U
  bothBox_mem {_ _} i _ h := by
    have := grayExactCylinder.{u}.isSaturated_bothBox_preimage (MorphismProperty.saturation.{u} S)
    exact MorphismProperty.saturation_le.{u} S
      (NatTrans.leibnizPreimage grayExactCylinder.{u}.endpointsNatTrans
        (MorphismProperty.saturation.{u} S)) (fun _ _ t ht ↦ hboth t ht) i h

theorem anodyne_eq_saturation_of_boxes (S : MorphismProperty DiagSet.{u})
    (hend : ∀ (ε : Bool) (U : Atom),
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)))
    (hboth : ∀ {K X : DiagSet.{u}} (i : K ⟶ X), S i →
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.bothBox i)) :
    grayExactCylinder.{u}.anodyne S = MorphismProperty.saturation.{u} S :=
  le_antisymm
    (grayExactCylinder.{u}.anodyne_le _ _ (isAnodyneClass_saturation_of_boxes S hend hboth))
    (MorphismProperty.saturation_le _ _ (grayExactCylinder.{u}.le_anodyne _))

theorem isFibrant_iff_rlp_of_boxes (S : MorphismProperty DiagSet.{u})
    (hend : ∀ (ε : Bool) (U : Atom),
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.endpointBox ε (sphereInclusion U)))
    (hboth : ∀ {K X : DiagSet.{u}} (i : K ⟶ X), S i →
      MorphismProperty.saturation.{u} S (grayExactCylinder.{u}.bothBox i)) (X : DiagSet.{u}) :
    grayExactCylinder.{u}.IsFibrant S X ↔ S.rlp (terminal.from X) := by
  unfold HomotopicalAlgebra.ExactCylinder.IsFibrant
  rw [anodyne_eq_saturation_of_boxes S hend hboth, MorphismProperty.rlp_saturation]

private theorem bothBox_mem_saturation_hornInclusions {K X : DiagSet.{u}} (i : K ⟶ X)
    (hi : hornInclusions i) :
    MorphismProperty.saturation.{u} hornInclusions.{u} (grayExactCylinder.{u}.bothBox i) := by
  obtain ⟨H⟩ := hi
  exact bothBox_hornInclusion_mem_saturation H

theorem isAnodyneClass_saturation_hornInclusions :
    HomotopicalAlgebra.IsAnodyneClass grayExactCylinder.{u} hornInclusions
      (MorphismProperty.saturation.{u} hornInclusions.{u}) :=
  isAnodyneClass_saturation_of_boxes hornInclusions endpointBox_sphereInclusion_mem_saturation
    bothBox_mem_saturation_hornInclusions

theorem anodyne_hornInclusions :
    grayExactCylinder.{u}.anodyne hornInclusions =
      MorphismProperty.saturation.{u} hornInclusions.{u} :=
  anodyne_eq_saturation_of_boxes hornInclusions endpointBox_sphereInclusion_mem_saturation
    bothBox_mem_saturation_hornInclusions

theorem isFibrant_hornInclusions_iff (X : DiagSet.{u}) :
    grayExactCylinder.{u}.IsFibrant hornInclusions X ↔ IsHornFibrant X :=
  isFibrant_iff_rlp_of_boxes hornInclusions endpointBox_sphereInclusion_mem_saturation
    bothBox_mem_saturation_hornInclusions X

end Atoms.Diagrammatic

open CategoryTheory Limits HomotopicalAlgebra Atoms.Shape

namespace Atoms.Diagrammatic

abbrev hornWeak : MorphismProperty DiagSet.{u} :=
  grayExactCylinder.{u}.weakEquivalences hornInclusions

theorem isFibrant_modelCategory_hornInclusions_iff (X : DiagSet.{u}) :
    letI := grayExactCylinder.{u}.modelCategory hornInclusions hornInclusions_le_monomorphisms
    IsFibrant X ↔ IsHornFibrant X :=
  (HomotopicalAlgebra.ExactCylinder.modelCategory.isFibrant_iff _ _ _ X).trans
    (isFibrant_hornInclusions_iff X)

end Atoms.Diagrammatic

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

namespace Atoms.Diagrammatic

theorem saturation_hornInclusions_le_trivialCofibrations :
    MorphismProperty.saturation.{u} hornInclusions.{u} ≤
      MorphismProperty.monomorphisms DiagSet.{u} ⊓ hornWeak := by
  rw [← anodyne_hornInclusions]
  exact le_inf (grayExactCylinder.{u}.anodyne_le_monomorphisms _ hornInclusions_le_monomorphisms)
    (grayExactCylinder.{u}.anodyne_le_weakEquivalences _ hornInclusions_le_monomorphisms)

theorem rlp_trivialCofibrations_iff_rlp_hornInclusions {X Y : DiagSet.{u}} (p : X ⟶ Y)
    (hY : IsHornFibrant Y) :
    (MorphismProperty.monomorphisms DiagSet.{u} ⊓ hornWeak).rlp
        p ↔
      hornInclusions.rlp p := by
  refine ⟨fun h ↦ MorphismProperty.antitone_rlp
    ((MorphismProperty.le_saturation _).trans saturation_hornInclusions_le_trivialCofibrations) p h,
    fun h ↦ ?_⟩
  refine grayExactCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne hornInclusions
    hornInclusions_le_monomorphisms p ?_ ((isFibrant_hornInclusions_iff Y).2 hY)
  rw [HomotopicalAlgebra.ExactCylinder.naiveFibrations, anodyne_hornInclusions,
    MorphismProperty.rlp_saturation]
  exact h

end Atoms.Diagrammatic
