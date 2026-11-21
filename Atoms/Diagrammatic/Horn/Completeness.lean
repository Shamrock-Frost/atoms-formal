import Atoms.Diagrammatic.Horn.Localizer
import Atoms.TestCategory.Localizer.CylinderCompleteness

open CategoryTheory Limits Opposite Atoms Atoms.Homotopical HomotopicalAlgebra
open Atoms.Shape Atoms.TestCategory

universe u

namespace Atoms.Diagrammatic

private theorem saturation_hornInclusions_yoneda_map {U T : Atom} (f : U ⟶ T) (hf : Mono f) :
    MorphismProperty.saturation.{0} hornInclusions (yoneda.map f) :=
  ((MorphismProperty.saturation.{0} hornInclusions).arrow_mk_iso_iff
    (Arrow.isoMk (uliftYonedaIsoYoneda.{0}.app U) (uliftYonedaIsoYoneda.{0}.app T)
      (uliftYonedaIsoYoneda.{0}.hom.naturality f).symm)).1
    (yoneda_map_mem_saturation_hornInclusions f (isInclusionHom_of_mono f))

theorem atom_mono_sliceHom_anodyne {U T : Atom} (f : U ⟶ T) [Mono f]
    (X : DiagSet.{0}) (b : yoneda.obj T ⟶ X) :
    (grayExactCylinder.over X).anodyne (sliceGenerators hornInclusions X)
      (sliceHom (yoneda.map f) b) :=
  anodyne_sliceHom_yoneda_map _ _ anodyne_hornInclusions saturation_hornInclusions_yoneda_map f X b

theorem atomElements_yoneda_mono_anodyne (X : DiagSet.{0})
    {a b : CostructuredArrow yoneda X} (f : a ⟶ b) [Mono f] :
    (grayExactCylinder.over X).anodyne (sliceGenerators hornInclusions X) (yoneda.map f) :=
  anodyne_over_yoneda_map _ _ anodyne_hornInclusions saturation_hornInclusions_yoneda_map X f

theorem atomElements_yoneda_map_weak (X : DiagSet.{0})
    {a b : CostructuredArrow yoneda X} (f : a ⟶ b) :
    (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X)
      (yoneda.map f) :=
  weakEquivalences_over_yoneda_map _ _ hornInclusions_le_monomorphisms anodyne_hornInclusions
    saturation_hornInclusions_yoneda_map X f

theorem atom_yoneda_map_absolute {a b : Atom} (f : a ⟶ b) :
    grayExactCylinder.absoluteWeakEquivalences hornInclusions (yoneda.map f) :=
  absoluteWeakEquivalences_yoneda_map _ _ hornInclusions_le_monomorphisms anodyne_hornInclusions
    saturation_hornInclusions_yoneda_map hornWeak_eq_minimal_wPsh_atom f

end Atoms.Diagrammatic

open CategoryTheory Limits MorphismProperty

namespace Atoms.Diagrammatic

open Atoms.Homotopical

theorem hornComplete_tfae :
    List.TFAE
      [MorphismProperty.monomorphisms DiagSet.{0} ⊓
            hornWeak =
          saturation.{0} hornInclusions,
        (MorphismProperty.monomorphisms DiagSet.{0} ⊓
          hornWeak).rlp = hornInclusions.rlp,
        ∀ ⦃X Y : DiagSet.{0}⦄ (p : X ⟶ Y),
          hornInclusions.rlp p → hornWeak p →
            (MorphismProperty.monomorphisms DiagSet.{0}).rlp p,
        grayExactCylinder.{0}.IsComplete hornInclusions,
        ∀ X : DiagSet.{0},
          (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X) =
            hornWeak.inverseImage (sliceForget X)] := by
  have hH := hornInclusions_le_monomorphisms
  have hrlp : (grayExactCylinder.anodyne hornInclusions).rlp = hornInclusions.rlp := by
    rw [anodyne_hornInclusions, rlp_saturation]
  have hle : hornInclusions ≤
      MorphismProperty.monomorphisms DiagSet.{0} ⊓ hornWeak :=
    (le_saturation.{0} _).trans saturation_hornInclusions_le_trivialCofibrations
  have h₁ := grayExactCylinder.isComplete_tfae hornInclusions hH
  have h₂ := grayExactCylinder.isComplete_tfae_absolute hornInclusions hH
  tfae_have 1 ↔ 4 := by
    unfold ExactCylinder.IsComplete
    rw [anodyne_hornInclusions]
    exact ⟨le_of_eq, fun h ↦ le_antisymm h saturation_hornInclusions_le_trivialCofibrations⟩
  tfae_have 2 ↔ 4 := by
    refine Iff.trans ?_ (h₁.out 1 0)
    rw [HomotopicalAlgebra.ExactCylinder.naiveFibrations, hrlp]
    exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm (antitone_rlp hle) h⟩
  tfae_have 3 ↔ 4 := by
    refine Iff.trans ?_ (h₁.out 2 0)
    rw [HomotopicalAlgebra.ExactCylinder.naiveFibrations, hrlp]
    exact ⟨fun h _ _ p hp ↦ h p hp.1 hp.2, fun h _ _ p hp hW ↦ h p ⟨hp, hW⟩⟩
  tfae_have 5 ↔ 4 := by
    refine Iff.trans ?_ (h₂.out 1 0)
    refine forall_congr' fun X ↦ ?_
    rw [grayExactCylinder.weakEquivalences_over_eq_of_eq_saturation hornInclusions
      hornInclusions hH anodyne_hornInclusions X]
  tfae_finish

end Atoms.Diagrammatic

open CategoryTheory Limits Opposite Atoms Atoms.TestCategory Atoms.Homotopical
open Atoms.Shape MorphismProperty

namespace Atoms.Diagrammatic

theorem hornWeak_over_eq_minimal_atomElements (X : DiagSet.{0}) :
    (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X) =
      minimalBasicLocalizer.wPsh (CostructuredArrow yoneda X) :=
  weakEquivalences_over_eq_minimal _ _ hornInclusions_le_monomorphisms anodyne_hornInclusions
    saturation_hornInclusions_yoneda_map hornWeak_eq_minimal_wPsh_atom X

theorem hornWeak_over_le_minimal_atomElements (X : DiagSet.{0}) :
    (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X) ≤
      minimalBasicLocalizer.wPsh (CostructuredArrow yoneda X) :=
  (hornWeak_over_eq_minimal_atomElements X).le

theorem minimal_atomElements_le_hornWeak_over (X : DiagSet.{0}) :
    minimalBasicLocalizer.wPsh (CostructuredArrow yoneda X) ≤
      (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X) :=
  (hornWeak_over_eq_minimal_atomElements X).ge

theorem hornWeak_over_eq_underlying (X : DiagSet.{0}) :
    (grayExactCylinder.over X).weakEquivalences (sliceGenerators hornInclusions X) =
      hornWeak.inverseImage (sliceForget X) :=
  weakEquivalences_over_eq_underlying _ _ hornInclusions_le_monomorphisms anodyne_hornInclusions
    saturation_hornInclusions_yoneda_map hornWeak_eq_minimal_wPsh_atom X

theorem hornWeak_eq_absolute :
    hornWeak =
      grayExactCylinder.absoluteWeakEquivalences hornInclusions := by
  have hH := hornInclusions_le_monomorphisms
  have hC : grayExactCylinder.{0}.IsComplete hornInclusions :=
    (hornComplete_tfae.out 4 3).1 hornWeak_over_eq_underlying
  exact le_antisymm ((grayExactCylinder.isComplete_tfae_absolute hornInclusions hH).out 0 2 |>.1 hC)
    (grayExactCylinder.absoluteWeakEquivalences_le_weakEquivalences hornInclusions hH)

end Atoms.Diagrammatic

open CategoryTheory Limits Opposite Atoms Atoms.TestCategory Atoms.Homotopical
open Atoms.Shape MorphismProperty

namespace Atoms.Diagrammatic

abbrev smallHornInclusions : MorphismProperty ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u) :=
  functorImage DiagSet.asSmallEquivalence.functor hornInclusions.{u}

theorem smallHornInclusions_le_monomorphisms :
    smallHornInclusions.{u} ≤ MorphismProperty.monomorphisms _ := by
  rintro _ _ _ ⟨K, L, t, ht, h⟩
  have : Mono t := hornInclusions_le_monomorphisms t ht
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (eqToIso h)).1
    (DiagSet.asSmallEquivalence.functor.map_mono t)

private theorem saturation_smallHornInclusions_map_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    saturation.{u} smallHornInclusions.{u} (DiagSet.asSmallEquivalence.functor.map f) ↔
      saturation.{u} hornInclusions.{u} f := by
  have h := inverseImage_saturation_functor.{u} DiagSet.asSmallEquivalence.symm hornInclusions.{u}
  simp only [Equivalence.symm_inverse] at h
  rw [← h]
  exact map_functor_map_inverse_iff DiagSet.asSmallEquivalence.symm _ f

theorem anodyne_smallGrayCylinder :
    smallGrayCylinder.{u}.anodyne smallHornInclusions.{u} =
      saturation.{u} smallHornInclusions.{u} := by
  let e := DiagSet.asSmallEquivalence.{u}
  refine le_antisymm (fun X Y f hf ↦ ?_)
    (saturation_le _ _ (smallGrayCylinder.{u}.le_anodyne smallHornInclusions.{u}))
  let i : Arrow.mk (e.functor.map (e.inverse.map f)) ≅ Arrow.mk f :=
    ((Functor.mapArrowFunctor _ _).mapIso e.counitIso).app (Arrow.mk f)
  rw [← (saturation.{u} smallHornInclusions.{u}).arrow_mk_iso_iff i,
    saturation_smallHornInclusions_map_iff, ← anodyne_hornInclusions,
    ← ExactCylinder.anodyne_transport_map_iff grayExactCylinder.{u} DiagSet.asSmallEquivalence
      hornInclusions.{u}]
  exact ((smallGrayCylinder.{u}.anodyne smallHornInclusions.{u}).arrow_mk_iso_iff i).2 hf

theorem saturation_smallHornInclusions_yoneda_map {a b : AsSmall.{u} Atom} (f : a ⟶ b)
    (hf : Mono f) : saturation.{u} smallHornInclusions.{u} (yoneda.map f) := by
  have : Mono (AsSmall.down.map f) := inferInstance
  have h := yoneda_map_mem_saturation_hornInclusions.{u} (AsSmall.down.map f)
    (isInclusionHom_of_mono _)
  rw [← saturation_smallHornInclusions_map_iff] at h
  exact ((saturation.{u} smallHornInclusions.{u}).arrow_mk_iso_iff
    (Arrow.isoMk (DiagSet.asSmallBallIso (AsSmall.down.obj a))
      (DiagSet.asSmallBallIso (AsSmall.down.obj b)) rfl)).1 h

private theorem smallHornInclusions_le_minimal :
    smallHornInclusions.{u} ≤ minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom) := by
  rintro _ _ _ ⟨K, L, t, ht, h⟩
  exact ((minimalBasicLocalizer.wPsh _).arrow_mk_iso_iff (eqToIso h)).1
    ((minimalBasicLocalizer.wDiagSet_iff t).1
      (minimalBasicLocalizer.hornInclusions_le_wDiagSet t ht))

theorem weakEquivalences_smallGrayCylinder :
    smallGrayCylinder.{u}.weakEquivalences smallHornInclusions.{u} =
      minimalBasicLocalizer.{u}.wPsh (AsSmall.{u} Atom) := by
  refine le_antisymm (ExactCylinder.weakEquivalences_le_of_endpoint_mem.{u, u}
    smallGrayCylinder.{u} smallHornInclusions.{u} smallHornInclusions_le_monomorphisms
    smallHornInclusions_le_minimal fun ε X ↦
      (IsALocalizer.endpoint_mem_iff_contraction_mem.{u, u} smallGrayCylinder.{u} ε X).2
        (minimalBasicLocalizer.cylinderCompatibleWith_smallGrayCylinder X)) ?_
  have := smallGrayCylinder.{u}.isALocalizer_weakEquivalences smallHornInclusions.{u}
    smallHornInclusions_le_monomorphisms
  rw [minimal_wPsh_eq_generatedALocalizer (AsSmall.{u} Atom)]
  refine generatedALocalizer_le ?_
  rintro _ _ _ ⟨a⟩
  obtain ⟨i, hi⟩ := exists_inclusion_atomPoint (AsSmall.down.obj a)
  let W := smallGrayCylinder.{u}.weakEquivalences smallHornInclusions.{u}
  let pt : AsSmall.{u} Atom := AsSmall.up.obj atomPoint
  have hT : IsTerminal (yoneda.obj pt) :=
    (isTerminalBallAtomPoint.{u}.isTerminalObj DiagSet.asSmall _).ofIso
      (DiagSet.asSmallBallIso atomPoint)
  have hm : Mono (AsSmall.up.map i : pt ⟶ a) :=
    have := mono_of_isInclusionHom i hi
    have h : Mono ((AsSmall.up : Atom ⥤ AsSmall.{u} Atom).map i) := inferInstance
    h
  have hwi : W (yoneda.map (AsSmall.up.map i : pt ⟶ a)) :=
    smallGrayCylinder.{u}.anodyne_le_weakEquivalences _ smallHornInclusions_le_monomorphisms _
      (anodyne_smallGrayCylinder ▸ saturation_smallHornInclusions_yoneda_map _ hm)
  have hiso : W (yoneda.map (AsSmall.up.map i : pt ⟶ a) ≫ terminal.from (yoneda.obj a)) := by
    rw [show yoneda.map (AsSmall.up.map i : pt ⟶ a) ≫ terminal.from (yoneda.obj a) =
      terminal.from (yoneda.obj pt) from terminal.hom_ext _ _]
    exact smallGrayCylinder.{u}.isomorphisms_le_weakEquivalences _ _
      (isIso_of_isTerminal hT terminalIsTerminal _)
  exact MorphismProperty.of_precomp W _ _ hwi hiso

theorem monomorphisms_inf_hornWeak_eq_saturation_hornInclusions :
    MorphismProperty.monomorphisms DiagSet.{u} ⊓ hornWeak.{u} =
      saturation.{u} hornInclusions.{u} := by
  let e := DiagSet.asSmallEquivalence.{u}
  refine le_antisymm (fun X Y f hf ↦ ?_) saturation_hornInclusions_le_trivialCofibrations
  have hc := isComplete_of_saturation_yoneda_map smallGrayCylinder.{u} smallHornInclusions.{u}
    smallHornInclusions_le_monomorphisms anodyne_smallGrayCylinder
    (fun f hf ↦ saturation_smallHornInclusions_yoneda_map f hf) weakEquivalences_smallGrayCylinder
  have hm : Mono f := hf.1
  have hw : smallGrayCylinder.{u}.weakEquivalences smallHornInclusions.{u} (e.functor.map f) := by
    rw [weakEquivalences_smallGrayCylinder]
    exact (minimalBasicLocalizer.wDiagSet_iff f).1 (hornWeak_eq_minimal_wDiagSet ▸ hf.2)
  rw [← anodyne_hornInclusions, ← ExactCylinder.anodyne_transport_map_iff grayExactCylinder.{u}
    DiagSet.asSmallEquivalence hornInclusions.{u}]
  exact hc _ ⟨e.functor.map_mono f, hw⟩

theorem rlp_monomorphisms_inf_hornWeak_eq_rlp_hornInclusions :
    (MorphismProperty.monomorphisms DiagSet.{u} ⊓
      hornWeak.{u}).rlp = hornInclusions.{u}.rlp := by
  rw [monomorphisms_inf_hornWeak_eq_saturation_hornInclusions, MorphismProperty.rlp_saturation]

theorem rlp_monomorphisms_of_rlp_hornInclusions_of_hornWeak ⦃X Y : DiagSet.{u}⦄ (p : X ⟶ Y)
    (hp : hornInclusions.rlp p) (hw : hornWeak p) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp p := by
  rw [isAccessibleALocalizer_hornWeak.isWeakFactorizationSystem_monomorphisms.rlp,
    rlp_monomorphisms_inf_hornWeak_eq_rlp_hornInclusions]
  exact ⟨hp, hw⟩

end Atoms.Diagrammatic
