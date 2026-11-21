import Atoms.Diagrammatic.Horn.Completeness

open CategoryTheory Limits Opposite Atoms Atoms.TestCategory Atoms.Homotopical HomotopicalAlgebra
open Atoms.Shape MorphismProperty

universe u

namespace Atoms.Diagrammatic

def infinityEquivalences : MorphismProperty DiagSet.{u} :=
  fun _ _ f ↦ kanWeak
    (CategoryTheory.nerveFunctor.map ((Functor.elementsFunctor ⋙ Cat.opFunctor).map f))

theorem infinityEquivalences_eq_kan_wDiagSet :
    infinityEquivalences.{u} = kanBasicLocalizer.{u}.wDiagSet := by
  ext X Y f
  rw [BasicLocalizer.wDiagSet_iff]
  let e : Arrow.mk (CategoryTheory.nerveFunctor.map
        ((elementsFunctor (AsSmall.{u} Atom)).map (DiagSet.asSmall.map f))) ≅
      Arrow.mk (CategoryTheory.nerveFunctor.map
        ((Functor.elementsFunctor ⋙ Cat.opFunctor).map f)) :=
    Arrow.isoMk (CategoryOfElements.nerveAsSmallIso X) (CategoryOfElements.nerveAsSmallIso Y) rfl
  exact ((kanBasicLocalizer_W_iff _).trans (kanWeak.arrow_mk_iso_iff e)).symm

theorem infinityEquivalences_eq_kan_wPsh :
    infinityEquivalences = kanBasicLocalizer.wPsh Atom :=
  kanBasicLocalizer.wDiagSet_eq_wPsh ▸ infinityEquivalences_eq_kan_wDiagSet

theorem yoneda_map_mem_infinityEquivalences {a b : Atom} (f : a ⟶ b) :
    infinityEquivalences (uliftYoneda.{u}.map f) := by
  rw [infinityEquivalences_eq_kan_wDiagSet]
  exact kanBasicLocalizer.wDiagSet_uliftYoneda_map f

theorem minimal_wDiagSet_eq_infinityEquivalences :
    minimalBasicLocalizer.{u}.wDiagSet = infinityEquivalences.{u} := by
  rw [minimalBasicLocalizer_eq_kanBasicLocalizer, infinityEquivalences_eq_kan_wDiagSet]

theorem minimal_wPsh_atom_eq_infinityEquivalences :
    minimalBasicLocalizer.wPsh Atom = infinityEquivalences :=
  minimalBasicLocalizer.wDiagSet_eq_wPsh ▸ minimal_wDiagSet_eq_infinityEquivalences

theorem hornWeak_eq_infinityEquivalences :
    hornWeak.{u} = infinityEquivalences.{u} := by
  rw [hornWeak_eq_minimal_wDiagSet, minimal_wDiagSet_eq_infinityEquivalences]

private theorem isWeakFactorizationSystem_trivialCofibrations_infinityEquivalences :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms DiagSet.{u} ⊓ infinityEquivalences)
      hornInclusions.rlp := by
  rw [← hornWeak_eq_infinityEquivalences, ← rlp_monomorphisms_inf_hornWeak_eq_rlp_hornInclusions]
  exact isAccessibleALocalizer_hornWeak.isWeakFactorizationSystem_trivialCofibrations

private theorem isWeakFactorizationSystem_monomorphisms_infinityEquivalences :
    IsWeakFactorizationSystem (MorphismProperty.monomorphisms DiagSet.{u})
      (hornInclusions.rlp ⊓ infinityEquivalences) := by
  rw [← hornWeak_eq_infinityEquivalences, ← rlp_monomorphisms_inf_hornWeak_eq_rlp_hornInclusions]
  exact isAccessibleALocalizer_hornWeak.isWeakFactorizationSystem_monomorphisms

namespace DiagSet.modelCategoryCisinski

open HomotopicalAlgebra

scoped instance cisinskiCofibrations : CategoryWithCofibrations DiagSet.{u} where
  cofibrations := MorphismProperty.monomorphisms DiagSet.{u}

scoped instance cisinskiWeakEquivalences : CategoryWithWeakEquivalences DiagSet.{u} where
  weakEquivalences := infinityEquivalences

scoped instance cisinskiFibrations : CategoryWithFibrations DiagSet.{u} where
  fibrations := hornInclusions.rlp

theorem cofibrations_eq :
    cofibrations DiagSet.{u} = MorphismProperty.monomorphisms DiagSet.{u} := rfl

theorem weakEquivalences_eq : weakEquivalences DiagSet.{u} = infinityEquivalences := rfl

theorem fibrations_eq : fibrations DiagSet.{u} = hornInclusions.rlp := rfl

scoped instance cisinskiModelCategory : ModelCategory DiagSet.{u} :=
  have : (weakEquivalences DiagSet.{u}).HasTwoOutOfThreeProperty := by
    rw [weakEquivalences_eq, ← hornWeak_eq_infinityEquivalences]
    exact grayExactCylinder.{u}.weakEquivalences_hasTwoOutOfThreeProperty hornInclusions
  have : IsWeakFactorizationSystem (cofibrations DiagSet.{u}) (trivialFibrations DiagSet.{u}) :=
    isWeakFactorizationSystem_monomorphisms_infinityEquivalences
  have : IsWeakFactorizationSystem (trivialCofibrations DiagSet.{u}) (fibrations DiagSet.{u}) :=
    isWeakFactorizationSystem_trivialCofibrations_infinityEquivalences
  ModelCategory.mk' DiagSet.{u}

scoped instance isCofibrant (X : DiagSet.{u}) : IsCofibrant X :=
  (isCofibrant_iff X).2
    ((cofibration_iff _).2 (MorphismProperty.monomorphisms.infer_property (initial.to X)))

theorem isFibrant_iff (X : DiagSet.{u}) : IsFibrant X ↔ IsHornFibrant X :=
  fibration_iff _

end DiagSet.modelCategoryCisinski

end Atoms.Diagrammatic
