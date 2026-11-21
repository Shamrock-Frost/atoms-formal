import Atoms.Diagrammatic.Localization.WalkingEquivalence
import Atoms.Diagrammatic.Marked.Cylinder
import Atoms.Diagrammatic.Marked.Generators
import Atoms.Homotopical.Cylinder.ModelStructure

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

namespace MarkedDiagSet

def markedAbove (X : DiagSet.{u}) (n : ℕ) : MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking X
    { marked V := {x | IsDegenerate X x ∨ n < V.dimension}
      markable _ _ hx := hx.elim dimension_pos_of_isDegenerate (lt_of_le_of_lt (Nat.zero_le n))
      degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
      transport _ _ e x := or_congr (isDegenerate_map_iso_iff e x).symm
        (Iff.of_eq (congrArg (n < ·) (Atom.dimension_eq_of_iso e).symm)) }

noncomputable def markedAboveMap (X : DiagSet.{u}) {m n : ℕ} (h : m ≤ n) :
    markedAbove X n ⟶ markedAbove X m :=
  MarkedPresheaf.homMk (X := markedAbove X n) (Y := markedAbove X m) (𝟙 X) fun V _ hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx).imp_right (lt_of_le_of_lt h))

noncomputable def markedWalkingEquivalence (U : Atom) (hU : 0 < U.dimension) :
    MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking (walkingEquivalence U hU)
    { marked V := {x | IsDegenerate _ x ∨
        ∃ g : V ⟶ U, IsIso g ∧ x = (toWalkingEquivalence U hU).app (op V) ⟨g⟩}
      markable _ _ hx := by
        rcases hx with hx | ⟨g, hg, -⟩
        · exact dimension_pos_of_isDegenerate hx
        · exact (congrArg (0 < ·) (Atom.dimension_eq_of_iso (asIso g))).mpr hU
      degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
      transport V W e x := by
        refine or_congr (isDegenerate_map_iso_iff e x).symm ⟨?_, ?_⟩
        · rintro ⟨g, hg, rfl⟩
          exact ⟨e.hom ≫ g, inferInstance,
            (NatTrans.naturality_apply (toWalkingEquivalence U hU) e.hom.op ⟨g⟩).symm⟩
        · rintro ⟨g, hg, hx⟩
          refine ⟨e.inv ≫ g, inferInstance, ?_⟩
          refine Eq.trans ?_
            (NatTrans.naturality_apply (toWalkingEquivalence U hU) e.inv.op ⟨g⟩).symm
          rw [← hx, ← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id,
            Functor.map_id_apply] }

noncomputable def flatToMarkedWalkingEquivalence (U : Atom) (hU : 0 < U.dimension) :
    (MarkedPresheaf.flat atomMarking).obj (walkingEquivalence.{u} U hU) ⟶
      markedWalkingEquivalence U hU :=
  MarkedPresheaf.homMk (𝟙 (walkingEquivalence U hU)) fun V _ hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inl ((mem_marked_flat_iff_isDegenerate _ V _).1 hx))

end MarkedDiagSet

def localizationGenerators : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : Atom // 0 < U.dimension} =>
    MarkedDiagSet.flatToMarkedWalkingEquivalence U.1 U.2

def invertorGenerators : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : Atom // 0 < U.dimension} =>
    MarkedDiagSet.markedAboveMap (invertorPair U.1 U.2) (Nat.sub_le U.1.dimension 1)

def coinductiveGenerators (n : ℕ∞) : MorphismProperty MarkedDiagSet.{u} :=
  markedHorns ⊔ markingGeneratorsAbove n ⊔ localizationGenerators

def inductiveGenerators (n : ℕ∞) : MorphismProperty MarkedDiagSet.{u} :=
  markedHorns ⊔ markingGeneratorsAbove n ⊔ invertorGenerators

instance isSmall_coinductiveGenerators (n : ℕ∞) : (coinductiveGenerators.{u} n).IsSmall.{u} :=
  haveI : markedHorns.IsSmall.{u} := isSmall_ofHoms _
  haveI : (markingGeneratorsAbove n).IsSmall.{u} := isSmall_ofHoms _
  haveI : localizationGenerators.IsSmall.{u} := isSmall_ofHoms _
  inferInstanceAs (markedHorns ⊔ markingGeneratorsAbove n ⊔ localizationGenerators).IsSmall

instance isSmall_inductiveGenerators (n : ℕ∞) : (inductiveGenerators.{u} n).IsSmall.{u} :=
  haveI : markedHorns.IsSmall.{u} := isSmall_ofHoms _
  haveI : (markingGeneratorsAbove n).IsSmall.{u} := isSmall_ofHoms _
  haveI : invertorGenerators.IsSmall.{u} := isSmall_ofHoms _
  inferInstanceAs (markedHorns ⊔ markingGeneratorsAbove n ⊔ invertorGenerators).IsSmall

theorem markedHorns_le_monomorphisms : markedHorns ≤ monomorphisms MarkedDiagSet.{u} := by
  rw [markedHorns, ofHoms_le_iff]
  intro h
  refine (MarkedPresheaf.mono_iff _).2 ?_
  refine ((monomorphisms DiagSet.{u}).arrow_mk_iso_iff h.forgetArrowIso).2 ?_
  exact hornInclusions_le_monomorphisms _ (ofHoms.mk h.toHornData)

theorem markingGeneratorsAbove_le_monomorphisms (n : ℕ∞) :
    markingGeneratorsAbove n ≤ monomorphisms MarkedDiagSet.{u} := by
  rw [markingGeneratorsAbove, ofHoms_le_iff]
  exact fun U => (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 _)))

theorem coinductiveGenerators_le_monomorphisms (n : ℕ∞) :
    coinductiveGenerators n ≤ monomorphisms MarkedDiagSet.{u} :=
  sup_le (sup_le markedHorns_le_monomorphisms (markingGeneratorsAbove_le_monomorphisms n))
    ((ofHoms_le_iff _ _).2 fun _ => (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 _))))

theorem inductiveGenerators_le_monomorphisms (n : ℕ∞) :
    inductiveGenerators n ≤ monomorphisms MarkedDiagSet.{u} :=
  sup_le (sup_le markedHorns_le_monomorphisms (markingGeneratorsAbove_le_monomorphisms n))
    ((ofHoms_le_iff _ _).2 fun _ => (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 _))))

@[instance_reducible]
noncomputable def coinductiveModelCategory (n : ℕ∞) : ModelCategory MarkedDiagSet.{u} :=
  markedExactCylinder.modelCategoryOfEmbedding
    (BoundedEmbedding.separated (MarkedSite.topology atomMarking)) (coinductiveGenerators n)
    (coinductiveGenerators_le_monomorphisms n)

@[instance_reducible]
noncomputable def inductiveModelCategory (n : ℕ∞) : ModelCategory MarkedDiagSet.{u} :=
  markedExactCylinder.modelCategoryOfEmbedding
    (BoundedEmbedding.separated (MarkedSite.topology atomMarking)) (inductiveGenerators n)
    (inductiveGenerators_le_monomorphisms n)

def MarkedDiagSet.Coinductive (_ : ℕ∞) : Type (u + 1) := MarkedDiagSet.{u}

def MarkedDiagSet.Inductive (_ : ℕ∞) : Type (u + 1) := MarkedDiagSet.{u}

namespace MarkedDiagSet.Coinductive

instance category (n : ℕ∞) : Category.{u} (MarkedDiagSet.Coinductive.{u} n) :=
  inferInstanceAs (Category MarkedDiagSet.{u})

noncomputable instance modelCategory (n : ℕ∞) :
    ModelCategory (MarkedDiagSet.Coinductive.{u} n) :=
  coinductiveModelCategory n

instance isCofibrant (n : ℕ∞) (X : MarkedDiagSet.Coinductive.{u} n) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  let X' : MarkedDiagSet.{u} := X
  exact MorphismProperty.monomorphisms.infer_property (initial.to X')

end MarkedDiagSet.Coinductive

namespace MarkedDiagSet.Inductive

instance category (n : ℕ∞) : Category.{u} (MarkedDiagSet.Inductive.{u} n) :=
  inferInstanceAs (Category MarkedDiagSet.{u})

noncomputable instance modelCategory (n : ℕ∞) : ModelCategory (MarkedDiagSet.Inductive.{u} n) :=
  inductiveModelCategory n

end MarkedDiagSet.Inductive

def MarkedDiagSet.toCoinductive (n : ℕ∞) : MarkedDiagSet.{u} ⥤ MarkedDiagSet.Coinductive n :=
  𝟭 MarkedDiagSet.{u}

def MarkedDiagSet.toInductive (n : ℕ∞) : MarkedDiagSet.{u} ⥤ MarkedDiagSet.Inductive n :=
  𝟭 MarkedDiagSet.{u}

end Atoms.Diagrammatic
