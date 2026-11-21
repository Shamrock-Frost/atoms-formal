import Atoms.Diagrammatic.InftyCategory
import Atoms.Diagrammatic.Localization.ReversibleCylinder
import Atoms.Diagrammatic.Localization.WalkingEquivalence
import Atoms.Diagrammatic.Marked.Lifting
import Atoms.Homotopical.Cylinder.ModelStructure

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def compositorGenerators : MorphismProperty DiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : RoundShape // 0 < U.dimension} =>
    toMergerInclusion U.1 U.2 ≫
      toWalkingEquivalence (toMergerAtom U.1 U.2) (pos_dimension_toMergerAtom U.1 U.2)

def walkingEquivalenceGenerators (n : ℕ∞) : MorphismProperty DiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : Atom // n < U.dimension} =>
    toWalkingEquivalence U.1 (Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) U.2))

def inftyGenerators (n : ℕ∞) : MorphismProperty DiagSet.{u} :=
  compositorGenerators ⊔ walkingEquivalenceGenerators n

instance isSmall_inftyGenerators (n : ℕ∞) : (inftyGenerators.{u} n).IsSmall.{u} :=
  haveI : compositorGenerators.IsSmall.{u} := isSmall_ofHoms _
  haveI : (walkingEquivalenceGenerators n).IsSmall.{u} := isSmall_ofHoms _
  inferInstanceAs (compositorGenerators ⊔ walkingEquivalenceGenerators n).IsSmall

theorem inftyGenerators_le_monomorphisms (n : ℕ∞) :
    inftyGenerators n ≤ monomorphisms DiagSet.{u} := by
  refine sup_le ((ofHoms_le_iff _ _).2 fun U => ?_) ((ofHoms_le_iff _ _).2 fun U => ?_)
  · have : Mono (toMergerInclusion U.1 U.2) :=
      haveI := mono_realize_map (RDCpx.ofInclusion (P := U.1.rdc)
        (Q := atomToRDCpx.obj (toMergerAtom U.1 U.2)) (toMergerInputIncl U.1 U.2))
        (IsInclusion.injective (f := toMergerInputIncl U.1 U.2))
      mono_comp _ _
    have : Mono (toWalkingEquivalence (toMergerAtom U.1 U.2)
        (pos_dimension_toMergerAtom U.1 U.2)) :=
      inferInstanceAs (Mono (topInversionData _ _).toLocalization)
    exact monomorphisms.infer_property _
  · exact inferInstanceAs (Mono (topInversionData _ _).toLocalization)

@[instance_reducible]
noncomputable def inftyModelCategory (n : ℕ∞) : ModelCategory DiagSet.{u} :=
  reversibleCylinder.modelCategory (inftyGenerators n) (inftyGenerators_le_monomorphisms n)

def DiagSet.Infty (_ : ℕ∞) : Type (u + 1) := DiagSet.{u}

namespace DiagSet.Infty

instance category (n : ℕ∞) : Category.{u} (DiagSet.Infty.{u} n) :=
  inferInstanceAs (Category DiagSet.{u})

noncomputable instance modelCategory (n : ℕ∞) : ModelCategory (DiagSet.Infty.{u} n) :=
  inftyModelCategory n

instance isCofibrant (n : ℕ∞) (X : DiagSet.Infty.{u} n) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  let X' : DiagSet.{u} := X
  exact MorphismProperty.monomorphisms.infer_property (initial.to X')

end DiagSet.Infty

def DiagSet.toInfty (n : ℕ∞) : DiagSet.{u} ⥤ DiagSet.Infty n := 𝟭 DiagSet.{u}

private theorem rlp_ofHoms_terminal_from_iff {ι : Type*} {A B : ι → DiagSet.{u}}
    (f : ∀ i, A i ⟶ B i) (X : DiagSet.{u}) :
    (ofHoms f).rlp (terminal.from X) ↔ ∀ i (q : A i ⟶ X), ∃ g : B i ⟶ X, f i ≫ g = q := by
  constructor
  · intro h i q
    have := h (f i) (ofHoms.mk i)
    have sq : CommSq q (f i) (terminal.from X) (terminal.from (B i)) := ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · rintro h _ _ _ ⟨i⟩
    refine ⟨fun {u _} _ => ?_⟩
    obtain ⟨g, hg⟩ := h i u
    exact CommSq.HasLift.mk' ⟨g, hg, terminal.hom_ext _ _⟩

theorem hasWeakComposites_iff_rlp_compositorGenerators (X : DiagSet.{u}) :
    HasWeakComposites X ↔ compositorGenerators.rlp (terminal.from X) := by
  rw [compositorGenerators, rlp_ofHoms_terminal_from_iff]
  constructor
  · intro hX U q
    obtain ⟨z, hz, hin⟩ := exists_mem_marked_toMergerInclusion_comp_eq
      (MarkedDiagSet.natural.obj X) (hasMarkedRLP_markedHorns_natural_of_hasWeakComposites hX)
      U.1 U.2 q
    obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff _ _ hX z).2
      ((MarkedDiagSet.mem_marked_natural_iff X _ z).1 hz)
    exact ⟨g, (Category.assoc _ _ _).trans
      ((congrArg (toMergerInclusion U.1 U.2 ≫ ·) hg).trans hin)⟩
  · intro h
    refine (hasWeakComposites_iff_positive X).2 fun u hu => ?_
    obtain ⟨g, hg⟩ := h ⟨u.roundShape, hu⟩ u.map
    let w := toWalkingEquivalence (toMergerAtom u.roundShape hu)
      (pos_dimension_toMergerAtom u.roundShape hu) ≫ g
    exact exists_weakComposite_of_isEquivalence u hu (uliftYonedaEquiv w)
      ((topInversionData _ _).isEquivalence_of_toLocalization_comp_eq g ⟨⟩)
      ((congrArg (toMergerInclusion u.roundShape hu ≫ ·)
        (uliftYonedaEquiv.symm_apply_apply w)).trans
        ((Category.assoc _ _ _).symm.trans hg))

theorem rlp_walkingEquivalenceGenerators_iff (n : ℕ∞) {X : DiagSet.{u}} (hX : HasWeakComposites X) :
    (walkingEquivalenceGenerators n).rlp (terminal.from X) ↔
      ∀ (U : Atom) (x : diagram X U), n < U.dimension → IsEquivalence X x := by
  rw [walkingEquivalenceGenerators, rlp_ofHoms_terminal_from_iff]
  constructor
  · intro h U x hn
    exact (exists_toWalkingEquivalence_comp_eq_iff _ _ hX x).1 (h ⟨U, hn⟩ (uliftYonedaEquiv.symm x))
  · intro h U q
    obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff U.1
      (Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) U.2)) hX (uliftYonedaEquiv q)).2
      (h U.1 (uliftYonedaEquiv q) U.2)
    exact ⟨g, hg.trans (uliftYonedaEquiv.symm_apply_apply q)⟩

theorem isInftyCategory_iff_rlp (n : ℕ∞) (X : DiagSet.{u}) :
    IsInftyCategory n X ↔ (inftyGenerators n).rlp (terminal.from X) := by
  have e : (compositorGenerators ⊔ walkingEquivalenceGenerators n).rlp =
      compositorGenerators.rlp ⊓ (walkingEquivalenceGenerators n).rlp :=
    MorphismProperty.gc_llp_rlp.u_inf
  rw [inftyGenerators, e]
  refine ⟨fun hX => ⟨(hasWeakComposites_iff_rlp_compositorGenerators X).1 hX.1,
    (rlp_walkingEquivalenceGenerators_iff n hX.1).2 hX.2⟩, fun h => ?_⟩
  have hW := (hasWeakComposites_iff_rlp_compositorGenerators X).2 h.1
  exact ⟨hW, (rlp_walkingEquivalenceGenerators_iff n hW).1 h.2⟩

theorem isInftyCategory_of_isFibrant (n : ℕ∞) (X : DiagSet.Infty.{u} n) (hX : IsFibrant X) :
    IsInftyCategory n X :=
  (isInftyCategory_iff_rlp n X).2 fun _ _ i hi =>
    (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators n)
      (inftyGenerators_le_monomorphisms n) X).1 hX i (reversibleCylinder.le_anodyne _ i hi)

theorem weakEquivalence_toInfty_map_of_rlp_monomorphisms (n : ℕ∞) {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (monomorphisms DiagSet.{u}).rlp g) : WeakEquivalence ((DiagSet.toInfty n).map g) := by
  have h : trivialFibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map g) := by
    rw [← cofibrations_rlp]
    exact hg
  exact (weakEquivalence_iff _).2 h.2

theorem weakEquivalence_toInfty_map_of_mem_inftyGenerators (n : ℕ∞) {A B : DiagSet.{u}}
    {f : A ⟶ B} (hf : inftyGenerators n f) : WeakEquivalence ((DiagSet.toInfty n).map f) :=
  (weakEquivalence_iff _).2 (reversibleCylinder.anodyne_le_weakEquivalences _
    (inftyGenerators_le_monomorphisms n) f (reversibleCylinder.le_anodyne _ f hf))

theorem rlp_monomorphisms_of_trivialFibration_toInfty_map (n : ℕ∞) {A B : DiagSet.{u}} {g : A ⟶ B}
    [Fibration ((DiagSet.toInfty n).map g)] [WeakEquivalence ((DiagSet.toInfty n).map g)] :
    (monomorphisms DiagSet.{u}).rlp g := by
  have h : trivialFibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map g) :=
    mem_trivialFibrations _
  rw [← cofibrations_rlp] at h
  exact h

end Atoms.Diagrammatic
