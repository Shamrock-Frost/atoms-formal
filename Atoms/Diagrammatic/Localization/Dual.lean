import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.Diagrammatic.Marked.FlatEquivalence
import Atoms.Diagrammatic.Equivalence.Dual
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Uniqueness
import Mathlib.AlgebraicTopology.ModelCategory.Transport
import Mathlib.Combinatorics.Quiver.ReflQuiver

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Atoms.Shape

universe u

namespace Atoms.Diagrammatic

section Dual

open Atoms.Molecule PastingDiagram

variable {X : DiagSet.{u}} (J : ℕ → Bool)

private noncomputable def dualCell {V : Atom} (c : diagram X V) :
    diagram ((DiagSet.dual J).obj X) (V.dual J) :=
  uliftYonedaEquiv ((realizeAtomIso (V.dual J)).inv ≫ ((PastingDiagram.ofCell c).dual J).map)

private theorem ofCell_dualCell {V : Atom} (c : diagram X V) :
    PastingDiagram.ofCell (dualCell J c) = (PastingDiagram.ofCell c).dual J := by
  change (⟨(V.dual J).toMoleculeShape, (PastingDiagram.ofCell (dualCell J c)).map⟩ :
    PastingDiagram _) = ⟨(PastingDiagram.ofCell c).shape.dual J, _⟩
  congr 1
  simp only [PastingDiagram.ofCell, dualCell, Equiv.symm_apply_apply]
  exact (realizeAtomIso (V.dual J)).hom_inv_id_assoc _

private theorem equivalent_dual {a b : RoundPastingDiagram X} (h : Equivalent a b) :
    Equivalent (a.dual J) (b.dual J) := by
  obtain ⟨hd, e, he, hde, hs, ht⟩ := h.data
  have ha : (a.dual J).dim = a.dim := dim_dual J a.toPastingDiagram
  have hb : (b.dual J).dim = b.dim := dim_dual J b.toPastingDiagram
  have hed : (e.dual J).dim = a.dim + 1 := (dim_dual J e.toPastingDiagram).trans hde
  have key (α : Bool) : ((e.dual J).boundary (a.dual J).dim α).Equiv
      ((e.boundary a.dim (xor (J (a.dim + 1)) α)).dual J) := by
    rw [ha]
    exact equiv_boundary_dual J e.toPastingDiagram a.dim α
  cases hJ : J (a.dim + 1)
  · refine EquivalenceData.equivalent ⟨ha.trans (hd.trans hb.symm), e.dual J,
      mem_equivalences_dual J he, hed.trans (congrArg (· + 1) ha.symm), ?_, ?_⟩
    · exact (key false).trans (by rw [hJ]; exact hs.dual J)
    · exact (key true).trans (by rw [hJ]; exact ht.dual J)
  · refine equivalent_symm (EquivalenceData.equivalent ⟨hb.trans (hd.symm.trans ha.symm),
      e.dual J, mem_equivalences_dual J he, ?_, ?_, ?_⟩)
    · rw [hed, hb, hd]
    · rw [hb, ← hd]
      exact (equiv_boundary_dual J e.toPastingDiagram a.dim false).trans
        (by rw [hJ]; exact ht.dual J)
    · rw [hb, ← hd]
      exact (equiv_boundary_dual J e.toPastingDiagram a.dim true).trans
        (by rw [hJ]; exact hs.dual J)

private theorem parallel_of_equivalent {a b : RoundPastingDiagram X} (h : Equivalent a b) :
    Parallel a b := by
  obtain ⟨hd, e, he, hde, hs, ht⟩ := h.data
  exact ((parallel_boundary e.isRound hde false true).of_equiv_left hs.symm).of_equiv_right
    ht.symm

private theorem exists_weakComposite_of_equivalent {u : RoundPastingDiagram X} (hu : 0 < u.dim)
    {V : Atom} {c : diagram X V} (h : Equivalent u (cellRound c)) :
    ∃ c' : diagram X (mergerAtom u.roundShape hu), Equivalent u (cellRound c') := by
  have hp := parallel_of_equivalent h
  have hd : u.dim = (u.dim - 1) + 1 := (Nat.sub_add_cancel hu).symm
  have hdV : V.toMoleculeShape.dimension = (u.dim - 1) + 1 := hp.1.symm.trans hd
  have hb (α : Bool) : (u.boundary (u.dim - 1) α).Equiv
      ((cellRound c).boundary (u.dim - 1) α) := by
    rcases hp.2 with h0 | hb
    · omega
    · exact (hb α).trans (by rw [← hp.1])
  obtain ⟨θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso
    (mergerAtom u.roundShape hu).toMoleculeShape V.toMoleculeShape (n := u.dim - 1)
    (fun α => mergerAtomBoundaryIso u.roundShape hu α ≪≫ (hb α).iso)
    (mergerAtom u.roundShape hu).isAtom V.isAtom ((dimension_mergerAtom u.roundShape hu).trans hd)
    hdV
  exact ⟨X.map (Atom.isoOfOGPIso θ).hom.op c, equivalent_trans h
    (equivalent_of_equiv (PastingDiagram.equiv_ofCell_map_iso (Atom.isoOfOGPIso θ) c).symm)⟩

theorem isInftyCategory_dual {n : ℕ∞} (hX : IsInftyCategory n X) :
    IsInftyCategory n ((DiagSet.dual J).obj X) := by
  refine ⟨(hasWeakComposites_iff_positive _).2 fun u hu => ?_, fun U x hx => ?_⟩
  · obtain ⟨c, hc⟩ := hX.1 ((u.dual J).mapTo (DiagSet.dualDualIso J X).hom)
    have h₁ := equivalent_dual J hc
    have h₂ : Equivalent u (cellRound (dualCell J c)) := by
      refine equivalent_trans (equivalent_of_equiv ?_) (equivalent_trans h₁
        (equivalent_of_equiv ?_))
      · exact (equiv_dual_mapTo_dual J u.toPastingDiagram).symm
      · change ((PastingDiagram.ofCell c).dual J).Equiv (PastingDiagram.ofCell (dualCell J c))
        rw [ofCell_dualCell]
    exact exists_weakComposite_of_equivalent hu h₂
  · have hd : (U.dual J).dimension = U.dimension := MoleculeShape.dimension_dual _ _
    have h₁ : IsEquivalence X ((DiagSet.dualDualIso J X).hom.app (op (U.dual J)) (dualCell J x)) :=
      hX.2 _ _ (by rw [hd]; exact hx)
    have h₂ : ((cellRound x).dual J).mapTo (DiagSet.dualDualIso J X).hom ∈ equivalences X := by
      refine mem_equivalences_of_equiv ?_ h₁
      change (PastingDiagram.ofCell
          ((DiagSet.dualDualIso J X).hom.app (op (U.dual J)) (dualCell J x))).Equiv
        ((PastingDiagram.ofCell x).dual J |>.mapTo (DiagSet.dualDualIso J X).hom)
      rw [PastingDiagram.ofCell_app, ofCell_dualCell]
    exact mem_equivalences_of_equiv (equiv_dual_mapTo_dual J _)
      (mem_equivalences_dual J h₂)

theorem isInftyCategory_dual_iff {n : ℕ∞} (X : DiagSet.{u}) :
    IsInftyCategory n ((DiagSet.dual J).obj X) ↔ IsInftyCategory n X :=
  ⟨fun h => isInftyCategory_of_iso (DiagSet.dualDualIso J X).symm (isInftyCategory_dual J h),
    isInftyCategory_dual J⟩

theorem mono_dual_map_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    Mono ((DiagSet.dual J).map f) ↔ Mono f :=
  ⟨fun _ => (DiagSet.dualEquivalence.{u} J).functor.mono_of_mono_map ‹_›,
    fun _ => (DiagSet.dualEquivalence.{u} J).functor.map_mono f⟩

end Dual

section Transport

variable (n : ℕ∞) (J : ℕ → Bool)

private def inftyDualEquivalence : DiagSet.Infty.{u} n ≌ DiagSet.Infty.{u} n :=
  DiagSet.dualEquivalence.{u} J

@[instance_reducible]
private noncomputable def inftyDualModelCategory : ModelCategory (DiagSet.Infty.{u} n) :=
  @ModelCategory.transport (DiagSet.Infty.{u} n) (DiagSet.Infty.{u} n) _ _ _
    ⟨(cofibrations (DiagSet.Infty.{u} n)).inverseImage (inftyDualEquivalence n J).functor⟩
    ⟨(fibrations (DiagSet.Infty.{u} n)).inverseImage (inftyDualEquivalence n J).functor⟩
    ⟨(weakEquivalences (DiagSet.Infty.{u} n)).inverseImage (inftyDualEquivalence n J).functor⟩
    (inftyDualEquivalence n J) rfl rfl rfl

private theorem fibrations_inftyDualModelCategory :
    (letI := inftyDualModelCategory.{u} n J; fibrations (DiagSet.Infty.{u} n)) =
      (fibrations (DiagSet.Infty.{u} n)).inverseImage (inftyDualEquivalence n J).functor :=
  rfl

private theorem weakEquivalences_infty_dual :
    weakEquivalences (DiagSet.Infty.{u} n) =
      (weakEquivalences (DiagSet.Infty.{u} n)).inverseImage (inftyDualEquivalence n J).functor :=
  ModelCategory.weakEquivalences_eq_of_cofibrations_eq_of_isFibrant_iff
    (DiagSet.Infty.modelCategory n) (inftyDualModelCategory n J) (by
      ext X Y f
      exact (mono_dual_map_iff J f).symm) fun X => by
    have hT : IsTerminal ((inftyDualEquivalence n J).functor.obj
        (letI := inftyDualModelCategory.{u} n J; ⊤_ (DiagSet.Infty.{u} n))) :=
      (letI := inftyDualModelCategory.{u} n J; terminalIsTerminal).isTerminalObj _
    have h₂ : (letI := inftyDualModelCategory.{u} n J; IsFibrant X) ↔
        Fibration ((inftyDualEquivalence n J).functor.map
          (letI := inftyDualModelCategory.{u} n J; terminal.from X)) := by
      rw [(letI := inftyDualModelCategory.{u} n J; isFibrant_iff X),
        (letI := inftyDualModelCategory.{u} n J; fibration_iff _),
        fibrations_inftyDualModelCategory, fibration_iff]
      rfl
    rw [h₂]
    exact (isFibrant_infty_iff n X).trans ((isInftyCategory_dual_iff J X).symm.trans
      ((isFibrant_infty_iff n _).symm.trans (isFibrant_iff_of_isTerminal _ hT)))

theorem weakEquivalence_toInfty_dual_map_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence ((DiagSet.toInfty n).map ((DiagSet.dual J).map f)) ↔
      WeakEquivalence ((DiagSet.toInfty n).map f) := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  exact (iff_of_eq (congrArg (fun W : MorphismProperty (DiagSet.Infty.{u} n) =>
    W ((DiagSet.toInfty n).map f)) (weakEquivalences_infty_dual n J))).symm

theorem trivialCofibration_toInfty_dual_map_iff {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    trivialCofibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map ((DiagSet.dual J).map f)) ↔
      trivialCofibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map f) := by
  rw [mem_trivialCofibrations_iff, mem_trivialCofibrations_iff,
    weakEquivalence_toInfty_dual_map_iff, cofibration_iff, cofibration_iff]
  exact and_congr_left' (mono_dual_map_iff J f)

end Transport

end Atoms.Diagrammatic
