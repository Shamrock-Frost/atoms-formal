import Atoms.Diagrammatic.Marked.Horn
import Atoms.Diagrammatic.Horn.Atomic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape
open Atoms.Homotopical (MarkedPresheaf)

universe u

namespace Atoms.Diagrammatic.MarkedDiagSet

variable {X Y : DiagSet.{u}}

def markedAtom (U : Atom) (hU : 0 < U.dimension) : MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking (ball U)
  ⟨fun V => {x | IsDegenerate (ball U) x ∨ IsIso (x.down : V ⟶ U)},
    fun V x hx => by
      rcases hx with hx | hx
      · exact dimension_pos_of_isDegenerate hx
      · exact (congrArg (0 < ·) (Atom.dimension_eq_of_iso (asIso (x.down : V ⟶ U)))).mpr hU,
    fun _ b p hp y => Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩,
    fun V W e x => by
      refine or_congr (isDegenerate_map_iso_iff e x).symm ?_
      change IsIso (x.down : W ⟶ U) ↔ IsIso (e.hom ≫ (x.down : W ⟶ U))
      exact (isIso_comp_left_iff e.hom _).symm⟩

noncomputable def markingInclusion (U : Atom) (hU : 0 < U.dimension) :
    (MarkedPresheaf.flat atomMarking).obj (ball.{u} U) ⟶ markedAtom U hU :=
  MarkedPresheaf.homMk (𝟙 (ball U)) fun V _ hx => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
    (Or.inl ((mem_marked_flat_iff_isDegenerate _ V _).1 hx))

end Atoms.Diagrammatic.MarkedDiagSet

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def markingGeneratorsAbove (n : ℕ∞) : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : Atom // n < U.dimension} =>
    MarkedDiagSet.markingInclusion U.1 (Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) U.2))

theorem hasMarkedRLP_markingGeneratorsAbove_iff (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    HasMarkedRLP (markingGeneratorsAbove n) X ↔
      ∀ (U : Atom) (x : diagram X.underlying U),
        n < U.dimension → x ∈ X.marked U := by
  constructor
  · intro hX U x hn
    have hU : 0 < U.dimension := Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) hn)
    let q := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ X).symm
      (uliftYonedaEquiv.symm x)
    obtain ⟨f, hf⟩ := hasMarkedRLP_iff.1 hX (MarkedDiagSet.markingInclusion U hU)
      (MorphismProperty.ofHoms.mk (⟨U, hn⟩ : {U : Atom // n < U.dimension})) q
    have hfq : MarkedPresheaf.forget.map f = uliftYonedaEquiv.symm x :=
      (Category.id_comp _).symm.trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map hf))
    have hx : (MarkedPresheaf.forget.map f).app (op U) ⟨𝟙 U⟩ = x := by
      rw [hfq]
      exact uliftYonedaEquiv.apply_symm_apply x
    rw [← hx]
    exact MarkedPresheaf.map_mem_marked f
      ((MarkedPresheaf.mem_marked_ofMarking _ _ U _).2 (Or.inr (IsIso.id U)))
  · intro hX
    refine hasMarkedRLP_iff.2 fun A B i hi q => ?_
    cases hi with
    | mk U =>
      refine ⟨MarkedPresheaf.homMk (MarkedPresheaf.forget.map q) fun V y hy => ?_,
        MarkedPresheaf.hom_ext ?_⟩
      · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | hy
        · exact MarkedPresheaf.map_mem_marked q
            ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).2 hy)
        · refine hX V _ ?_
          rw [Atom.dimension_eq_of_iso (asIso (y.down : V ⟶ U.1))]
          exact U.2
      · exact (MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)

theorem exists_markedHorn (h : AtomicHornData) :
    ∃ m : MarkedHornData, Nonempty
      (Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u} m)) ≅
        Arrow.mk (hornInclusion h.toHornData)) := by
  obtain ⟨m, hm⟩ := h.exists_markedHornData
  exact ⟨m, ⟨m.forgetArrowIso.trans
    (eqToIso (congrArg (fun k => Arrow.mk (hornInclusion k)) hm))⟩⟩

theorem hasMarkedRLP_markedHorns_sharp_iff (X : DiagSet.{u}) :
    HasMarkedRLP markedHorns ((MarkedPresheaf.sharp atomMarking).obj X) ↔
      IsAtomicHornFibrant X := by
  constructor
  · intro hX A B i hi
    cases hi with
    | mk h =>
      obtain ⟨m, ⟨e⟩⟩ := exists_markedHorn h
      have := (MarkedPresheaf.hasLiftingProperty_terminal_from_sharp_iff atomMarking _ X).1
        (hX _ (MorphismProperty.ofHoms.mk m))
      exact HasLiftingProperty.of_arrow_iso_left e (terminal.from X)
  · intro hX A B i hi
    cases hi with
    | mk m =>
      have : HasLiftingProperty (hornInclusion m.toHornData) (terminal.from X) :=
        hX _ (MorphismProperty.ofHoms.mk (⟨m.toHornData, m.isAtomic⟩ : AtomicHornData))
      exact (MarkedPresheaf.hasLiftingProperty_terminal_from_sharp_iff atomMarking _ X).2
        (HasLiftingProperty.of_arrow_iso_left m.forgetArrowIso.symm (terminal.from X))

end Atoms.Diagrammatic
