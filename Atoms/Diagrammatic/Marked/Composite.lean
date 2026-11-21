import Atoms.Diagrammatic.Marked.Invertible
import Atoms.Diagrammatic.InftyCategory

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

section Compositor

variable (U : RoundShape) (hU : 0 < U.dimension)

def compositorHornMap {Y : DiagSet.{u}} (v : realize.obj U.rdc ⟶ Y) :
    realize.obj (compositorMarkedHorn U hU).hornRDC ⟶ Y :=
  realize.map (RDCpx.isoOfIso (P := (compositorMarkedHorn U hU).hornRDC) (Q := U.rdc)
    (compositorHornIso U hU).symm).hom ≫ v

end Compositor

theorem exists_mem_marked_toMergerInclusion_comp_eq_of_hasLiftingProperty (X : MarkedDiagSet.{u})
    (U : RoundShape) (hU : 0 < U.dimension)
    (hX : HasLiftingProperty (markedHornInclusion (compositorMarkedHorn U hU)) (terminal.from X))
    (v : realize.obj U.rdc ⟶ X.underlying) :
    ∃ z : diagram X.underlying (toMergerAtom U hU), z ∈ X.marked (toMergerAtom U hU) ∧
      toMergerInclusion U hU ≫ uliftYonedaEquiv.symm z = v := by
  obtain ⟨z, hz, hzm, -⟩ := exists_fills_of_hasLiftingProperty (compositorMarkedHorn U hU) hX
    (compositorHornMap U hU v) (fun a ha => absurd ha (Set.notMem_empty a))
  refine ⟨z, hzm, (Category.assoc _ _ _).trans ?_⟩
  have hcomp : RDCpx.ofInclusion (P := U.rdc) (Q := (compositorMarkedHorn U hU).hornRDC)
      (codRestrict (toMergerInputIncl U hU) (compositorMarkedHorn U hU).hornSet
        (inputEmb_mem_horn U hU)) ≫ (compositorMarkedHorn U hU).hornIncl =
      RDCpx.ofInclusion (P := U.rdc) (Q := atomToRDCpx.obj (toMergerAtom U hU))
        (toMergerInputIncl U hU) := by
    ext x
    rfl
  exact (congrArg (fun t => realize.map t ≫ (ofCell z).map) hcomp.symm).trans
      ((realize.map_comp_assoc _ _ _).trans ((congrArg (realize.map _ ≫ ·) hz).trans
        ((realize.map_comp_assoc _ _ _).symm.trans
          ((congrArg (fun t => realize.map t ≫ v)
            (inputEmb_comp_compositorHornIso U hU)).trans
            ((congrArg (· ≫ v) (realize.map_id _)).trans (Category.id_comp _))))))

theorem exists_mem_marked_toMergerInclusion_comp_eq (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP markedHorns X) (U : RoundShape) (hU : 0 < U.dimension)
    (v : realize.obj U.rdc ⟶ X.underlying) :
    ∃ z : diagram X.underlying (toMergerAtom U hU), z ∈ X.marked (toMergerAtom U hU) ∧
      toMergerInclusion U hU ≫ uliftYonedaEquiv.symm z = v :=
  exists_mem_marked_toMergerInclusion_comp_eq_of_hasLiftingProperty X U hU
    (hX _ (MorphismProperty.ofHoms.mk _)) v

theorem exists_weakComposite_of_isEquivalence (u : RoundPastingDiagram X) (hu : 0 < u.dim)
    (z : diagram X (toMergerAtom u.roundShape hu)) (hz : IsEquivalence X z)
    (hin : toMergerInclusion u.roundShape hu ≫ uliftYonedaEquiv.symm z = u.map) :
    ∃ c : diagram X (mergerAtom u.roundShape hu), Equivalent u (cellRound c) := by
  let U : RoundShape := u.roundShape
  have hd : U.dimension = U.dimension - 1 + 1 := (Nat.sub_add_cancel hu).symm
  have hU : 0 < U.dimension := hu
  let inIncl : u.shape.ogp ⟶ (toMergerAtom U hu).ogp := toMergerInputIncl U hu
  have : IsInclusion inIncl := inferInstanceAs (IsInclusion (toMergerInputIncl U hU))
  let outIncl : (mergerAtom U hu).ogp ⟶ (toMergerAtom U hu).ogp := U.outputIncl hd
  have : IsInclusion outIncl := inferInstanceAs (IsInclusion (U.outputIncl hd))
  have hin' : realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (toMergerAtom U hu).rdc)
      inIncl) ≫ (ofCell z).map = u.map :=
    (Category.assoc _ _ _).symm.trans hin
  let g : mergerAtom U hu ⟶ toMergerAtom U hu := Atom.ofInclusion outIncl
  have hout : realize.map (RDCpx.ofInclusion (P := (mergerAtom U hu).rdc)
      (Q := (toMergerAtom U hu).rdc) outIncl) ≫ (ofCell z).map = (ofCell (X.map g.op z)).map :=
    (ofCell_map_op_map g z).symm
  refine ⟨X.map g.op z, EquivalenceData.equivalent ⟨(dimension_mergerAtom U hu).symm,
    cellRound z, hz, dimension_toMergerAtom U hu, ?_, ?_⟩⟩
  · exact equiv_of_emb_of_image_eq (a := (ofCell z).boundary u.dim false) (b := u.toPastingDiagram)
      (C := (toMergerAtom U hu).toMoleculeShape.rdc) (ofCell z).map
      ((toMergerAtom U hu).toMoleculeShape.boundaryIncl u.dim false) inIncl
      (boundary_comm (ofCell z) _ _) hin'
      ((MoleculeShape.map_boundaryIncl_top _ _ _).trans ((bdry_toMergerAtom U hu false).symm.trans
        (U.map_inputIncl hd).symm))
  · exact equiv_of_emb_of_image_eq (a := (ofCell z).boundary u.dim true)
      (b := ofCell (X.map g.op z)) (C := (toMergerAtom U hu).toMoleculeShape.rdc) (ofCell z).map
      ((toMergerAtom U hu).toMoleculeShape.boundaryIncl u.dim true) outIncl
      (boundary_comm (ofCell z) _ _) hout
      ((MoleculeShape.map_boundaryIncl_top _ _ _).trans ((bdry_toMergerAtom U hu true).symm.trans
        (U.map_outputIncl hd).symm))

theorem hasWeakComposites_of_hasLiftingProperty (X : MarkedDiagSet.{u})
    (hC : ∀ (U : RoundShape) (hU : 0 < U.dimension),
      HasLiftingProperty (markedHornInclusion (compositorMarkedHorn U hU)) (terminal.from X))
    (hI : ∀ (V : Atom) (ε : Bool) (hV : 0 < V.dimension),
      HasLiftingProperty (markedHornInclusion (invertorMarkedHorn V ε hV)) (terminal.from X)) :
    HasWeakComposites X.underlying := by
  refine (hasWeakComposites_iff_positive _).2 fun u hu => ?_
  obtain ⟨z, hzm, hin⟩ := exists_mem_marked_toMergerInclusion_comp_eq_of_hasLiftingProperty X
    u.roundShape hu (hC u.roundShape hu) u.map
  exact exists_weakComposite_of_isEquivalence u hu z
    (isEquivalence_of_mem_marked X hI _ z hzm) hin

theorem hasWeakComposites_of_hasMarkedRLP (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP markedHorns X) : HasWeakComposites X.underlying :=
  hasWeakComposites_of_hasLiftingProperty X (fun _ _ => hX _ (MorphismProperty.ofHoms.mk _))
    (fun _ _ _ => hX _ (MorphismProperty.ofHoms.mk _))

theorem isInftyCategory_of_hasMarkedRLP (n : ℕ∞) (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP (markedHorns ⊔ markingGeneratorsAbove n) X) :
    IsInftyCategory n X.underlying := by
  obtain ⟨hH, hJ⟩ := (hasMarkedRLP_sup _ _ X).1 hX
  exact ⟨hasWeakComposites_of_hasMarkedRLP X hH, fun U x hn =>
    marked_subset_equivalences X hH U x ((hasMarkedRLP_markingGeneratorsAbove_iff n X).1 hJ U x hn)⟩

end Atoms.Diagrammatic
