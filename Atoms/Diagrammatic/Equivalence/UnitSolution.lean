import Atoms.Diagrammatic.Equivalence.Calculus
import Atoms.Diagrammatic.Pasting.Unitors

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section UnitEquation

variable (u : RoundPastingDiagram X) (hd : 0 < u.dim) (α : Bool)
  {v : PastingDiagram X} (j : Within v (u.boundary (u.dim - 1) α))
  (hj : (u.boundary (u.dim - 1) α).shape.ogp.IsRewritableSubmolecule j.image ⊤)

theorem dim_unit_sub : (j.round_image_iff.1 hj.isRound).unit.dim = u.dim - 1 + 1 := by
  change v.unit.dim = _
  rw [dim_unit, Within.dim_eq_of_isRewritableSubmolecule_boundary hj (Nat.sub_le _ _)]

include hd in
def unitEquation : Equation α (u.dim - 1) (j.round_image_iff.1 hj.isRound).unit u :=
  ⟨dim_unit_sub u α j hj, (Nat.sub_add_cancel hd).symm, v, j, hj,
    (boundary_unit (Within.dim_eq_of_isRewritableSubmolecule_boundary hj (Nat.sub_le _ _))
      α).symm⟩

include hd in
def unitData : PasteAtData α (u.dim - 1) (j.round_image_iff.1 hj.isRound).unit u :=
  ⟨dim_unit_sub u α j hj, (Nat.sub_add_cancel hd).symm, v, j, hj,
    boundary_unit (Within.dim_eq_of_isRewritableSubmolecule_boundary hj (Nat.sub_le _ _)) (!α)⟩

def unitorRound : RoundPastingDiagram X :=
  ⟨unitorAt u.toPastingDiagram hd u.isRound α j hj, (isDegenerate_unitorAt _ hd u.isRound α j hj).2⟩

theorem isDegenerate_unitorRound : (unitorRound u hd α j hj).IsDegenerate :=
  (isDegenerate_unitorAt _ hd u.isRound α j hj).1

theorem dim_unitorRound : (unitorRound u hd α j hj).dim = u.dim + 1 :=
  dim_cylDiagram u.toPastingDiagram _
    (unitorSubset_le_bdryFull u.toPastingDiagram hd u.isRound α j hj)

theorem hasBdry_unitorRound :
    HasBdry (!α) (u.dim - 1 + 1) (unitorRound u hd α j hj).toPastingDiagram
      (unitData u hd α j hj).pasting u.toPastingDiagram :=
  HasBdry.of_dim_eq (Nat.sub_add_cancel hd).symm (dim_unitorRound u hd α j hj)
    (unitData u hd α j hj).dim_pasting (Nat.sub_add_cancel hd).symm
    (equiv_boundary_not_unitorAt u.toPastingDiagram hd u.isRound α j hj _)
    (by rw [Bool.not_not]; exact equiv_boundary_unitorAt u.toPastingDiagram hd u.isRound α j hj)

noncomputable def unitorReverseRound : RoundPastingDiagram X :=
  ⟨(unitorRound u hd α j hj).reverse (isDegenerate_unitorRound u hd α j hj),
    isRound_reverse (isDegenerate_unitorRound u hd α j hj) (unitorRound u hd α j hj).isRound⟩

theorem isDegenerate_unitorReverseRound : (unitorReverseRound u hd α j hj).IsDegenerate :=
  isDegenerate_reverse _ _

theorem hasBdry_unitorReverseRound :
    HasBdry α (u.dim - 1 + 1) (unitorReverseRound u hd α j hj).toPastingDiagram
      (unitData u hd α j hj).pasting u.toPastingDiagram := by
  have hμ := dim_unitorRound u hd α j hj
  have hk : (unitorRound u hd α j hj).dim - 1 = u.dim := by omega
  refine HasBdry.of_dim_eq (k := (unitorRound u hd α j hj).dim - 1) (by omega)
    (by rw [unitorReverseRound, dim_reverse]; omega)
    (unitData u hd α j hj).dim_pasting (Nat.sub_add_cancel hd).symm ?_ ?_
  · exact (boundary_reverse _ (isDegenerate_unitorRound u hd α j hj) α).trans
      (boundary_congr _ hk.symm (!α) ▸
        equiv_boundary_not_unitorAt u.toPastingDiagram hd u.isRound α j hj _)
  · refine PastingDiagram.Equiv.trans
      (boundary_reverse _ (isDegenerate_unitorRound u hd α j hj) (!α)) ?_
    rw [Bool.not_not]
    exact boundary_congr _ hk.symm α ▸
      equiv_boundary_unitorAt u.toPastingDiagram hd u.isRound α j hj

def withinEndpoint (β : Bool) :
    Within u.toPastingDiagram (unitorRound u hd α j hj).toPastingDiagram :=
  Within.cylCopy u.toPastingDiagram (unitorSubset u.toPastingDiagram hd u.isRound α j hj) β

def withinUnit :
    Within (j.round_image_iff.1 hj.isRound).unit.toPastingDiagram
      (unitorRound u hd α j hj).toPastingDiagram :=
  unitorUnit u.toPastingDiagram hd u.isRound α j hj

theorem image_withinEndpoint :
    (withinEndpoint u hd α j hj α).image =
      (unitorRound u hd α j hj).shape.ogp.boundary ⊤ u.dim α :=
  map_cylEndpoint_top u.shape _ hd
    (boundary_not_le_unitorSubset u.toPastingDiagram hd u.isRound α j hj)

theorem image_occurrence_withinEndpoint (β : Bool) :
    (j.trans ((Within.boundary u.toPastingDiagram (u.dim - 1) α).trans
      (withinEndpoint u hd α j hj β))).image =
        OGP.map (cylEndpoint u.shape (unitorSubset u.toPastingDiagram hd u.isRound α j hj) β)
          (unitorImage u.toPastingDiagram α j) := by
  rw [Within.image_trans_assoc, Within.image_trans]
  exact (map_cylEndpoint_unitorImage_eq u.toPastingDiagram hd u.isRound α j hj β).symm

theorem isPastingAtIn_unitor :
    IsPastingAtIn (unitorRound u hd α j hj).shape.ogp (u.dim - 1) α (withinUnit u hd α j hj).image
      (withinEndpoint u hd α j hj (!α)).image
      ((unitorRound u hd α j hj).shape.ogp.boundary ⊤ u.dim (!α)) := by
  have hinter : (withinUnit u hd α j hj).image ⊓ (withinEndpoint u hd α j hj (!α)).image =
      OGP.map (cylEndpoint u.shape (unitorSubset u.toPastingDiagram hd u.isRound α j hj) (!α))
        (unitorImage u.toPastingDiagram α j) :=
    image_unitorUnit_inf u.toPastingDiagram hd u.isRound α j hj
  refine ⟨(withinUnit u hd α j hj).isMoleculeIn_image,
    (withinEndpoint u hd α j hj (!α)).isMoleculeIn_image,
    (image_unitorUnit_sup u.toPastingDiagram hd u.isRound α j hj).symm, ?_, ?_⟩
  · rw [hinter]
    exact map_cylEndpoint_unitorImage u.toPastingDiagram hd u.isRound α j hj (!α)
  · rw [hinter, (withinEndpoint u hd α j hj (!α)).boundary_image]
    exact (isSubmoleculeOf_map_iff
      (cylEndpoint u.shape (unitorSubset u.toPastingDiagram hd u.isRound α j hj) (!α))).2
      (isSubmoleculeOf_bdryOccurrence u.toPastingDiagram (u.dim - 1) α j hj.isSubmoleculeOf)

theorem image_occurrence_eq_inter :
    (j.trans ((Within.boundary u.toPastingDiagram (u.dim - 1) α).trans
      (withinEndpoint u hd α j hj (!α)))).image =
        (withinUnit u hd α j hj).image ⊓ (withinEndpoint u hd α j hj (!α)).image :=
  (image_occurrence_withinEndpoint u hd α j hj (!α)).trans
    (image_unitorUnit_inf u.toPastingDiagram hd u.isRound α j hj).symm

theorem isMoleculeIn_boundary_unitor :
    IsMoleculeIn (unitorRound u hd α j hj).shape.ogp
      ((unitorRound u hd α j hj).shape.ogp.boundary ⊤ u.dim (!α)) :=
  IsMoleculeIn.boundary (unitorRound u hd α j hj).shape.isMolecule _ _

theorem equiv_pasting_restrictTo :
    (unitData u hd α j hj).pasting.Equiv
      ((unitorRound u hd α j hj).toPastingDiagram.restrictTo
        (isMoleculeIn_boundary_unitor u hd α j hj)) :=
  equiv_pasteAtBoundary_of_within (withinUnit u hd α j hj) (withinEndpoint u hd α j hj (!α))
    (isPastingAtIn_unitor u hd α j hj) j hj.isSubmoleculeOf
    (image_occurrence_eq_inter u hd α j hj) (unitData u hd α j hj).equiv

theorem compat_unitData : Compat (unitEquation u hd α j hj) (unitData u hd α j hj) := by
  let g : Geometry (unitData u hd α j hj) u (unitorRound u hd α j hj) (!α) :=
    Geometry.ofHasBdry (hasBdry_unitorRound u hd α j hj)
  refine g.compat_of_image ?_
  have hwU : g.wU = withinEndpoint u hd α j hj α := by
    refine Within.ext_of_image_eq _ _ ?_
    rw [g.image_wU, image_withinEndpoint, Bool.not_not, Nat.sub_add_cancel hd]
  have hR := isMoleculeIn_boundary_unitor u hd α j hj
  let e₀ := equiv_pasting_restrictTo u hd α j hj
  have hwP : g.wP = (Within.ofEquiv e₀).trans
      (Within.restrictTo (unitorRound u hd α j hj).toPastingDiagram hR) := by
    refine Within.ext_of_image_eq _ _ ?_
    rw [g.image_wP, Within.image_trans, Within.image_ofEquiv]
    exact (congrArg (fun k => (unitorRound u hd α j hj).shape.ogp.boundary ⊤ k (!α))
      (Nat.sub_add_cancel hd)).trans (Within.image_restrictTo _ hR).symm
  have hE : g.withinE.image = (withinUnit u hd α j hj).image := by
    have hemb : g.withinE.emb = (withinUnit u hd α j hj).emb := by
      ext x
      rw [Geometry.withinE, hwP]
      exact (apply_iso_pasteAtInl_and_pasteAtInr_of_within (withinUnit u hd α j hj)
        (withinEndpoint u hd α j hj (!α)) (isPastingAtIn_unitor u hd α j hj) j hj.isSubmoleculeOf
        (image_occurrence_eq_inter u hd α j hj) hR (unitData u hd α j hj).equiv e₀).1 x
    exact congrArg (OGP.map · ⊤) hemb
  rw [hwU, hE]
  change (j.trans ((Within.boundary u.toPastingDiagram (u.dim - 1) α).trans
    (withinEndpoint u hd α j hj α))).image = _
  rw [image_occurrence_withinEndpoint]
  exact map_cylEndpoint_unitorImage u.toPastingDiagram hd u.isRound α j hj α

noncomputable def unitSolution :
    UnbiasedSolution {a : RoundPastingDiagram X | a.IsDegenerate} (unitEquation u hd α j hj) :=
  UnbiasedSolution.ofSides u (unitData u hd α j hj) (compat_unitData u hd α j hj) (β := α)
    ⟨unitorReverseRound u hd α j hj, isDegenerate_unitorReverseRound u hd α j hj,
      hasBdry_unitorReverseRound u hd α j hj⟩
    ⟨unitorRound u hd α j hj, isDegenerate_unitorRound u hd α j hj, hasBdry_unitorRound u hd α j hj⟩

end UnitEquation

end Atoms.Diagrammatic
