import Atoms.Diagrammatic.Pasting.Units
import Atoms.Diagrammatic.Pasting.Within
import Atoms.Molecule.Cylinder.Unitor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X : DiagSet.{u}}

section Cylinder

variable (m : PastingDiagram X) {K : LowerSet m.shape.ogp} [DecidablePred (· ∈ K)]

def cylImage (S : LowerSet (partialCylinder m.shape.ogp K)) :
    LowerSet (cylDiagram m K).shape.ogp :=
  OGP.map (cylShapeIso m.shape K).hom S

variable {m}

theorem isMoleculeIn_cylImage {S : LowerSet (partialCylinder m.shape.ogp K)}
    (h : IsMoleculeIn (partialCylinder m.shape.ogp K) S) :
    IsMoleculeIn (cylDiagram m K).shape.ogp (cylImage m S) :=
  (isMoleculeIn_map_iff (cylShapeIso m.shape K).hom S).2 h

theorem isPastingIn_cylImage {n : ℕ} {S T R : LowerSet (partialCylinder m.shape.ogp K)}
    (h : (partialCylinder m.shape.ogp K).IsPastingIn n S T R) :
    (cylDiagram m K).shape.ogp.IsPastingIn n (cylImage m S) (cylImage m T) (cylImage m R) :=
  (isPastingIn_map_iff (cylShapeIso m.shape K).hom n S T R).2 h

theorem isPastingAtIn_cylImage {n : ℕ} {α : Bool}
    {S T R : LowerSet (partialCylinder m.shape.ogp K)}
    (h : (partialCylinder m.shape.ogp K).IsPastingAtIn n α S T R) :
    (cylDiagram m K).shape.ogp.IsPastingAtIn n α (cylImage m S) (cylImage m T)
      (cylImage m R) :=
  h.map (cylShapeIso m.shape K).hom

theorem boundary_cylImage (S : LowerSet (partialCylinder m.shape.ogp K)) (n : ℕ) (α : Bool) :
    (cylDiagram m K).shape.ogp.boundary (cylImage m S) n α =
      cylImage m ((partialCylinder m.shape.ogp K).boundary S n α) :=
  (map_boundary _ S n α).symm

theorem krullDim_cylImage (S : LowerSet (partialCylinder m.shape.ogp K)) :
    krullDim (cylImage m S) = krullDim S :=
  krullDim_map _ S

theorem cylImage_top : cylImage m (⊤ : LowerSet (partialCylinder m.shape.ogp K)) = ⊤ :=
  map_top_of_isIso _

theorem cylImage_inf (S T : LowerSet (partialCylinder m.shape.ogp K)) :
    cylImage m (S ⊓ T) = cylImage m S ⊓ cylImage m T :=
  map_inf _ S T

theorem image_boundary_cylDiagram (n : ℕ) (α : Bool) :
    (Within.boundary (cylDiagram m K) n α).image =
      cylImage m ((partialCylinder m.shape.ogp K).boundary ⊤ n α) := by
  rw [Within.image_boundary, ← cylImage_top, boundary_cylImage]

variable (m K)

def Within.cylCopy (β : Bool) : Within m (cylDiagram m K) :=
  ⟨cylEndpoint m.shape K β, by
    change realize.map (RDCpx.ofInclusion (P := m.shape.rdc) (Q := (cylShape m.shape K).rdc)
      (cylEndpoint m.shape K β)) ≫ realize.map (cylProj m.shape K) ≫ m.map = m.map
    rw [← Category.assoc, ← realize.map_comp, ofInclusion_cylEndpoint_comp_cylProj,
      realize.map_id, Category.id_comp]⟩

theorem image_cylCopy (β : Bool) :
    (Within.cylCopy m K β).image = cylImage m (PartialCylinder.copy K β ⊤) := by
  change OGP.map (partialCylinderEndpoint m.shape.ogp K β ≫ (cylShapeIso m.shape K).hom) ⊤ = _
  rw [map_comp, PartialCylinder.map_partialCylinderEndpoint]
  rfl

theorem image_trans_cylCopy {a : PastingDiagram X} (w : Within a m) (β : Bool) :
    (w.trans (Within.cylCopy m K β)).image = cylImage m (PartialCylinder.copy K β w.image) := by
  rw [Within.image_trans]
  change OGP.map (partialCylinderEndpoint m.shape.ogp K β ≫ (cylShapeIso m.shape K).hom)
    w.image = _
  rw [map_comp, PartialCylinder.map_partialCylinderEndpoint]
  rfl

def Within.cyl {a : PastingDiagram X} (w : Within a m) {L : LowerSet a.shape.ogp}
    [DecidablePred (· ∈ L)] (hf : ∀ x, w.emb x ∈ K ↔ x ∈ L) :
    Within (cylDiagram a L) (cylDiagram m K) :=
  ⟨(cylShapeIso a.shape L).inv ≫ PartialCylinder.embOfEmb K L w.emb hf ≫
      (cylShapeIso m.shape K).hom, by
    have E : RDCpx.ofInclusion (P := (cylShape a.shape L).rdc) (Q := (cylShape m.shape K).rdc)
        ((cylShapeIso a.shape L).inv ≫ PartialCylinder.embOfEmb K L w.emb hf ≫
          (cylShapeIso m.shape K).hom) ≫ cylProj m.shape K =
        cylProj a.shape L ≫ RDCpx.ofInclusion (P := a.shape.rdc) (Q := m.shape.rdc) w.emb := by
      ext x
      exact (congrArg (partialCylinderProj _ _)
        ((cylShapeIso m.shape K).hom_inv_id_apply _)).trans
          (PartialCylinder.proj_carrierMapOfMap K L w.emb hf _)
    change realize.map (RDCpx.ofInclusion (P := (cylShape a.shape L).rdc)
        (Q := (cylShape m.shape K).rdc) _) ≫ realize.map (cylProj m.shape K) ≫ m.map =
      realize.map (cylProj a.shape L) ≫ a.map
    exact (realize.map_comp_assoc _ _ _).symm.trans
      ((congrArg (fun t => realize.map t ≫ m.map) E).trans
        ((realize.map_comp_assoc _ _ _).trans (congrArg _ w.comm)))⟩

theorem image_cyl {a : PastingDiagram X} (w : Within a m) {L : LowerSet a.shape.ogp}
    [DecidablePred (· ∈ L)] (hf : ∀ x, w.emb x ∈ K ↔ x ∈ L) :
    (Within.cyl m K w hf).image = cylImage m (PartialCylinder.over K w.image) := by
  change OGP.map ((cylShapeIso a.shape L).inv ≫ PartialCylinder.embOfEmb K L w.emb hf ≫
      (cylShapeIso m.shape K).hom) ⊤ = _
  rw [map_comp, map_comp, map_top_of_isIso, PartialCylinder.map_embOfEmb_top]
  rfl

end Cylinder

theorem equiv_substitute_of_equiv (u : PastingDiagram X) {v : PastingDiagram X} (ι : Within v u)
    (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤) (w : RoundPastingDiagram X)
    (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w) (e : w.toPastingDiagram.Equiv v) :
    (u.substitute ι hι w hw).Equiv u := by
  classical
  let K := hι.complement
  let wW : Within w.toPastingDiagram (cylDiagram u K) :=
    (Within.ofEquiv e).trans (ι.trans (Within.cylCopy u K true))
  have hocc (β : Bool) : (ι.trans (Within.cylCopy u K β)).image =
      cylImage u (PartialCylinder.copy K β (OGP.map ι.emb ⊤)) :=
    image_trans_cylCopy u K ι β
  have hW : wW.image = cylImage u (PartialCylinder.copy K true (OGP.map ι.emb ⊤)) := by
    rw [Within.image_trans, Within.image_ofEquiv]
    exact hocc true
  have hs : (cylDiagram u K).shape.ogp.IsSubstitutionIn (Within.cylCopy u K false).image
      (ι.trans (Within.cylCopy u K false)).image wW.image
      (Within.cylCopy u K true).image := by
    rw [image_cylCopy u K false, hocc false, hW, image_cylCopy u K true]
    exact (PartialCylinder.isSubstitutionIn_copy hι).map (cylShapeIso u.shape K).hom
  exact PastingDiagram.Equiv.trans
    (equiv_substitute_of_within ι hι w hw (Within.cylCopy u K false) wW hs
      (Within.cylCopy u K true).isMoleculeIn_image)
    ((Within.cylCopy u K true).equiv_restrictTo_of_eq rfl
      (Within.cylCopy u K true).isMoleculeIn_image).symm

end Atoms.Diagrammatic.PastingDiagram
