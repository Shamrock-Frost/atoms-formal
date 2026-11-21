import Atoms.Diagrammatic.Pasting.CylinderDiagram

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

theorem isRewritableSubmolecule_image_refl {u : PastingDiagram X} (hu : u.IsRound) :
    u.shape.ogp.IsRewritableSubmolecule (Within.refl u).image ⊤ := by
  rw [Within.image_refl]
  exact ⟨.refl u.shape.isMolecule, rfl, hu⟩

section Unitor

variable (u : PastingDiagram X) (hd : 0 < u.dim) (hu : u.IsRound) (α : Bool)
  {v : PastingDiagram X} (ι : Within v (u.boundary (u.dim - 1) α))
  (hι : (u.boundary (u.dim - 1) α).shape.ogp.IsRewritableSubmolecule ι.image ⊤)

abbrev unitorImage : LowerSet u.shape.ogp :=
  OGP.map (bdryOccurrence u (u.dim - 1) α ι) ⊤

include hd hι in
theorem isSubmoleculeOf_unitorImage :
    u.shape.ogp.IsSubmoleculeOf (unitorImage u α ι) (u.shape.ogp.bdry ⊤ α) := by
  rw [bdry_eq_boundary (u.shape.krullDim_top_eq (Nat.sub_add_cancel hd).symm)]
  exact isSubmoleculeOf_bdryOccurrence u (u.dim - 1) α ι hι.isSubmoleculeOf

include hd hι in
theorem krullDim_unitorImage :
    krullDim (unitorImage u α ι) = krullDim (u.shape.ogp.bdry ⊤ α) := by
  rw [bdry_eq_boundary (u.shape.krullDim_top_eq (Nat.sub_add_cancel hd).symm), unitorImage,
    bdryOccurrence, map_comp, krullDim_map (u.shape.boundaryIncl (u.dim - 1) α),
    ← u.shape.map_boundaryIncl_top, krullDim_map (u.shape.boundaryIncl (u.dim - 1) α)]
  exact hι.krullDim_eq

abbrev unitorSubset : LowerSet u.shape.ogp :=
  (isSubmoleculeOf_unitorImage u hd α ι hι).hornSet u.shape.isMolecule (u.shape.isRound_iff.1 hu)
    (krullDim_unitorImage u hd α ι hι)

@[implicit_reducible] def unitorAt : PastingDiagram X :=
  cylDiagram u (unitorSubset u hd hu α ι hι)

theorem unitorSubset_le_bdryFull : unitorSubset u hd hu α ι hι ≤ u.shape.ogp.bdryFull ⊤ :=
  fun _ hy => hy.1

theorem boundary_not_le_unitorSubset :
    u.shape.ogp.boundary ⊤ (u.dim - 1) (!α) ≤ unitorSubset u hd hu α ι hι :=
  (bdry_eq_boundary (u.shape.krullDim_top_eq (Nat.sub_add_cancel hd).symm) (!α)).ge.trans
    ((isSubmoleculeOf_unitorImage u hd α ι hι).bdry_not_le_hornSet u.shape.isMolecule
      (u.shape.isRound_iff.1 hu) (krullDim_unitorImage u hd α ι hι)
      (u.shape.krullDim_top_eq (Nat.sub_add_cancel hd).symm))

theorem isDegenerate_unitorAt :
    (unitorAt u hd hu α ι hι).IsDegenerate ∧ (unitorAt u hd hu α ι hι).IsRound :=
  ⟨isDegenerate_cylDiagram u _ (unitorSubset_le_bdryFull u hd hu α ι hι),
    isRound_cylDiagram u _ hu (unitorSubset_le_bdryFull u hd hu α ι hι)⟩

theorem apply_bdryOccurrence_mem_unitorSubset_iff (x : v.shape.ogp) :
    bdryOccurrence u (u.dim - 1) α ι x ∈ unitorSubset u hd hu α ι hι ↔
      x ∈ v.shape.ogp.bdryFull ⊤ :=
  ((isSubmoleculeOf_unitorImage u hd α ι hι).mem_hornSet_iff_of_mem u.shape.isMolecule
    (u.shape.isRound_iff.1 hu) (krullDim_unitorImage u hd α ι hι)
    ⟨x, LowerSet.mem_top, rfl⟩).trans (by
      rw [← map_bdryFull, apply_mem_map_iff])

def unitorUnit : Within v.unit (unitorAt u hd hu α ι hι) :=
  Within.cyl u (unitorSubset u hd hu α ι hι) (ι.trans (Within.boundary u (u.dim - 1) α))
    (apply_bdryOccurrence_mem_unitorSubset_iff u hd hu α ι hι)

theorem unitorUnit_apply_eq_cylEndpoint_iff (β : Bool) (x : (unitShape v.shape).ogp)
    (y : u.shape.ogp) :
    (unitorUnit u hd hu α ι hι).emb x = cylEndpoint u.shape (unitorSubset u hd hu α ι hι) β y ↔
      ∃ x0, x = cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) β x0 ∧
        bdryOccurrence u (u.dim - 1) α ι x0 = y :=
  ((IsInclusion.injective (f := (cylShapeIso u.shape (unitorSubset u hd hu α ι hι)).hom)).eq_iff
    (a := PartialCylinder.embOfEmb (unitorSubset u hd hu α ι hι) (v.shape.ogp.bdryFull ⊤)
      (bdryOccurrence u (u.dim - 1) α ι) (apply_bdryOccurrence_mem_unitorSubset_iff u hd hu α ι hι)
      ((cylShapeIso v.shape (v.shape.ogp.bdryFull ⊤)).inv x))
    (b := partialCylinderEndpoint u.shape.ogp (unitorSubset u hd hu α ι hι) β y)).trans
    ((PartialCylinder.carrierMapOfMap_eq_endpoint_iff _ _ (bdryOccurrence u (u.dim - 1) α ι)
      (apply_bdryOccurrence_mem_unitorSubset_iff u hd hu α ι hι) β _ y).trans
      (exists_congr fun _ => and_congr_left' ⟨fun h =>
        ((cylShapeIso v.shape _).inv_hom_id_apply x).symm.trans
          (congrArg (cylShapeIso v.shape _).hom h), fun h =>
        (congrArg (cylShapeIso v.shape _).inv h).trans
          ((cylShapeIso v.shape _).hom_inv_id_apply _)⟩))

theorem map_cylEndpoint_unitorImage (β : Bool) :
    OGP.map (cylEndpoint u.shape (unitorSubset u hd hu α ι hι) β) (unitorImage u α ι) =
      (unitorAt u hd hu α ι hι).shape.ogp.boundary (unitorUnit u hd hu α ι hι).image
        (u.dim - 1) β := by
  have hsd : v.shape.dimension = u.dim - 1 :=
    Within.dim_eq_of_isRewritableSubmolecule_boundary hι (Nat.sub_le _ _)
  have hi : OGP.map (cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) β) ⊤ =
      v.unit.shape.ogp.boundary ⊤ (u.dim - 1) β := by
    rw [← hsd]
    exact map_cylEndpoint_bdryFull_top v.shape β
  have E : bdryOccurrence u (u.dim - 1) α ι ≫ cylEndpoint u.shape (unitorSubset u hd hu α ι hι) β =
      cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) β ≫ (unitorUnit u hd hu α ι hι).emb := by
    ext x0
    exact ((unitorUnit_apply_eq_cylEndpoint_iff u hd hu α ι hι β _ _).2 ⟨x0, rfl, rfl⟩).symm
  exact (map_comp _ _ ⊤).symm.trans ((congrArg (OGP.map · ⊤) E).trans ((map_comp _ _ ⊤).trans
    ((congrArg (OGP.map (unitorUnit u hd hu α ι hι).emb) hi).trans
      ((unitorUnit u hd hu α ι hι).boundary_image _ _).symm)))

theorem map_cylEndpoint_unitorImage_eq (β : Bool) :
    OGP.map (cylEndpoint u.shape (unitorSubset u hd hu α ι hι) β) (unitorImage u α ι) =
      OGP.map (cylEndpoint u.shape (unitorSubset u hd hu α ι hι) β)
        (OGP.map (u.shape.boundaryIncl (u.dim - 1) α) ι.image) :=
  congrArg _ (map_comp ι.emb (u.shape.boundaryIncl (u.dim - 1) α) ⊤)

theorem image_unitorUnit_sup :
    (unitorUnit u hd hu α ι hι).image ⊔
      (Within.cylCopy u (unitorSubset u hd hu α ι hι) (!α)).image =
        (unitorAt u hd hu α ι hι).shape.ogp.boundary ⊤ u.dim (!α) :=
  map_sup_map_eq_boundary u.shape.isMolecule (u.shape.isRound_iff.1 hu)
    u.shape.krullDim_eq_dimension hd
    (isSubmoleculeOf_unitorImage u hd α ι hι) (krullDim_unitorImage u hd α ι hι)
    (v.shape.ogp.bdryFull ⊤) (bdryOccurrence u (u.dim - 1) α ι) rfl
    (apply_bdryOccurrence_mem_unitorSubset_iff u hd hu α ι hι)
    (cylShapeIso v.shape _).symm (cylShapeIso u.shape _)

theorem image_unitorUnit_inf :
    (unitorUnit u hd hu α ι hι).image ⊓
      (Within.cylCopy u (unitorSubset u hd hu α ι hι) (!α)).image =
        OGP.map (cylEndpoint u.shape (unitorSubset u hd hu α ι hι) (!α)) (unitorImage u α ι) := by
  refine SetLike.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩ := LowerSet.mem_inf_iff.1 hz
    obtain ⟨x0, rfl, rfl⟩ :=
      (unitorUnit_apply_eq_cylEndpoint_iff u hd hu α ι hι (!α) x y).1 hy.symm
    exact ⟨_, ⟨x0, LowerSet.mem_top, rfl⟩, hy⟩
  · obtain ⟨y, ⟨x0, -, rfl⟩, rfl⟩ := hz
    exact LowerSet.mem_inf_iff.2 ⟨⟨cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) (!α) x0,
      LowerSet.mem_top, (unitorUnit_apply_eq_cylEndpoint_iff u hd hu α ι hι (!α) _ _).2
        ⟨x0, rfl, rfl⟩⟩, ⟨_, LowerSet.mem_top, rfl⟩⟩

theorem equiv_boundary_unitorAt : ((unitorAt u hd hu α ι hι).boundary u.dim α).Equiv u :=
  Within.equiv_of_image_eq (Within.boundary (unitorAt u hd hu α ι hι) u.dim α)
    (Within.cylCopy u (unitorSubset u hd hu α ι hι) α)
    ((Within.image_boundary _ _ _).trans
      (map_cylEndpoint_top u.shape _ hd (boundary_not_le_unitorSubset u hd hu α ι hι)).symm)

theorem equiv_boundary_not_unitorAt (h : (v.unit.boundary (u.dim - 1) (!α)).Equiv v) :
    ((unitorAt u hd hu α ι hι).boundary u.dim (!α)).Equiv
      (pasteAtBoundary v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h) := by
  have hsd : v.shape.dimension = u.dim - 1 :=
    Within.dim_eq_of_isRewritableSubmolecule_boundary hι (Nat.sub_le _ _)
  have R := cylEndpoint_bdryFull_apply_of_iso hsd (!α) h.iso
  have hmem (x0 : v.shape.ogp) : cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) (!α) x0 ∈
      (unitShape v.shape).ogp.boundary ⊤ (u.dim - 1) (!α) := by
    have hi := map_cylEndpoint_bdryFull_top v.shape (!α)
    rw [hsd] at hi
    exact hi ▸ ⟨x0, LowerSet.mem_top, rfl⟩
  let e := (unitShape v.shape).subIso ((unitShape v.shape).isMolecule.boundary (u.dim - 1) (!α))
  have hcond (x : (unitShape v.shape).ogp) (y : u.shape.ogp) :
      (unitorUnit u hd hu α ι hι).emb x =
          cylEndpoint u.shape (unitorSubset u hd hu α ι hι) (!α) y ↔
        pasteAtInl v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h x =
          pasteAtInr v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h y := by
    refine (unitorUnit_apply_eq_cylEndpoint_iff u hd hu α ι hι (!α) x y).trans (Iff.symm
      ((IsInclusion.injective
        (f := (pasteAtShapeIso v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h).hom)).eq_iff.trans
        (glue.inl_eq_inr_iff.trans ?_)))
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨h.iso.hom (e.hom ⟨x, hx⟩),
        ((R _).trans (congrArg Subtype.val (e.hom_inv_id_apply ⟨x, hx⟩))).symm, rfl⟩
    · rintro ⟨x0, rfl, rfl⟩
      refine ⟨hmem x0, congrArg (bdryOccurrence u (u.dim - 1) α ι) ?_⟩
      exact IsInclusion.injective (f := cylEndpoint v.shape (v.shape.ogp.bdryFull ⊤) (!α))
        ((R _).trans (congrArg Subtype.val (e.hom_inv_id_apply _)))
  exact (exists_iso_of_covers (a := (unitorAt u hd hu α ι hι).boundary u.dim (!α))
    (b := pasteAtBoundary v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h)
    (C := (unitorAt u hd hu α ι hι).shape.rdc) (P := (unitShape v.shape).rdc) (Q := u.shape.rdc)
    (unitorAt u hd hu α ι hι).map ((unitorAt u hd hu α ι hι).shape.boundaryIncl u.dim (!α)) rfl
    (unitorUnit u hd hu α ι hι).emb (cylEndpoint u.shape (unitorSubset u hd hu α ι hι) (!α))
    ((image_unitorUnit_sup u hd hu α ι hι).trans
      ((unitorAt u hd hu α ι hι).shape.map_boundaryIncl_top u.dim (!α)).symm)
    (pasteAtInl v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h)
    (pasteAtInr v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h)
    (map_pasteAtInl_sup_map_pasteAtInr _ _ _ _ _ _ _) hcond
    ((unitorUnit u hd hu α ι hι).comm.trans
      (ofInclusion_pasteAtInl_map v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h).symm)
    ((Within.cylCopy u (unitorSubset u hd hu α ι hι) (!α)).comm.trans
      (ofInclusion_pasteAtInr_map v.unit u (u.dim - 1) α ι hι.isSubmoleculeOf h).symm)).elim
    fun Θ hΘ => ⟨Θ, hΘ.1⟩

end Unitor

end Atoms.Diagrammatic.PastingDiagram
