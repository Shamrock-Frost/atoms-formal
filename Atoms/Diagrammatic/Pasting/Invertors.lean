import Atoms.Diagrammatic.Pasting.Reverse
import Atoms.Diagrammatic.Pasting.SubsetRestriction
import Atoms.Molecule.MoleculeShape.InvertedCylinder

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

private theorem shape_dimension_pos {u : PastingDiagram X} (hu : u.IsDegenerate) :
    0 < u.shape.dimension :=
  dim_pos_of_isDegenerate hu

noncomputable def invertor (u : PastingDiagram X) (hu : u.IsDegenerate) (α : Bool) :
    PastingDiagram X :=
  ⟨invertorShape u.shape (!α) (shape_dimension_pos hu),
    realize.map (invertorProj u.shape (!α) (shape_dimension_pos hu) hu.factorization.proj
      hu.factorization.dim_lt) ≫ hu.factorization.map⟩

theorem dim_invertor (u : PastingDiagram X) (hu : u.IsDegenerate) (α : Bool) :
    (u.invertor hu α).dim = u.dim + 1 := by
  have hd := shape_dimension_pos hu
  obtain ⟨x, hx, hxd⟩ := exists_notMem_bdryFull_grade_eq u.shape.isMolecule
    u.shape.krullDim_eq_dimension
  have h := krullDim_partialCylinder (K := u.shape.ogp.bdry ⊤ (!α))
    u.shape.krullDim_eq_dimension ⟨x, fun h => hx (bdry_le_bdryFull ⊤ _ h), hxd⟩
  have h2 : krullDim (u.invertor hu α).shape.ogp =
      krullDim (partialCylinder u.shape.ogp (u.shape.ogp.bdry ⊤ (!α))) :=
    (krullDim_eq_of_orderIso (orderIsoOfIso (invertorShapeIso u.shape (!α) hd))).symm
  rw [h, (u.invertor hu α).shape.krullDim_eq_dimension] at h2
  exact_mod_cast h2

theorem isDegenerate_invertor (u : PastingDiagram X) (hu : u.IsDegenerate) (α : Bool) :
    (u.invertor hu α).IsDegenerate :=
  ⟨hu.factorization.target,
    invertorProj u.shape (!α) (shape_dimension_pos hu) hu.factorization.proj
      hu.factorization.dim_lt, hu.factorization.map,
    surjective_invertorProj _ _ _ _ _ hu.factorization.surjective,
    hu.factorization.dim_lt.trans (by
      rw [dim_invertor]
      exact_mod_cast Nat.lt_succ_self _), rfl⟩

theorem isRound_invertor {u : PastingDiagram X} (hu : u.IsDegenerate) (hr : u.IsRound)
    (α : Bool) : (u.invertor hu α).IsRound :=
  (isRound_top_iff_of_iso (invertorShapeIso u.shape (!α) (shape_dimension_pos hu))).2
    (InvertedCylinder.isRound_invertedCylinder u.shape.isMolecule u.shape.krullDim_eq_dimension
      (shape_dimension_pos hu) hr le_rfl)

section Invertor

variable (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)

def invertorDual (w : realize.obj (invertorShape P ε hd).rdc ⟶ X) : PastingDiagram X :=
  ⟨P.dual (OGP.topDim P.dimension),
    realize.map (RDCpx.ofInclusion (P := (P.dual (OGP.topDim P.dimension)).rdc)
      (Q := (invertorShape P ε hd).rdc) (invertorEndpointDual P ε hd)) ≫ w⟩

theorem equiv_invertor_boundary_eps (hr : P.IsRound)
    (w : realize.obj (invertorShape P ε hd).rdc ⟶ X) (v : realize.obj P.rdc ⟶ X)
    (hu : realize.map (RDCpx.ofInclusion
        (P := (unitShape (P.boundary (P.dimension - 1) (!ε))).rdc)
        (Q := (invertorShape P ε hd).rdc) (invertorUnitEmb P ε hd hr)) ≫ w =
      realize.map (cylProj (P.boundary (P.dimension - 1) (!ε))
          ((P.boundary (P.dimension - 1) (!ε)).ogp.bdryFull ⊤)) ≫
        realize.map (P.boundaryInclRDC (P.dimension - 1) (!ε)) ≫ v) :
    ((⟨invertorShape P ε hd, w⟩ : PastingDiagram X).boundary P.dimension ε).Equiv
      ((⟨P, v⟩ : PastingDiagram X).boundary (P.dimension - 1) (!ε)).unit :=
  equiv_of_emb_of_image_eq w ((invertorShape P ε hd).boundaryIncl P.dimension ε)
    (invertorUnitEmb P ε hd hr) rfl hu
    (((invertorShape P ε hd).map_boundaryIncl_top _ _).trans
      (image_invertorUnitEmb P ε hd hr).symm)

private theorem isPastingIn_invertorShape_cond {u v : PastingDiagram X}
    (gA : u.shape.ogp ⟶ (invertorShape P ε hd).ogp) (gB : v.shape.ogp ⟶ (invertorShape P ε hd).ogp)
    (hA : OGP.map gA ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) (!ε) ⊤))
    (hB : OGP.map gB ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) ε ⊤)) :
    (invertorShape P ε hd).ogp.IsPastingIn (P.dimension - 1) (cond ε (OGP.map gA ⊤) (OGP.map gB ⊤))
      (cond ε (OGP.map gB ⊤) (OGP.map gA ⊤))
      ((invertorShape P ε hd).ogp.boundary ⊤ P.dimension (!ε)) := by
  rw [hA, hB]
  cases ε <;> exact isPastingIn_invertorShape P _ hd

theorem equiv_invertor_boundary_meet (w : realize.obj (invertorShape P ε hd).rdc ⟶ X)
    (u v : PastingDiagram X) (gA : u.shape.ogp ⟶ (invertorShape P ε hd).ogp)
    (gB : v.shape.ogp ⟶ (invertorShape P ε hd).ogp) [IsInclusion gA] [IsInclusion gB]
    (hu : realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (invertorShape P ε hd).rdc)
      gA) ≫ w = u.map)
    (hv : realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := (invertorShape P ε hd).rdc)
      gB) ≫ w = v.map)
    (hA : OGP.map gA ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) (!ε) ⊤))
    (hB : OGP.map gB ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) ε ⊤)) :
    (u.boundary (P.dimension - 1) ε).Equiv (v.boundary (P.dimension - 1) (!ε)) := by
  obtain ⟨-, h₁, h₂⟩ :=
    (isPastingIn_cond_iff ε).1 (isPastingIn_invertorShape_cond P ε hd gA gB hA hB)
  refine equiv_of_emb_of_image_eq w
    (u.shape.boundaryIncl _ ε ≫ gA :
      (u.shape.boundary (P.dimension - 1) ε).ogp ⟶ (invertorShape P ε hd).ogp)
    (v.shape.boundaryIncl _ (!ε) ≫ gB :
      (v.shape.boundary (P.dimension - 1) (!ε)).ogp ⟶ (invertorShape P ε hd).ogp) ?_ ?_ ?_
  · exact (congrArg (fun t => realize.map t ≫ w) (by ext; rfl :
      RDCpx.ofInclusion (P := (u.shape.boundary (P.dimension - 1) ε).rdc)
        (Q := (invertorShape P ε hd).rdc) (u.shape.boundaryIncl _ ε ≫ gA) =
      u.shape.boundaryInclRDC _ ε ≫ RDCpx.ofInclusion (P := u.shape.rdc)
        (Q := (invertorShape P ε hd).rdc) gA)).trans
      ((realize.map_comp_assoc _ _ _).trans (congrArg (realize.map _ ≫ ·) hu))
  · exact (congrArg (fun t => realize.map t ≫ w) (by ext; rfl :
      RDCpx.ofInclusion (P := (v.shape.boundary (P.dimension - 1) (!ε)).rdc)
        (Q := (invertorShape P ε hd).rdc) (v.shape.boundaryIncl _ (!ε) ≫ gB) =
      v.shape.boundaryInclRDC _ (!ε) ≫ RDCpx.ofInclusion (P := v.shape.rdc)
        (Q := (invertorShape P ε hd).rdc) gB)).trans
      ((realize.map_comp_assoc _ _ _).trans (congrArg (realize.map _ ≫ ·) hv))
  · rw [map_comp, map_comp, u.shape.map_boundaryIncl_top, v.shape.map_boundaryIncl_top,
      map_boundary, map_boundary]
    exact h₂.symm.trans h₁

theorem equiv_invertor_boundary_not_eps (w : realize.obj (invertorShape P ε hd).rdc ⟶ X)
    (u v : PastingDiagram X) (gA : u.shape.ogp ⟶ (invertorShape P ε hd).ogp)
    (gB : v.shape.ogp ⟶ (invertorShape P ε hd).ogp) [IsInclusion gA] [IsInclusion gB]
    (hu : realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (invertorShape P ε hd).rdc)
      gA) ≫ w = u.map)
    (hv : realize.map (RDCpx.ofInclusion (P := v.shape.rdc) (Q := (invertorShape P ε hd).rdc)
      gB) ≫ w = v.map)
    (hA : OGP.map gA ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) (!ε) ⊤))
    (hB : OGP.map gB ⊤ =
      OGP.map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) ε ⊤))
    (h : (cond ε u v).Pastable (cond ε v u) (P.dimension - 1)) :
    ((⟨invertorShape P ε hd, w⟩ : PastingDiagram X).boundary P.dimension (!ε)).Equiv
      ((cond ε u v).paste (cond ε v u) (P.dimension - 1) h) := by
  have hp := isPastingIn_invertorShape_cond P ε hd gA gB hA hB
  rw [← (invertorShape P ε hd).map_boundaryIncl_top] at hp
  cases ε
  · exact .symm (equiv_paste_of_emb v u _ _ h w _ gB gA rfl hv hu hp)
  · exact .symm (equiv_paste_of_emb u v _ _ h w _ gA gB rfl hu hv hp)

end Invertor

theorem boundary_invertor_unit (u : PastingDiagram X) (hu : u.IsDegenerate) (hr : u.IsRound)
    (α : Bool) :
    ((u.invertor hu α).boundary u.dim (!α)).Equiv (u.boundary (u.dim - 1) α).unit := by
  have hd := shape_dimension_pos hu
  have hr : u.shape.IsRound := hr
  have h := equiv_invertor_boundary_eps u.shape (!α) hd hr (u.invertor hu α).map u.map (by
    change realize.map (RDCpx.ofInclusion
          (P := (unitShape (u.shape.boundary (u.shape.dimension - 1) (!!α))).rdc)
          (Q := (invertorShape u.shape (!α) hd).rdc) (invertorUnitEmb u.shape (!α) hd hr)) ≫
          realize.map (invertorProj u.shape (!α) hd hu.factorization.proj
            hu.factorization.dim_lt) ≫ hu.factorization.map = _
    rw [← realize.map_comp_assoc]
    refine (congrArg (fun t => realize.map t ≫ hu.factorization.map)
      (embHom_invertorUnitEmb_comp_invertorProj u.shape (!α) hd hr hu.factorization.proj
        hu.factorization.dim_lt)).trans ?_
    rw [realize.map_comp, realize.map_comp, Category.assoc, Category.assoc,
      hu.factorization.comp_eq]
    rfl)
  rwa [Bool.not_not] at h

theorem boundary_invertor_composite (u : PastingDiagram X) (hu : u.IsDegenerate) (α : Bool) :
    ∃ h : (cond α (u.reverse hu) u).Pastable (cond α u (u.reverse hu)) (u.dim - 1),
      ((u.invertor hu α).boundary u.dim α).Equiv
        ((cond α (u.reverse hu) u).paste (cond α u (u.reverse hu)) (u.dim - 1) h) := by
  have hd := shape_dimension_pos hu
  have hNot (ε : Bool) : realize.map (RDCpx.ofInclusion (P := u.shape.rdc)
      (Q := (invertorShape u.shape ε hd).rdc) (invertorEndpointNot u.shape ε hd)) ≫
      realize.map (invertorProj u.shape ε hd hu.factorization.proj hu.factorization.dim_lt) ≫
        hu.factorization.map = u.map :=
    (realize.map_comp_assoc _ _ _).symm.trans
      ((congrArg (fun t => realize.map t ≫ hu.factorization.map)
        (embHom_invertorEndpointNot_comp_invertorProj u.shape ε hd _ _)).trans
        hu.factorization.comp_eq)
  have hDual (ε : Bool) : realize.map (RDCpx.ofInclusion
      (P := (u.shape.dual (OGP.topDim u.shape.dimension)).rdc)
      (Q := (invertorShape u.shape ε hd).rdc) (invertorEndpointDual u.shape ε hd)) ≫
      realize.map (invertorProj u.shape ε hd hu.factorization.proj hu.factorization.dim_lt) ≫
        hu.factorization.map = (u.reverse hu).map :=
    (realize.map_comp_assoc _ _ _).symm.trans
      (congrArg (fun t => realize.map t ≫ hu.factorization.map)
        (embHom_invertorEndpointDual_comp_invertorProj u.shape ε hd _ _))
  have h : (cond α (u.reverse hu) u).Pastable (cond α u (u.reverse hu)) (u.dim - 1) :=
    Pastable.of_side α (boundary_reverse u hu α) (by rw [dim_reverse, dim_def]; omega)
      (by rw [dim_def]; omega)
  have e := equiv_invertor_boundary_not_eps u.shape (!α) hd _ u (u.reverse hu)
    (invertorEndpointNot u.shape (!α) hd) (invertorEndpointDual u.shape (!α) hd) (hNot _)
    (hDual _) (image_invertorEndpointNot _ _ _) (image_invertorEndpointDual _ _ _)
    (by simpa only [Bool.cond_not, dim_def] using h)
  exact ⟨h, by simpa only [invertor, Bool.not_not, Bool.cond_not, dim_def] using e⟩

end Atoms.Diagrammatic.PastingDiagram
