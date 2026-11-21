import Atoms.Molecule.MoleculeShape.PartialCylinder
import Atoms.Molecule.Cylinder.InvertedCartesian

universe u

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

section Invertor

def invertorShape (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) : MoleculeShape :=
  .ofOGP (invertedCylinder P.ogp (P.ogp.bdry ⊤ ε) ε P.dimension)
    (InvertedCylinder.isMolecule_invertedCylinder P.isMolecule P.krullDim_eq_dimension hd le_rfl)

def invertorShapeIso (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    invertedCylinder P.ogp (P.ogp.bdry ⊤ ε) ε P.dimension ≅ (invertorShape P ε hd).ogp :=
  FiniteOGP.ofOGPIso _

def invertorProj (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) {Q : RDCpx.{0}}
    (p : P.rdc ⟶ Q) (hQ : krullDim Q.obj.toOGP < P.dimension) :
    (invertorShape P ε hd).rdc ⟶ Q :=
  haveI : (ConcreteCategory.hom p.hom).isMap.monotone.functor.IsFibered := p.property
  let rdcInv : RDCpxDown.{0} := ⟨invertedCylinder P.ogp (P.ogp.bdry ⊤ ε) ε P.dimension,
    isRDC_of_isMolecule (InvertedCylinder.isMolecule_invertedCylinder P.isMolecule
      P.krullDim_eq_dimension hd le_rfl)⟩
  (RDCpx.isoOfIso (P := ⟨rdcInv⟩) (Q := (invertorShape P ε hd).rdc)
      (invertorShapeIso P ε hd)).inv ≫
    ⟨ConcreteCategory.ofHom (C := RDCpxDown.{0}) (X := rdcInv) (Y := Q.obj)
      ⟨fun x => ConcreteCategory.hom p.hom (partialCylinderProj P.ogp (P.ogp.bdry ⊤ ε) x),
        InvertedCylinder.isMap_comp_invertedProj P.isMolecule P.krullDim_eq_dimension hd le_rfl
          (ConcreteCategory.hom p.hom).isMap hQ⟩,
      InvertedCylinder.functor_isFibered_comp_invertedProj
        (ConcreteCategory.hom p.hom).isMap.monotone _⟩

def invertorEndpointNot (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    P.ogp ⟶ (invertorShape P ε hd).ogp :=
  InvertedCylinder.endpointNot P.ogp (P.ogp.bdry ⊤ ε) ε P.dimension ≫
    (invertorShapeIso P ε hd).hom

instance (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    IsInclusion (invertorEndpointNot P ε hd) :=
  ⟨IsInclusion.injective
    (f := InvertedCylinder.endpointNot P.ogp (P.ogp.bdry ⊤ ε) ε P.dimension ≫
      (invertorShapeIso P ε hd).hom)⟩

def invertorEndpointDual (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    (P.dual (OGP.topDim P.dimension)).ogp ⟶ (invertorShape P ε hd).ogp :=
  (P.dualIso (OGP.topDim P.dimension)).inv ≫
    InvertedCylinder.endpointDual P.ogp (P.ogp.bdry ⊤ ε) ε (fun _ hz => by
      have h := grade_lt_of_mem_bdry hz
      rw [LowerSet.krullDim_top, P.krullDim_eq_dimension] at h
      exact_mod_cast h) ≫
    (invertorShapeIso P ε hd).hom

instance (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    IsInclusion (invertorEndpointDual P ε hd) :=
  ⟨IsInclusion.injective (f := (P.dualIso (OGP.topDim P.dimension)).inv ≫
    InvertedCylinder.endpointDual P.ogp (P.ogp.bdry ⊤ ε) ε _ ≫
    (invertorShapeIso P ε hd).hom)⟩

theorem invertorEndpointNot_apply (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)
    (x : P.ogp) :
    invertorEndpointNot P ε hd x = (invertorShapeIso P ε hd).hom
      (partialCylinderEndpoint P.ogp (P.ogp.bdry ⊤ ε) (!ε) x) :=
  rfl

theorem invertorEndpointNot_mem_std (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)
    (x : P.ogp) :
    (invertorShapeIso P ε hd).inv (invertorEndpointNot P ε hd x) ∈
      InvertedCylinder.std (P.ogp.bdry ⊤ ε) ε P.dimension := by
  rw [invertorEndpointNot_apply, Iso.hom_inv_id_apply]
  exact InvertedCylinder.endpoint_notMem_std x

theorem proj_invertorShapeIso_symm_invertorEndpointNot (P : MoleculeShape) (ε : Bool)
    (hd : 0 < P.dimension) (x : P.ogp) :
    partialCylinderProj P.ogp (P.ogp.bdry ⊤ ε)
      ((invertorShapeIso P ε hd).inv (invertorEndpointNot P ε hd x)) = x := by
  rw [invertorEndpointNot_apply, Iso.hom_inv_id_apply, partialCylinderProj_endpoint]

theorem embHom_invertorEndpointNot_comp_invertorProj (P : MoleculeShape) (ε : Bool)
    (hd : 0 < P.dimension) {Q : RDCpx.{0}} (p : P.rdc ⟶ Q)
    (hQ : krullDim Q.obj.toOGP < P.dimension) :
    @RDCpx.ofInclusion P.rdc (invertorShape P ε hd).rdc (invertorEndpointNot P ε hd)
      (inferInstanceAs (IsInclusion (invertorEndpointNot P ε hd))) ≫
      invertorProj P ε hd p hQ = p := by
  ext x
  exact congrArg (ConcreteCategory.hom p.hom)
    (proj_invertorShapeIso_symm_invertorEndpointNot P ε hd x)

theorem embHom_invertorEndpointDual_comp_invertorProj (P : MoleculeShape) (ε : Bool)
    (hd : 0 < P.dimension) {Q : RDCpx.{0}} (p : P.rdc ⟶ Q)
    (hQ : krullDim Q.obj.toOGP < P.dimension) :
    @RDCpx.ofInclusion (P.dual (OGP.topDim P.dimension)).rdc
        (invertorShape P ε hd).rdc (invertorEndpointDual P ε hd)
        (inferInstanceAs (IsInclusion (invertorEndpointDual P ε hd))) ≫
        invertorProj P ε hd p hQ =
      P.dualLift p (fun x => decide_eq_false_iff_not.2
        (by exact_mod_cast ((grade_le_krullDim x).trans_lt hQ).ne)) := by
  ext x
  exact congrArg (ConcreteCategory.hom p.hom)
    ((congrArg (partialCylinderProj _ _)
      (Iso.hom_inv_id_apply (invertorShapeIso P ε hd) _)).trans
      (partialCylinderProj_endpoint _ _ _ _))

theorem apply_boundaryEmb_mem_bdry_iff (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)
    (hr : P.IsRound) (x : (P.boundary (P.dimension - 1) (!ε)).ogp) :
    P.boundaryIncl (P.dimension - 1) (!ε) x ∈ P.ogp.bdry ⊤ ε ↔
      x ∈ (P.boundary (P.dimension - 1) (!ε)).ogp.bdryFull ⊤ := by
  have htop := P.krullDim_top_eq (Nat.sub_add_cancel hd).symm
  have hι := P.map_boundaryIncl_top (P.dimension - 1) (!ε)
  have hx : P.boundaryIncl (P.dimension - 1) (!ε) x ∈
      P.ogp.boundary ⊤ (P.dimension - 1) (!ε) :=
    hι ▸ ⟨x, LowerSet.mem_top, rfl⟩
  rw [bdry_eq_boundary htop,
    show P.boundaryIncl (P.dimension - 1) (!ε) x ∈ P.ogp.boundary ⊤ (P.dimension - 1) ε ↔
      P.boundaryIncl (P.dimension - 1) (!ε) x ∈
        P.ogp.boundary ⊤ (P.dimension - 1) (!ε) ⊓ P.ogp.boundary ⊤ (P.dimension - 1) (!!ε) by
      rw [Bool.not_not, LowerSet.mem_inf_iff, and_iff_right hx],
    hr.inf_boundary_eq_properBoundary P.isMolecule
      (by rw [htop]; exact_mod_cast Nat.lt_succ_self _) (!ε),
    (P.isMolecule.boundary (P.dimension - 1) (!ε)).properBoundary_eq_bdryFull,
    ← hι, ← map_bdryFull, apply_mem_map_iff]

def invertorUnitEmb (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) (hr : P.IsRound) :
    (unitShape (P.boundary (P.dimension - 1) (!ε))).ogp ⟶ (invertorShape P ε hd).ogp :=
  (cylShapeIso _ _).inv ≫
    InvertedCylinder.embOfStd
      (PartialCylinder.embOfEmb (P.ogp.bdry ⊤ ε)
        ((P.boundary (P.dimension - 1) (!ε)).ogp.bdryFull ⊤)
        (P.boundaryIncl (P.dimension - 1) (!ε)) (apply_boundaryEmb_mem_bdry_iff P ε hd hr))
      (InvertedCylinder.embOfEmb_mem_std (P.ogp.bdry ⊤ ε) ε P.dimension
        ((P.boundary (P.dimension - 1) (!ε)).ogp.bdryFull ⊤)
        (P.boundaryIncl (P.dimension - 1) (!ε)) (apply_boundaryEmb_mem_bdry_iff P ε hd hr)
        fun x => by
          have hx : P.boundaryIncl (P.dimension - 1) (!ε) x ∈
              P.ogp.boundary ⊤ (P.dimension - 1) (!ε) :=
            P.map_boundaryIncl_top (P.dimension - 1) (!ε) ▸ ⟨x, LowerSet.mem_top, rfl⟩
          have := grade_le_of_mem_boundary hx
          omega) ≫
    (invertorShapeIso P ε hd).hom

instance (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) (hr : P.IsRound) :
    IsInclusion (invertorUnitEmb P ε hd hr) :=
  ⟨IsInclusion.injective (f := (cylShapeIso _ _).inv ≫
    InvertedCylinder.embOfStd _ _ ≫ (invertorShapeIso P ε hd).hom)⟩

theorem proj_invertorShapeIso_symm_invertorUnitEmb (P : MoleculeShape) (ε : Bool)
    (hd : 0 < P.dimension) (hr : P.IsRound)
    (y : (unitShape (P.boundary (P.dimension - 1) (!ε))).ogp) :
    partialCylinderProj P.ogp (P.ogp.bdry ⊤ ε)
        ((invertorShapeIso P ε hd).inv (invertorUnitEmb P ε hd hr y)) =
      P.boundaryIncl (P.dimension - 1) (!ε) (ConcreteCategory.hom (cylProj _ _).hom y) :=
  (congrArg (partialCylinderProj _ _)
    (Iso.hom_inv_id_apply (invertorShapeIso P ε hd) _)).trans
    (PartialCylinder.proj_carrierMapOfMap _ _ _ (apply_boundaryEmb_mem_bdry_iff P ε hd hr) _)

theorem embHom_invertorUnitEmb_comp_invertorProj (P : MoleculeShape) (ε : Bool)
    (hd : 0 < P.dimension) (hr : P.IsRound) {Q : RDCpx.{0}} (p : P.rdc ⟶ Q)
    (hQ : krullDim Q.obj.toOGP < P.dimension) :
    @RDCpx.ofInclusion (unitShape (P.boundary (P.dimension - 1) (!ε))).rdc
        (invertorShape P ε hd).rdc (invertorUnitEmb P ε hd hr)
        (inferInstanceAs (IsInclusion (invertorUnitEmb P ε hd hr))) ≫
        invertorProj P ε hd p hQ =
      cylProj _ _ ≫
        @RDCpx.ofInclusion (P.boundary (P.dimension - 1) (!ε)).rdc P.rdc
          (P.boundaryIncl (P.dimension - 1) (!ε))
          (inferInstanceAs (IsInclusion (P.boundaryIncl (P.dimension - 1) (!ε)))) ≫ p := by
  ext y
  exact congrArg (ConcreteCategory.hom p.hom)
    (proj_invertorShapeIso_symm_invertorUnitEmb P ε hd hr y)

theorem image_invertorUnitEmb (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)
    (hr : P.IsRound) :
    map (invertorUnitEmb P ε hd hr) ⊤ =
      (invertorShape P ε hd).ogp.boundary ⊤ P.dimension ε := by
  have he : P.dimension = P.dimension - 1 + 1 := (Nat.sub_add_cancel hd).symm
  have htop := P.krullDim_top_eq he
  have hUle (w : P.ogp) : grade ℕ w ≤ P.dimension - 1 + 1 :=
    he ▸ krullDim_le_coe_iff.1 P.krullDim_eq_dimension.le w
  have hKU := bdry_eq_boundary htop ε
  rw [invertorUnitEmb, map_comp, map_comp, map_top_of_isIso, InvertedCylinder.map_embOfStd,
    PartialCylinder.map_embOfEmb_top, P.map_boundaryIncl_top,
    ← InvertedCylinder.boundary_over_top_eps hUle (InvertedCylinder.dim_lt_of_mem_K hKU.le)
      (InvertedCylinder.orient_eq_of_mem_K hKU.le), PartialCylinder.over_top,
    ← he, map_boundary, map_top_of_isIso]

theorem image_invertorEndpointNot (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    map (invertorEndpointNot P ε hd) ⊤ =
      map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) (!ε) ⊤) := by
  rw [invertorEndpointNot, map_comp, InvertedCylinder.map_endpointNot]

theorem image_invertorEndpointDual (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    map (invertorEndpointDual P ε hd) ⊤ =
      map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) ε ⊤) := by
  rw [invertorEndpointDual, map_comp, map_comp, map_top_of_isIso,
    InvertedCylinder.map_endpointDual]

theorem isPastingIn_invertorShape (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension) :
    (invertorShape P ε hd).ogp.IsPastingIn (P.dimension - 1)
      (map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) false ⊤))
      (map (invertorShapeIso P ε hd).hom (PartialCylinder.copy (P.ogp.bdry ⊤ ε) true ⊤))
      ((invertorShape P ε hd).ogp.boundary ⊤ P.dimension (!ε)) := by
  have he : P.dimension = P.dimension - 1 + 1 := (Nat.sub_add_cancel hd).symm
  have htop := P.krullDim_top_eq he
  have hUle (w : P.ogp) : grade ℕ w ≤ P.dimension - 1 + 1 :=
    he ▸ krullDim_le_coe_iff.1 P.krullDim_eq_dimension.le w
  have hp := InvertedCylinder.isPastingIn_copy_copy (ε := ε) hUle (bdry_eq_boundary htop ε)
  rw [← he] at hp
  have h := (isPastingIn_map_iff (invertorShapeIso P ε hd).hom (P.dimension - 1) _ _ _).2 hp
  rwa [map_boundary, map_top_of_isIso] at h

theorem surjective_invertorProj (P : MoleculeShape) (ε : Bool) (hd : 0 < P.dimension)
    {Q : RDCpx.{0}} (p : P.rdc ⟶ Q) (hQ : krullDim Q.obj.toOGP < P.dimension)
    (hp : Function.Surjective (ConcreteCategory.hom p.hom)) :
    Function.Surjective (ConcreteCategory.hom (invertorProj P ε hd p hQ).hom) := by
  intro y
  obtain ⟨x, rfl⟩ := hp y
  exact ⟨invertorEndpointNot P ε hd x,
    congrArg (ConcreteCategory.hom p.hom)
      (proj_invertorShapeIso_symm_invertorEndpointNot P ε hd x)⟩

end Invertor

end Atoms.Molecule
