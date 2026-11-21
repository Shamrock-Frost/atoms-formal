import Atoms.Molecule.MoleculeShape.Dual
import Atoms.Molecule.Cylinder.PartialMolecule
import Atoms.Molecule.Rigidity

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

instance instFinEnumPartialCylinder (U : OGP.{u}) [FinEnum U] (K : LowerSet U)
    [DecidablePred (· ∈ K)] : FinEnum (partialCylinder U K) :=
  letI : FinEnum Bool := FinEnum.ofList [false, true] (by intro b; cases b <;> simp)
  letI : FinEnum ArrowElt := FinEnum.insertNone Bool (Fin.last _)
  inferInstanceAs (FinEnum ({x : U // x ∈ K} ⊕
    (ULift.{u} ArrowElt × {x : U // x ∉ K})))

variable (U : OGP.{u}) (K : LowerSet U) in
transfer_instances partialCylinder U K with DecidableLE

namespace PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U}

def swapEnds : PartialCylinderCarrier U K → PartialCylinderCarrier U K
  | Sum.inl x => Sum.inl x
  | Sum.inr p => Sum.inr (⟨p.1.down.map not⟩, p.2)

theorem swapEnds_swapEnds (a : PartialCylinderCarrier U K) : swapEnds (swapEnds a) = a := by
  rcases a with x | ⟨⟨_ | β⟩, x⟩
  · rfl
  · rfl
  · exact congrArg Sum.inr (Prod.ext (ULift.ext _ _ (congrArg some (Bool.not_not β))) rfl)

variable (U K) in
def dualTopIso : dual (partialCylinder U K) ⊤ ≅ partialCylinder (dual U ⊤) K :=
  isoMk ⟨⟨swapEnds (U := U) (K := K), swapEnds (U := U) (K := K), swapEnds_swapEnds,
    fun a => swapEnds_swapEnds (U := U) (K := K) a⟩, fun {a b} => by
      rcases a with x | ⟨⟨i⟩, x⟩ <;> rcases b with y | ⟨⟨j⟩, y⟩
      · exact Iff.rfl
      · exact Iff.rfl
      · exact Iff.rfl
      · refine and_congr_left fun _ => ?_
        change i.map not = j.map not ∨ j.map not = none ↔ i = j ∨ j = none
        rw [(Option.map_injective fun a b (h : (!a) = !b) => by simpa using h).eq_iff,
          Option.map_eq_none_iff]⟩ fun {a b} h => by
    rw [orient_dual]
    rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩ <;> rcases b with ⟨y, hy⟩ | ⟨⟨_ | γ⟩, ⟨y, hy⟩⟩
    all_goals first
      | rfl
      | exact (PartialCylinderCarrier.not_covBy_inl_inr_none h).elim
      | (simp only [Pi.top_apply, top_eq_true, Bool.true_xor]; rfl)
      | (have hyx := PartialCylinderCarrier.proj_covBy_of_covBy_inr_none h
         refine (orient_mkI_none_mkI_none (U := dual U ⊤) hx hy hyx _).trans ?_
         rw [orient_mkI_none_mkI_none hx hy hyx h, orient_dual]
         simp only [Pi.top_apply, top_eq_true, Bool.true_xor])

@[simp] theorem dualTopIso_hom_apply (a : dual (partialCylinder U K) ⊤) :
    (dualTopIso U K).hom a = swapEnds a :=
  rfl

end PartialCylinder

end Atoms.Molecule.OGP

namespace Atoms.Molecule

open OGP

def cylShape (P : MoleculeShape) (K : LowerSet P.ogp) [DecidablePred (· ∈ K)] :
    MoleculeShape :=
  .ofOGP (partialCylinder P.ogp K) (isMolecule_partialCylinder P.isMolecule K)

def cylShapeIso (P : MoleculeShape) (K : LowerSet P.ogp) [DecidablePred (· ∈ K)] :
    partialCylinder P.ogp K ≅ (cylShape P K).ogp :=
  FiniteOGP.ofOGPIso _

section Cylinder

variable (P : MoleculeShape) (K : LowerSet P.ogp) [DecidablePred (· ∈ K)]

def cylProj : (cylShape P K).rdc ⟶ P.rdc :=
  (RDCpx.isoOfIso (P := ⟨⟨partialCylinder P.ogp K,
      isRDC_of_isMolecule (isMolecule_partialCylinder P.isMolecule K)⟩⟩)
    (Q := (cylShape P K).rdc) (cylShapeIso P K)).inv ≫
    ⟨ConcreteCategory.ofHom (C := RDCpxDown.{0})
      (X := ⟨partialCylinder P.ogp K,
        isRDC_of_isMolecule (isMolecule_partialCylinder P.isMolecule K)⟩)
      (Y := P.rdc.obj)
      ⟨partialCylinderProj P.ogp K, isMap_partialCylinderProj P.isMolecule K⟩,
      functor_isFibered_partialCylinderProj P.ogp K⟩

def cylEndpoint (α : Bool) : P.ogp ⟶ (cylShape P K).ogp :=
  partialCylinderEndpoint P.ogp K α ≫ (cylShapeIso P K).hom

instance (α : Bool) : IsInclusion (cylEndpoint P K α) :=
  ⟨IsInclusion.injective (f := partialCylinderEndpoint P.ogp K α ≫ (cylShapeIso P K).hom)⟩

theorem cylProj_cylEndpoint (α : Bool) (x : P.ogp) :
    ConcreteCategory.hom (cylProj P K).hom (cylEndpoint P K α x) = x :=
  (congrArg (partialCylinderProj P.ogp K)
    (Iso.hom_inv_id_apply (cylShapeIso P K)
      (partialCylinderEndpoint P.ogp K α x))).trans
    (partialCylinderProj_endpoint P.ogp K α x)

theorem ofInclusion_cylEndpoint_comp_cylProj (α : Bool) :
    @RDCpx.ofInclusion P.rdc (cylShape P K).rdc (cylEndpoint P K α)
      (inferInstanceAs (IsInclusion (cylEndpoint P K α))) ≫ cylProj P K = 𝟙 P.rdc := by
  ext x
  exact cylProj_cylEndpoint P K α x

theorem surjective_cylProj : Function.Surjective (ConcreteCategory.hom (cylProj P K).hom) :=
  fun x => ⟨cylEndpoint P K false x, cylProj_cylEndpoint P K false x⟩

theorem dimension_cylShape (hKU : ∃ x, x ∉ K ∧ grade ℕ x = P.dimension) :
    (cylShape P K).dimension = P.dimension + 1 := by
  have h := (MoleculeShape.dimension_ofOGP (partialCylinder P.ogp K)
    (isMolecule_partialCylinder P.isMolecule K)).trans
    (krullDim_partialCylinder P.krullDim_eq_dimension hKU)
  exact_mod_cast h

theorem isRound_cylShape (hP : P.IsRound) (hKU : K ≤ P.ogp.bdryFull ⊤) :
    (cylShape P K).IsRound :=
  MoleculeShape.isRound_ofOGP _ _ (isRound_partialCylinder hP hKU)

theorem map_cylEndpoint_top (hd : 0 < P.dimension) {β : Bool}
    (hsub : P.ogp.boundary ⊤ (P.dimension - 1) (!β) ≤ K) :
    map (cylEndpoint P K β) ⊤ =
      (cylShape P K).ogp.boundary ⊤ P.dimension β := by
  rw [cylEndpoint, map_comp,
    map_endpoint_eq_boundary_dimension K P.isMolecule P.krullDim_eq_dimension hd hsub,
    map_boundary, map_top_of_isIso]

end Cylinder

section UnitShape

abbrev unitShape (P : MoleculeShape) : MoleculeShape :=
  cylShape P (P.ogp.bdryFull ⊤)

theorem map_cylEndpoint_bdryFull_top (P : MoleculeShape) (α : Bool) :
    map (cylEndpoint P (P.ogp.bdryFull ⊤) α) ⊤ =
      (unitShape P).ogp.boundary ⊤ P.dimension α := by
  rcases Nat.eq_zero_or_pos P.dimension with h0 | hpos
  · have hd0 : krullDim P.ogp ≤ 0 := P.krullDim_eq_dimension.le.trans (by rw [h0]; rfl)
    rw [cylEndpoint, map_comp, h0, map_endpoint_eq_boundary_zero hd0 α,
      map_boundary, map_top_of_isIso]
  · exact map_cylEndpoint_top P (P.ogp.bdryFull ⊤) hpos (by
      have hd := P.krullDim_top_eq (Nat.sub_add_cancel hpos).symm
      rw [← bdry_eq_boundary hd]
      exact bdry_le_bdryFull ⊤ (!α))

def unitShapeIsoOfIso {P Q : MoleculeShape} (ψ : P.ogp ≅ Q.ogp) :
    (unitShape P).ogp ≅ (unitShape Q).ogp :=
  (cylShapeIso P (P.ogp.bdryFull ⊤)).symm ≪≫
    PartialCylinder.isoOfIso _ _ ψ (fun x => by
      rw [← map_top_of_isIso ψ.hom, ← map_bdryFull, apply_mem_map_iff]) ≪≫
    cylShapeIso Q (Q.ogp.bdryFull ⊤)

theorem isoOfIso_unitShapeIsoOfIso_comp_cylProj {P Q : MoleculeShape} (ψ : P.ogp ≅ Q.ogp) :
    (RDCpx.isoOfIso (P := (unitShape P).rdc) (Q := (unitShape Q).rdc) (unitShapeIsoOfIso ψ)).hom ≫
      cylProj Q (Q.ogp.bdryFull ⊤) =
        cylProj P (P.ogp.bdryFull ⊤) ≫ (RDCpx.isoOfIso (P := P.rdc) (Q := Q.rdc) ψ).hom := by
  ext x
  exact (congrArg (partialCylinderProj Q.ogp (Q.ogp.bdryFull ⊤))
    (Iso.hom_inv_id_apply (cylShapeIso Q (Q.ogp.bdryFull ⊤)) _)).trans
    (PartialCylinder.proj_carrierMapOfMap _ _ ψ.hom (fun y => by
      rw [← map_top_of_isIso ψ.hom, ← map_bdryFull, apply_mem_map_iff]) _)

private theorem dualIso_mem_bdryFull_iff (P : MoleculeShape) (x : OGP.dual P.ogp ⊤) :
    (P.dualIso ⊤).hom x ∈ (P.dual ⊤).ogp.bdryFull ⊤ ↔ x ∈ P.ogp.bdryFull ⊤ := by
  rw [← map_top_of_isIso (P.dualIso ⊤).hom, ← map_bdryFull, apply_mem_map_iff, bdryFull_dual]

def unitShapeDualIso (P : MoleculeShape) :
    ((unitShape P).dual ⊤).ogp ≅ (unitShape (P.dual ⊤)).ogp :=
  ((unitShape P).dualIso ⊤).symm ≪≫ (OGP.dualFunctor ⊤).mapIso (cylShapeIso P _).symm ≪≫
    PartialCylinder.dualTopIso P.ogp _ ≪≫
    PartialCylinder.isoOfIso _ _ (P.dualIso ⊤) (dualIso_mem_bdryFull_iff P) ≪≫
    cylShapeIso (P.dual ⊤) _

theorem isoOfIso_unitShapeDualIso_comp_cylProj (P : MoleculeShape) :
    (RDCpx.isoOfIso (P := ((unitShape P).dual ⊤).rdc) (Q := (unitShape (P.dual ⊤)).rdc)
        (unitShapeDualIso P)).hom ≫ cylProj (P.dual ⊤) ((P.dual ⊤).ogp.bdryFull ⊤) ≫
      (RDCpx.isoOfIso (P := (P.dual ⊤).rdc) (Q := (RDCpx.dualFunctor ⊤).obj P.rdc)
        (P.dualIso ⊤).symm).hom =
    (RDCpx.isoOfIso (P := ((unitShape P).dual ⊤).rdc)
        (Q := (RDCpx.dualFunctor ⊤).obj (unitShape P).rdc) ((unitShape P).dualIso ⊤).symm).hom ≫
      (RDCpx.dualFunctor ⊤).map (cylProj P (P.ogp.bdryFull ⊤)) := by
  ext x
  change (P.dualIso ⊤).inv (partialCylinderProj (P.dual ⊤).ogp ((P.dual ⊤).ogp.bdryFull ⊤)
    ((cylShapeIso (P.dual ⊤) ((P.dual ⊤).ogp.bdryFull ⊤)).inv ((unitShapeDualIso P).hom x))) =
    partialCylinderProj P.ogp (P.ogp.bdryFull ⊤)
      ((cylShapeIso P (P.ogp.bdryFull ⊤)).inv (((unitShape P).dualIso ⊤).inv x))
  have e : (unitShapeDualIso P).hom x = (cylShapeIso (P.dual ⊤) ((P.dual ⊤).ogp.bdryFull ⊤)).hom
      ((PartialCylinder.dualTopIso P.ogp (P.ogp.bdryFull ⊤) ≪≫
        PartialCylinder.isoOfIso _ _ (P.dualIso ⊤) (dualIso_mem_bdryFull_iff P)).hom
        ((cylShapeIso P (P.ogp.bdryFull ⊤)).inv (((unitShape P).dualIso ⊤).inv x))) :=
    rfl
  rw [e, Iso.hom_inv_id_apply, Iso.trans_hom, ConcreteCategory.comp_apply,
    PartialCylinder.isoOfIso_hom_apply, PartialCylinder.proj_carrierMapOfMap,
    Iso.hom_inv_id_apply, PartialCylinder.dualTopIso_hom_apply]
  generalize (cylShapeIso P (P.ogp.bdryFull ⊤)).inv (((unitShape P).dualIso ⊤).inv x) = y
  rcases y with y | y <;> rfl

theorem cylEndpoint_bdryFull_apply_of_iso {P : MoleculeShape} {k : ℕ}
    (hk : P.dimension = k) (β : Bool) (ψ : ((unitShape P).boundary k β).ogp ≅ P.ogp)
    (b : ((unitShape P).boundary k β).ogp) :
    cylEndpoint P (P.ogp.bdryFull ⊤) β (ψ.hom b) =
      (unitShape P).boundaryIncl k β b := by
  subst hk
  exact ((unitShape P).boundary P.dimension β).isMolecule.eqOn_of_map_eq
    (ψ.hom ≫ cylEndpoint P (P.ogp.bdryFull ⊤) β) ((unitShape P).boundaryIncl P.dimension β)
    (by rw [map_comp, map_top_of_isIso, map_cylEndpoint_bdryFull_top,
      MoleculeShape.map_boundaryIncl_top])
    (LowerSet.mem_top (a := b))

theorem isAtom_unitShape_of_dimension_eq_zero (P : MoleculeShape) (h0 : P.dimension = 0) :
    IsAtom (unitShape P).ogp := by
  have hd : krullDim (⊤ : LowerSet P.ogp) = 0 := by
    rw [LowerSet.krullDim_top, P.krullDim_eq_dimension, h0, Nat.cast_zero]
  obtain ⟨x, -, -⟩ := P.isMolecule.exists_eq_Iic_of_krullDim_eq_zero hd
  have hnot : x ∉ P.ogp.bdryFull ⊤ := by
    rw [bdryFull_eq_bot hd.le]
    exact LowerSet.notMem_bot
  refine ⟨(unitShape P).isMolecule, (cylShapeIso P (P.ogp.bdryFull ⊤)).hom
    (PartialCylinder.mkI (P.ogp.bdryFull ⊤) none x hnot), le_antisymm (fun a _ => ?_) le_top⟩
  rw [SetLike.mem_coe, LowerSet.mem_Iic_iff,
    ← Iso.inv_hom_id_apply (cylShapeIso P (P.ogp.bdryFull ⊤)) a]
  exact (isMorphism (cylShapeIso P (P.ogp.bdryFull ⊤)).hom).monotone
    (PartialCylinder.le_mkI_none_of_proj_le hnot
      ((P.subsingleton_of_dimension_eq_zero h0).elim _ x).le)

end UnitShape

end Atoms.Molecule
