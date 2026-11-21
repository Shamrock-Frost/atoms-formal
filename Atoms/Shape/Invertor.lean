import Atoms.Shape.MarkedHorn
import Atoms.Molecule.Cylinder.InvertedHorn
import Atoms.Molecule.MoleculeShape.InvertedCylinder

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Set

namespace Atoms.Shape

section InvertorAtom

variable (V : Atom) (ε : Bool) (hV : 0 < V.dimension)

@[implicit_reducible] def invertorAtom : Atom :=
  Atom.ofIsAtom (invertorShape V.toMoleculeShape ε hV).toFiniteOGP
    ((isAtom_iff_of_iso (invertorShapeIso V.toMoleculeShape ε hV)).1
      (InvertedCylinder.isAtom_invertedCylinder V.isAtom V.krullDim_eq_dimension hV le_rfl))

def invertorAtomIso :
    invertedCylinder V.ogp (V.ogp.bdry ⊤ ε) ε V.dimension ≅ (invertorAtom V ε hV).ogp :=
  invertorShapeIso V.toMoleculeShape ε hV

theorem top_notMem_bdry : V.top ∉ V.ogp.bdry ⊤ ε :=
  InvertedCylinder.top_notMem_K le_rfl V.le_top

def invertorTopElt (i : ArrowElt) : (invertorAtom V ε hV).ogp :=
  (invertorAtomIso V ε hV).hom
    (PartialCylinder.mkI (V.ogp.bdry ⊤ ε) i V.top (top_notMem_bdry V ε))

theorem le_invertorTopElt_none (x : (invertorAtom V ε hV).ogp) :
    x ≤ invertorTopElt V ε hV none := by
  rw [← Iso.inv_hom_id_apply (invertorAtomIso V ε hV) x]
  exact (isMorphism (invertorAtomIso V ε hV).hom).monotone
    (InvertedCylinder.le_mkI_none_top le_rfl V.le_top _)

theorem invertorAtom_top : (invertorAtom V ε hV).top = invertorTopElt V ε hV none :=
  le_antisymm (le_invertorTopElt_none V ε hV _) ((invertorAtom V ε hV).le_top _)

theorem dimension_invertorAtom :
    (invertorAtom V ε hV).dimension = V.dimension + 1 := by
  rw [(invertorAtom V ε hV).dimension_eq, invertorAtom_top, invertorTopElt,
    (isMorphism (invertorAtomIso V ε hV).hom).grade_eq]
  exact congrArg (· + 1) V.dimension_eq.symm

theorem dim_invertorTopElt_some (β : Bool) :
    grade ℕ (invertorTopElt V ε hV (some β)) = V.dimension :=
  ((isMorphism (invertorAtomIso V ε hV).hom).grade_eq _).trans V.dimension_eq.symm

theorem invertorTopElt_mem_faceSet (β : Bool) :
    invertorTopElt V ε hV (some β) ∈
      (invertorAtom V ε hV).ogp.faces (!ε) (invertorAtom V ε hV).top := by
  rw [invertorAtom_top]
  exact (IsInclusion.mem_faces_iff (invertorAtomIso V ε hV).hom).2
    (InvertedCylinder.mkI_some_top_mem_faceSet_top V.krullDim_eq_dimension le_rfl V.le_top β)

theorem closure_invertorTopElt (β : Bool) :
    LowerSet.Iic (invertorTopElt V ε hV (some β)) =
      map (invertorAtomIso V ε hV).hom (PartialCylinder.copy (V.ogp.bdry ⊤ ε) β ⊤) := by
  rw [invertorTopElt, ← map_Iic]
  refine congrArg (map _) ?_
  change (LowerSet.Iic (PartialCylinder.mkI (V.ogp.bdry ⊤ ε) (some β) V.top
    (top_notMem_bdry V ε)) : LowerSet (partialCylinder V.ogp (V.ogp.bdry ⊤ ε))) = _
  rw [← PartialCylinder.endpoint_of_notMem β (top_notMem_bdry V ε),
    PartialCylinder.Iic_endpoint, V.Iic_top]

theorem hornSet_invertorAtom :
    ((invertorAtom V ε hV).isRewritableSubmolecule_Iic_of_mem_faces
        (invertorTopElt_mem_faceSet V ε hV ε)).hornSet
        (invertorAtom V ε hV).isMolecule (invertorAtom V ε hV).isAtom.isRound =
      map (invertorAtomIso V ε hV).hom
        (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension) := by
  refine SetLike.coe_injective ?_
  rw [IsSubmoleculeOf.coe_hornSet, coe_map, ← InvertedCylinder.hornSet_closure_mkI_some_top
      (U := V.ogp) V.isAtom V.krullDim_eq_dimension hV le_rfl V.le_top,
    Set.image_sdiff (IsInclusion.injective (f := (invertorAtomIso V ε hV).hom)),
    image_interior, ← coe_map, map_bdryFull, map_top_of_isIso, invertorTopElt, ← map_Iic]

theorem eq_of_mem_closure_invertorTopElt {β : Bool} {y : (invertorAtom V ε hV).ogp}
    (hy : y ∈ LowerSet.Iic (invertorTopElt V ε hV (some β)))
    (hd : grade ℕ y = (invertorAtom V ε hV).dimension - 1) :
    y = invertorTopElt V ε hV (some β) :=
  GradeOrder.eq_of_le_of_grade_le (LowerSet.mem_Iic_iff.1 hy) (by
    rw [dim_invertorTopElt_some, hd, dimension_invertorAtom]
    omega)

theorem krullDim_closure_invertorTopElt (β : Bool) :
    krullDim (LowerSet.Iic (invertorTopElt V ε hV (some β))) =
      ((invertorAtom V ε hV).dimension - 1 : ℕ) := by
  rw [LowerSet.krullDim_Iic, dim_invertorTopElt_some, dimension_invertorAtom]
  rfl

theorem dimension_invertorAtom_pos : 0 < (invertorAtom V ε hV).dimension := by
  rw [dimension_invertorAtom]
  omega

theorem bdry_invertorAtom (α : Bool) :
    (invertorAtom V ε hV).ogp.bdry ⊤ α =
      (invertorAtom V ε hV).ogp.boundary ⊤ V.dimension α := by
  rw [(invertorAtom V ε hV).bdry_top_eq_boundary (dimension_invertorAtom_pos V ε hV),
    dimension_invertorAtom, Nat.add_sub_cancel]

theorem image_invertorUnitEmb_invertorAtom (hr : V.toMoleculeShape.IsRound) :
    map (invertorUnitEmb V.toMoleculeShape ε hV hr :
        (unitShape (V.toMoleculeShape.boundary (V.dimension - 1) (!ε))).ogp ⟶
          (invertorAtom V ε hV).ogp) ⊤ =
      (invertorAtom V ε hV).ogp.boundary ⊤ V.dimension ε :=
  image_invertorUnitEmb V.toMoleculeShape ε hV hr

theorem isPastingIn_closure_invertorTopElt :
    (invertorAtom V ε hV).ogp.IsPastingIn ((invertorAtom V ε hV).dimension - 2)
      (cond (!ε) (.Iic (invertorTopElt V ε hV (some ε)))
        (.Iic (invertorTopElt V ε hV (some (!ε)))))
      (cond (!ε) (.Iic (invertorTopElt V ε hV (some (!ε))))
        (.Iic (invertorTopElt V ε hV (some ε))))
      ((invertorAtom V ε hV).ogp.bdry ⊤ (!ε)) := by
  have hk1 : (invertorAtom V ε hV).dimension - 2 = V.dimension - 1 := by
    rw [dimension_invertorAtom]; omega
  rw [closure_invertorTopElt, closure_invertorTopElt, bdry_invertorAtom, hk1]
  cases ε <;> exact isPastingIn_invertorShape V.toMoleculeShape _ hV

theorem isMoleculeIn_bdry_invertorAtom (α : Bool) :
    IsMoleculeIn (invertorAtom V ε hV).ogp ((invertorAtom V ε hV).ogp.bdry ⊤ α) :=
  (invertorAtom V ε hV).isMolecule.bdry
    ((invertorAtom V ε hV).krullDim_top_pos (dimension_invertorAtom_pos V ε hV)) α

theorem invertorTopElt_some_bnot_mem_hornSet :
    invertorTopElt V ε hV (some (!ε)) ∈
      ((invertorAtom V ε hV).isRewritableSubmolecule_Iic_of_mem_faces
        (invertorTopElt_mem_faceSet V ε hV ε)).hornSet
        (invertorAtom V ε hV).isMolecule (invertorAtom V ε hV).isAtom.isRound := by
  rw [hornSet_invertorAtom]
  exact ⟨_, InvertedCylinder.mkI_some_notMem_std _, rfl⟩

def invertorMarkedHorn : MarkedHornData :=
  MarkedHornData.ofTopPasting (invertorAtom V ε hV) (by rw [dimension_invertorAtom]; omega) (!ε)
    (invertorTopElt V ε hV (some ε)) (invertorTopElt_mem_faceSet V ε hV ε)
    {invertorTopElt V ε hV (some (!ε))}
    (fun a ha => by
      rw [Set.mem_singleton_iff.1 ha]
      exact ⟨invertorTopElt_some_bnot_mem_hornSet V ε hV,
        by rw [dim_invertorTopElt_some]; exact hV⟩) _ _ _
    (.ofCond (by rw [dimension_invertorAtom]; omega) (!ε) ((invertorAtom V ε hV).isRDC _)
      (krullDim_closure_invertorTopElt V ε hV (!ε)).le
      (fun _ hy hyd => Set.mem_singleton_iff.2 (eq_of_mem_closure_invertorTopElt V ε hV hy hyd))
      (isPastingIn_closure_invertorTopElt V ε hV))

def invertorStdEmb :
    (partialCylinder V.ogp (V.ogp.bdry ⊤ ε)).restrict
      (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension) ⟶
    (invertorAtom V ε hV).ogp :=
  InvertedCylinder.ofStd (V.ogp.bdry ⊤ ε) ε V.dimension ≫ (invertorAtomIso V ε hV).hom

instance (V : Atom) (ε : Bool) (hV : 0 < V.dimension) : IsInclusion (invertorStdEmb V ε hV) :=
  ⟨IsInclusion.injective
    (f := InvertedCylinder.ofStd (V.ogp.bdry ⊤ ε) ε V.dimension ≫
      (invertorAtomIso V ε hV).hom)⟩

theorem image_invertorStdEmb :
    map (invertorStdEmb V ε hV) ⊤ = (invertorMarkedHorn V ε hV).hornSet := by
  rw [invertorStdEmb, map_comp, InvertedCylinder.map_ofStd_top]
  exact (hornSet_invertorAtom V ε hV).symm

def invertorStdIso :
    (partialCylinder V.ogp (V.ogp.bdry ⊤ ε)).restrict
      (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension) ≅
    (invertorAtom V ε hV).ogp.restrict (invertorMarkedHorn V ε hV).hornSet where
  hom := codRestrict (invertorStdEmb V ε hV) (invertorMarkedHorn V ε hV).hornSet
    fun x => image_invertorStdEmb V ε hV ▸ ⟨x, LowerSet.mem_top, rfl⟩
  inv := ConcreteCategory.ofHom
    ⟨fun a => ⟨(invertorAtomIso V ε hV).inv a.1, by
        have ha : a.1 ∈ map (invertorAtomIso V ε hV).hom
            (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension) :=
          hornSet_invertorAtom V ε hV ▸ a.2
        obtain ⟨b, hb, hba⟩ := ha
        rwa [← hba, Iso.hom_inv_id_apply]⟩,
      IsMorphism.of_comp_of_injective
        (g := codRestrict (invertorStdEmb V ε hV) (invertorMarkedHorn V ε hV).hornSet
          fun x => image_invertorStdEmb V ε hV ▸ ⟨x, LowerSet.mem_top, rfl⟩)
        (isMorphism _)
        (fun _ _ h => IsInclusion.injective (f := invertorStdEmb V ε hV) (congrArg Subtype.val h))
        (by
          convert IsMorphism.id
            ((invertorAtom V ε hV).ogp.restrict (invertorMarkedHorn V ε hV).hornSet) using 1
          funext a
          exact Subtype.ext (Iso.inv_hom_id_apply (invertorAtomIso V ε hV) a.1))⟩
  hom_inv_id := by
    ext x
    exact Iso.hom_inv_id_apply (invertorAtomIso V ε hV) x.1
  inv_hom_id := by
    ext a
    exact Iso.inv_hom_id_apply (invertorAtomIso V ε hV) a.1

def invertorHornProj : (invertorMarkedHorn V ε hV).hornRDC ⟶ V.rdc :=
  let rdcCyl : RDCpx.{0} := ⟨⟨partialCylinder V.ogp (V.ogp.bdry ⊤ ε),
    isRDC_of_isMolecule (isMolecule_partialCylinder V.isMolecule (V.ogp.bdry ⊤ ε))⟩⟩
  (RDCpx.isoOfIso
      (P := RDCpx.restrict rdcCyl (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension))
      (Q := (invertorMarkedHorn V ε hV).hornRDC)
      (invertorStdIso V ε hV)).inv ≫
    RDCpx.restrictIncl rdcCyl (InvertedCylinder.std (V.ogp.bdry ⊤ ε) ε V.dimension) ≫
    ⟨ConcreteCategory.ofHom (C := RDCpxDown.{0}) (X := rdcCyl.obj) (Y := V.rdc.obj)
      ⟨partialCylinderProj V.ogp (V.ogp.bdry ⊤ ε),
        isMap_partialCylinderProj V.isMolecule (V.ogp.bdry ⊤ ε)⟩,
      functor_isFibered_partialCylinderProj V.ogp (V.ogp.bdry ⊤ ε)⟩

theorem invertorHornProj_apply
    (a : (invertorAtom V ε hV).ogp.restrict (invertorMarkedHorn V ε hV).hornSet) :
    ConcreteCategory.hom (invertorHornProj V ε hV).hom a =
      partialCylinderProj V.ogp (V.ogp.bdry ⊤ ε) ((invertorAtomIso V ε hV).inv a.1) :=
  rfl

end InvertorAtom

section InvertorHorn

variable {V : Atom} (ε : Bool) (hV : 0 < V.dimension)

theorem invertorEndpointNot_mem_horn (x : V.ogp) :
    invertorEndpointNot V.toMoleculeShape ε hV x ∈ (invertorMarkedHorn V ε hV).hornSet := by
  change invertorEndpointNot V.toMoleculeShape ε hV x ∈
    ((invertorAtom V ε hV).isRewritableSubmolecule_Iic_of_mem_faces
      (invertorTopElt_mem_faceSet V ε hV ε)).hornSet
      (invertorAtom V ε hV).isMolecule (invertorAtom V ε hV).isAtom.isRound
  rw [hornSet_invertorAtom]
  exact ⟨_, invertorEndpointNot_mem_std V.toMoleculeShape ε hV x,
    Iso.inv_hom_id_apply (invertorShapeIso V.toMoleculeShape ε hV) _⟩

theorem invertorUnitEmb_mem_horn (hr : V.toMoleculeShape.IsRound)
    (y : (unitShape (V.toMoleculeShape.boundary (V.dimension - 1) (!ε))).ogp) :
    invertorUnitEmb V.toMoleculeShape ε hV hr y ∈ (invertorMarkedHorn V ε hV).hornSet := by
  have h1 : invertorUnitEmb V.toMoleculeShape ε hV hr y ∈
      (invertorAtom V ε hV).ogp.boundary ⊤ V.dimension ε := by
    rw [← image_invertorUnitEmb_invertorAtom V ε hV hr]
    exact ⟨y, LowerSet.mem_top, rfl⟩
  have h2 : (invertorAtom V ε hV).ogp.bdry ⊤ ε ≤ (invertorMarkedHorn V ε hV).hornSet := by
    have h := (invertorMarkedHorn V ε hV).bdry_not_subset_hornSet
    change (invertorAtom V ε hV).ogp.bdry ⊤ (!!ε) ≤ _ at h
    rwa [Bool.not_not] at h
  rw [bdry_invertorAtom] at h2
  exact h2 h1

theorem invertorEndpointNot_top :
    invertorEndpointNot V.toMoleculeShape ε hV V.top = invertorTopElt V ε hV (some (!ε)) :=
  (invertorEndpointNot_apply V.toMoleculeShape ε hV V.top).trans
    (congrArg (invertorShapeIso V.toMoleculeShape ε hV).hom
      (PartialCylinder.endpoint_of_notMem _ (top_notMem_bdry V ε)))

theorem invertorEndpointNot_comp_proj :
    @RDCpx.ofInclusion V.rdc (invertorMarkedHorn V ε hV).hornRDC
        (codRestrict (invertorEndpointNot V.toMoleculeShape ε hV)
          (invertorMarkedHorn V ε hV).hornSet (invertorEndpointNot_mem_horn ε hV))
        ⟨fun _ _ h => IsInclusion.injective
          (f := invertorEndpointNot V.toMoleculeShape ε hV) (congrArg Subtype.val h)⟩ ≫
      invertorHornProj V ε hV = 𝟙 V.rdc := by
  ext x
  exact proj_invertorShapeIso_symm_invertorEndpointNot V.toMoleculeShape ε hV x

theorem invertorUnitEmb_comp_proj (hr : V.toMoleculeShape.IsRound) :
    @RDCpx.ofInclusion (unitShape (V.toMoleculeShape.boundary (V.dimension - 1) (!ε))).rdc
        (invertorMarkedHorn V ε hV).hornRDC
        (codRestrict (invertorUnitEmb V.toMoleculeShape ε hV hr)
          (invertorMarkedHorn V ε hV).hornSet (invertorUnitEmb_mem_horn ε hV hr))
        ⟨fun _ _ h => IsInclusion.injective
          (f := invertorUnitEmb V.toMoleculeShape ε hV hr) (congrArg Subtype.val h)⟩ ≫
      invertorHornProj V ε hV =
      cylProj _ _ ≫
        @RDCpx.ofInclusion (V.toMoleculeShape.boundary (V.dimension - 1) (!ε)).rdc V.rdc
          (V.toMoleculeShape.boundaryIncl (V.dimension - 1) (!ε))
          (inferInstanceAs (IsInclusion (V.toMoleculeShape.boundaryIncl _ _))) := by
  ext y
  exact proj_invertorShapeIso_symm_invertorUnitEmb V.toMoleculeShape ε hV hr y

end InvertorHorn

end Atoms.Shape
