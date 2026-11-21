import Atoms.Shape.Collapse
import Atoms.Molecule.Construction.GrayCylinder
import Atoms.Molecule.Construction.GrayProductHorn

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

@[implicit_reducible] def cylAtom (U : Atom) : Atom :=
  Atom.ofOGP (grayProduct (globe 1) U.ogp) (isAtom_grayProduct (isAtom_globe 1) U.isAtom)

def cylAtomIso (U : Atom) : grayProduct (globe 1) U.ogp ≅ (cylAtom U).ogp :=
  FiniteOGP.ofOGPIso _

@[implicit_reducible, simps obj] def grayCylinder : Atom ⥤ Atom where
  obj U := cylAtom U
  map {U V} f :=
    letI := Atom.functor_isFibered f
    letI := Monotone.functor_isFibered_id (α := globe.{0} 1)
    letI := functor_isFibered_prodMap monotone_id (Atom.isMap f).monotone
      (isMap_prod_right_of_isMap isRDC_globe_one U.isRDC V.isRDC (Atom.isMap f)).monotone
    Atom.conjHom (cylAtomIso U) (cylAtomIso V) (fun w => (w.1, f w.2))
      (isMap_prod_right_of_isMap isRDC_globe_one U.isRDC V.isRDC (Atom.isMap f))
  map_id U := Atom.conjHom_id (cylAtomIso U)
  map_comp {U V W} f g :=
    letI := Atom.functor_isFibered f
    letI := Atom.functor_isFibered g
    letI := Monotone.functor_isFibered_id (α := globe.{0} 1)
    letI := functor_isFibered_prodMap monotone_id (Atom.isMap f).monotone
      (isMap_prod_right_of_isMap isRDC_globe_one U.isRDC V.isRDC (Atom.isMap f)).monotone
    letI := functor_isFibered_prodMap monotone_id (Atom.isMap g).monotone
      (isMap_prod_right_of_isMap isRDC_globe_one V.isRDC W.isRDC (Atom.isMap g)).monotone
    (Atom.conjHom_comp (cylAtomIso U) (cylAtomIso V) (cylAtomIso W)
      (isMap_prod_right_of_isMap isRDC_globe_one U.isRDC V.isRDC (Atom.isMap f))
      (isMap_prod_right_of_isMap isRDC_globe_one V.isRDC W.isRDC (Atom.isMap g))).symm

theorem symm_grayCylinder_map_apply {V U : Atom} (f : V ⟶ U)
    (z : (grayCylinder.obj V).ogp) :
    (cylAtomIso U).inv (grayCylinder.map f z) =
      (((cylAtomIso V).inv z).1, f ((cylAtomIso V).inv z).2) :=
  ConcreteCategory.congr_hom (cylAtomIso U).hom_inv_id _

def grayEndpoint (ε : Bool) : 𝟭 Atom ⟶ grayCylinder where
  app U := Atom.ofInclusion (cylEndpoint ε U.ogp ≫ (cylAtomIso U).hom)
  naturality U V f := Eq.symm (Atom.hom_ext fun x =>
    congrArg (cylAtomIso V).hom
      (congrArg (fun w : grayProduct (globe.{0} 1) U.ogp =>
          ((w.1, f w.2) : grayProduct (globe.{0} 1) V.ogp))
        (ConcreteCategory.congr_hom (cylAtomIso U).hom_inv_id (SuspCarrier.pole ε, x))))

theorem symm_grayEndpoint_apply (ε : Bool) (U : Atom) (x : U.ogp) :
    (cylAtomIso U).inv ((grayEndpoint ε).app U x) = (SuspCarrier.pole ε, x) :=
  ConcreteCategory.congr_hom (cylAtomIso U).hom_inv_id (SuspCarrier.pole ε, x)

theorem isInclusionHom_grayCylinder_map {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f) :
    IsInclusionHom (grayCylinder.map f) :=
  letI := Atom.functor_isFibered f
  letI := Monotone.functor_isFibered_id (α := globe.{0} 1)
  letI := functor_isFibered_prodMap monotone_id (Atom.isMap f).monotone
    (isMap_prod_right_of_isMap isRDC_globe_one V.isRDC U.isRDC (Atom.isMap f)).monotone
  Atom.isInclusionHom_conjHom (cylAtomIso V) (cylAtomIso U)
    (isMap_prod_right_of_isMap isRDC_globe_one V.isRDC U.isRDC (Atom.isMap f))
    (fun _ _ h => Prod.ext (Prod.mk.inj h).1 (hf (Prod.mk.inj h).2))

theorem isInclusionHom_grayEndpoint (ε : Bool) (U : Atom) :
    IsInclusionHom ((grayEndpoint ε).app U) :=
  IsInclusion.injective (f := cylEndpoint ε U.ogp ≫ (cylAtomIso U).hom)

def endpointSubset (ε : Bool) (U : Atom) : LowerSet (grayCylinder.obj U).ogp :=
  map (cylEndpoint ε U.ogp ≫ (cylAtomIso U).hom) ⊤

theorem endpointSubset_eq_map (ε : Bool) (U : Atom) :
    endpointSubset ε U =
      map (cylAtomIso U).hom (LowerSet.Iic (SuspCarrier.pole ε) ×ˢ (⊤ : LowerSet U.ogp)) := by
  rw [endpointSubset, map_comp, map_grayProduct_inr]

@[simp] theorem coe_endpointSubset (ε : Bool) (U : Atom) :
    (endpointSubset ε U : Set (grayCylinder.obj U).ogp) = Set.range ((grayEndpoint ε).app U) := by
  rw [endpointSubset, coe_map, LowerSet.coe_top, Set.image_univ]
  rfl

theorem dimension_grayCylinder_obj (U : Atom) :
    (grayCylinder.obj U).dimension = U.dimension + 1 := by
  have h : krullDim (grayCylinder.obj U).ogp = (U.dimension + 1 : ℕ) := by
    rw [grayCylinder_obj, ← krullDim_eq_of_orderIso (orderIsoOfIso (cylAtomIso U)),
      krullDim_grayProduct (krullDim_globe 1) U.krullDim_eq_dimension, Nat.add_comm]
  exact_mod_cast (grayCylinder.obj U).krullDim_eq_dimension.symm.trans h

theorem isRewritableSubmolecule_grayCylinder_obj (U : Atom) {α : Bool}
    {W : LowerSet (grayProduct (globe.{0} 1) U.ogp)}
    (hW : (grayProduct (globe.{0} 1) U.ogp).IsRewritableSubmolecule W
      ((grayProduct (globe.{0} 1) U.ogp).bdry ⊤ α)) :
    (grayCylinder.obj U).ogp.IsRewritableSubmolecule (map (cylAtomIso U).hom W)
      ((grayCylinder.obj U).ogp.bdry ⊤ α) := by
  have h := (isRewritableSubmolecule_map_iff (cylAtomIso U).hom W _).2 hW
  rwa [map_bdry, map_top_of_isIso] at h

def grayContraction : grayCylinder ⟶ 𝟭 Atom where
  app U :=
    letI := (isLocalEmbedding_of_isInclusion (cylAtomIso U).inv).functor_isFibered
    letI := functor_isFibered_snd_grayProduct (isMap_snd_grayProduct_globe_one U.isRDC).monotone
    letI := Monotone.functor_isFibered_comp
      (isMap_of_isInclusion (cylAtomIso U).inv).monotone
      (isMap_snd_grayProduct_globe_one U.isRDC).monotone
    Atom.homMk (fun z => ((cylAtomIso U).inv z).2)
      ((isMap_of_isInclusion (cylAtomIso U).inv).comp (isMap_snd_grayProduct_globe_one U.isRDC))
  naturality _ _ f := Atom.hom_ext fun z =>
    congrArg Prod.snd (symm_grayCylinder_map_apply f z)

theorem grayContraction_app_apply (U : Atom) (z : (grayCylinder.obj U).ogp) :
    grayContraction.app U z = ((cylAtomIso U).inv z).2 := rfl

theorem grayEndpoint_grayContraction (ε : Bool) (U : Atom) :
    (grayEndpoint ε).app U ≫ grayContraction.app U = 𝟙 U :=
  Atom.hom_ext fun x => congrArg Prod.snd (symm_grayEndpoint_apply ε U x)

theorem isCollapseHom_grayContraction_app (U : Atom) : IsCollapseHom (grayContraction.app U) :=
  fun x => ⟨(grayEndpoint true).app U x, congrArg Prod.snd (symm_grayEndpoint_apply true U x)⟩

theorem snd_symm_cylAtomIso_le {U : Atom} {w z : (grayCylinder.obj U).ogp}
    (h : w ≤ z) : ((cylAtomIso U).inv w).2 ≤ ((cylAtomIso U).inv z).2 :=
  ((orderIsoOfIso (cylAtomIso U)).symm.monotone h).2

def cylinderSubset (U : Atom) (S : LowerSet U.ogp) :
    LowerSet (grayCylinder.obj U).ogp :=
  map (cylAtomIso U).hom ((⊤ : LowerSet (globe.{0} 1)) ×ˢ S)

theorem mem_cylinderSubset_iff (U : Atom) (S : LowerSet U.ogp)
    (z : (grayCylinder.obj U).ogp) :
    z ∈ cylinderSubset U S ↔ ((cylAtomIso U).inv z).2 ∈ S := by
  refine ⟨?_, fun h => ⟨(cylAtomIso U).inv z, ⟨LowerSet.mem_top, h⟩,
    ConcreteCategory.congr_hom (cylAtomIso U).inv_hom_id z⟩⟩
  rintro ⟨p, ⟨-, hp⟩, rfl⟩
  rwa [Iso.hom_inv_id_apply]

theorem grayCylinder_map_apply_mem_cylinderSubset (U : Atom) (S : LowerSet U.ogp)
    {V : Atom} (f : V ⟶ U) (hf : ∀ a, f a ∈ S) (z : (grayCylinder.obj V).ogp) :
    grayCylinder.map f z ∈ cylinderSubset U S :=
  (mem_cylinderSubset_iff U S _).2 (by rw [symm_grayCylinder_map_apply]; exact hf _)

theorem comp_grayCylinder_map_closureIncl_mem (U : Atom) (S : LowerSet U.ogp)
    (x : S) {T : Atom} (g : T ⟶ grayCylinder.obj (Atom.ofClosure U x.1)) (t : T.ogp) :
    (g ≫ grayCylinder.map (Atom.closureIncl U x.1)) t ∈ cylinderSubset U S :=
  grayCylinder_map_apply_mem_cylinderSubset U S (Atom.closureIncl U x.1)
    (closureIncl_mem_of_closed U S x) (g t)

theorem exists_grayCylinder_map_closureIncl_eq (U : Atom) (x : U.ogp) {T : Atom}
    (f : T ⟶ grayCylinder.obj U) (h : ∀ t, ((cylAtomIso U).inv (f t)).2 ≤ x)
    (t : T.ogp) : ∃ a, grayCylinder.map (Atom.closureIncl U x) a = f t := by
  obtain ⟨b, hb⟩ := (Atom.exists_closureIncl_eq_iff U x _).2 (h t)
  refine ⟨(cylAtomIso (Atom.ofClosure U x)).hom (((cylAtomIso U).inv (f t)).1, b), ?_⟩
  rw [← Iso.inv_hom_id_apply (cylAtomIso U) (grayCylinder.map _ _), symm_grayCylinder_map_apply,
    Iso.hom_inv_id_apply, hb, Prod.mk.eta, Iso.inv_hom_id_apply]

theorem snd_symm_le_snd_symm_top {U T : Atom} (f : T ⟶ grayCylinder.obj U)
    (t : T.ogp) :
    ((cylAtomIso U).inv (f t)).2 ≤ ((cylAtomIso U).inv (f T.top)).2 :=
  snd_symm_cylAtomIso_le ((Atom.isMap f).monotone (T.le_top t))

end Atoms.Shape
