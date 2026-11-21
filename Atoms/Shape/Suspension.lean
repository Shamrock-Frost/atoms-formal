import Atoms.Molecule.Construction.SuspensionMap
import Atoms.Shape.Standard

open CategoryTheory Order Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Shape

private def suspHom {U V : Atom} (f : U ⟶ V) :
    Atom.ofOGP (suspension U.ogp) (isAtom_suspension U.ogp U.isAtom) ⟶
      Atom.ofOGP (suspension V.ogp) (isAtom_suspension V.ogp V.isAtom) :=
  haveI := functor_isFibered_suspMap (Atom.isMap f).monotone
  Atom.conjHom (FiniteOGP.ofOGPIso _) (FiniteOGP.ofOGPIso _) (suspMap f)
    (isMap_suspMap U.isRDC (Atom.isMap f))

def atomSuspension : Atom ⥤ Atom where
  obj U := Atom.ofOGP (suspension U.ogp) (isAtom_suspension U.ogp U.isAtom)
  map := suspHom
  map_id U := Atom.hom_ext fun x => by
    have h : suspMap (𝟙 U : U ⟶ U) = fun w => w :=
      (congrArg suspMap (funext (ConcreteCategory.id_apply (X := U)))).trans suspMap_id
    rw [suspHom, Atom.conjHom_apply, h]
    exact Iso.inv_hom_id_apply _ x
  map_comp f g := Atom.hom_ext fun x => by
    rw [ConcreteCategory.comp_apply, suspHom, suspHom, suspHom, Atom.conjHom_apply,
      Atom.conjHom_apply, Atom.conjHom_apply, Iso.hom_inv_id_apply]
    have h : suspMap (f ≫ g : _ ⟶ _) = fun w => suspMap g (suspMap f w) :=
      (congrArg suspMap (funext (ConcreteCategory.comp_apply f g))).trans (suspMap_comp _ _)
    rw [h]

theorem atomSuspension_obj (U : Atom) :
    atomSuspension.obj U = Atom.ofOGP (suspension U.ogp) (isAtom_suspension U.ogp U.isAtom) :=
  rfl

theorem atomSuspension_map_apply {U V : Atom} (f : U ⟶ V) (x : (atomSuspension.obj U).ogp) :
    atomSuspension.map f x = (FiniteOGP.ofOGPIso (suspension V.ogp)).hom
      (suspMap f ((FiniteOGP.ofOGPIso (suspension U.ogp)).inv x)) :=
  rfl

def suspPole (U : Atom) (α : Bool) : atomPoint ⟶ atomSuspension.obj U :=
  haveI := (isLocalEmbedding_of_isInclusion (suspension.poleIncl U.ogp α)).functor_isFibered
  Atom.conjHom (FiniteOGP.ofOGPIso point) (FiniteOGP.ofOGPIso _) (suspension.poleIncl U.ogp α)
    (isMap_of_isInclusion _)

theorem suspPole_apply (U : Atom) (α : Bool) (x : atomPoint.ogp) :
    suspPole U α x = (FiniteOGP.ofOGPIso (suspension U.ogp)).hom (SuspCarrier.pole α) :=
  rfl

@[reassoc (attr := simp)] theorem suspPole_comp_atomSuspension_map {U V : Atom} (f : U ⟶ V)
    (α : Bool) : suspPole U α ≫ atomSuspension.map f = suspPole V α :=
  Atom.hom_ext fun x => by
    rw [ConcreteCategory.comp_apply, atomSuspension_map_apply, suspPole_apply,
      Iso.hom_inv_id_apply, suspMap_pole, suspPole_apply]

theorem suspPole_false_ne_true (U : Atom) : suspPole U false ≠ suspPole U true := fun h => by
  have := ConcreteCategory.congr_hom h (default : atomPoint.ogp)
  rw [suspPole_apply, suspPole_apply] at this
  exact Bool.false_ne_true (SuspCarrier.pole.inj
    (IsInclusion.injective (f := (FiniteOGP.ofOGPIso (suspension U.ogp)).hom) this))

theorem dimension_atomSuspension (U : Atom) :
    (atomSuspension.obj U).dimension = U.dimension + 1 := by
  have htop : (⊤ : LowerSet (suspension U.ogp)) = LowerSet.Iic (SuspCarrier.susp U.top) := by
    refine le_antisymm (fun w _ => ?_) le_top
    cases w with
    | pole α => exact SuspCarrier.pole_le_susp α U.top
    | susp x => exact SuspCarrier.susp_le_susp.2 (U.le_top x)
  have hk : krullDim (atomSuspension.obj U).ogp = ((U.dimension + 1 : ℕ) : WithBot ℕ∞) := by
    refine (krullDim_eq_of_orderIso
      (orderIsoOfIso (FiniteOGP.ofOGPIso (suspension U.ogp)))).symm.trans ?_
    rw [← LowerSet.krullDim_top, htop, LowerSet.krullDim_Iic, SuspCarrier.grade_susp,
      ← U.dimension_eq]
  exact_mod_cast (atomSuspension.obj U).krullDim_eq_dimension.symm.trans hk

theorem isInclusionHom_atomSuspension_map {U V : Atom} {f : U ⟶ V} (hf : IsInclusionHom f) :
    IsInclusionHom (atomSuspension.map f) :=
  haveI := functor_isFibered_suspMap (Atom.isMap f).monotone
  Atom.isInclusionHom_conjHom _ _ (isMap_suspMap U.isRDC (Atom.isMap f)) (injective_suspMap hf)

theorem isCollapseHom_atomSuspension_map {U V : Atom} {f : U ⟶ V} (hf : IsCollapseHom f) :
    IsCollapseHom (atomSuspension.map f) :=
  haveI := functor_isFibered_suspMap (Atom.isMap f).monotone
  Atom.isCollapseHom_conjHom _ _ (isMap_suspMap U.isRDC (Atom.isMap f)) (surjective_suspMap hf)

instance : atomSuspension.Faithful where
  map_injective {U V} {f g} h := Atom.hom_ext fun x => by
    have := (atomSuspension_map_apply f _).symm.trans ((ConcreteCategory.congr_hom h
      ((FiniteOGP.ofOGPIso (suspension U.ogp)).hom (SuspCarrier.susp x))).trans
        (atomSuspension_map_apply g _))
    rw [Iso.hom_inv_id_apply, suspMap_susp, suspMap_susp] at this
    exact SuspCarrier.susp.inj
      (IsInclusion.injective (f := (FiniteOGP.ofOGPIso (suspension V.ogp)).hom) this)

def atomSuspensionGlobeIso (n : ℕ) : atomSuspension.obj (atomGlobe n) ≅ atomGlobe (n + 1) :=
  Atom.isoOfIso ((FiniteOGP.ofOGPIso (suspension (atomGlobe n).ogp)).symm ≪≫
    suspension.mapIso (FiniteOGP.ofOGPIso (globe n)).symm ≪≫
      FiniteOGP.ofOGPIso (globe (n + 1)))

def atomSuspensionRDCIso (U : Atom) :
    atomToRDCpx.obj (atomSuspension.obj U) ≅ RDCpx.suspensionFunctor.obj (atomToRDCpx.obj U) :=
  RDCpx.isoOfIso (P := atomToRDCpx.obj (atomSuspension.obj U))
    (Q := RDCpx.suspensionFunctor.obj (atomToRDCpx.obj U))
    (FiniteOGP.ofOGPIso (suspension U.ogp)).symm

theorem atomSuspensionRDCIso_hom_apply (U : Atom) (x : (atomSuspension.obj U).ogp) :
    ConcreteCategory.hom (atomSuspensionRDCIso U).hom.hom x =
      (FiniteOGP.ofOGPIso (suspension U.ogp)).inv x :=
  rfl

@[reassoc] theorem atomSuspensionRDCIso_hom_naturality {U V : Atom} (f : U ⟶ V) :
    atomToRDCpx.map (atomSuspension.map f) ≫ (atomSuspensionRDCIso V).hom =
      (atomSuspensionRDCIso U).hom ≫ RDCpx.suspensionFunctor.map (atomToRDCpx.map f) := by
  ext x
  exact ConcreteCategory.congr_hom (FiniteOGP.ofOGPIso (suspension V.ogp)).hom_inv_id _

def suspPoleRDC (P : RDCpx.{0}) (α : Bool) :
    atomToRDCpx.obj atomPoint ⟶ RDCpx.suspensionFunctor.obj P :=
  haveI : IsInclusion ((FiniteOGP.ofOGPIso point.{0}).inv ≫ suspension.poleIncl P.obj.toOGP α) :=
    inferInstance
  @RDCpx.ofInclusion (atomToRDCpx.obj atomPoint) (RDCpx.suspensionFunctor.obj P)
    ((FiniteOGP.ofOGPIso point.{0}).inv ≫ suspension.poleIncl P.obj.toOGP α) this

theorem suspPoleRDC_apply (P : RDCpx.{0}) (α : Bool) (x : atomPoint.ogp) :
    ConcreteCategory.hom (suspPoleRDC P α).hom x = SuspCarrier.pole α :=
  rfl

@[reassoc (attr := simp)] theorem suspPoleRDC_comp_suspensionFunctor_map {P Q : RDCpx.{0}}
    (f : P ⟶ Q) (α : Bool) : suspPoleRDC P α ≫ RDCpx.suspensionFunctor.map f = suspPoleRDC Q α :=
  rfl

@[reassoc] theorem suspPole_comp_atomSuspensionRDCIso_hom (U : Atom) (α : Bool) :
    atomToRDCpx.map (suspPole U α) ≫ (atomSuspensionRDCIso U).hom =
      suspPoleRDC (atomToRDCpx.obj U) α := by
  ext x
  exact ConcreteCategory.congr_hom (FiniteOGP.ofOGPIso (suspension U.ogp)).hom_inv_id _

end Atoms.Shape
