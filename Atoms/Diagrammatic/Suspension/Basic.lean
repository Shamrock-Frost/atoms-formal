import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.Shape.Suspension
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable abbrev pointPair : DiagSet.{u} := ball atomPoint ⨿ ball atomPoint

noncomputable def suspendedBallPoles (U : Atom) : pointPair.{u} ⟶ ball.{u} (atomSuspension.obj U) :=
  coprod.desc (uliftYoneda.map (suspPole U false)) (uliftYoneda.map (suspPole U true))

@[reassoc (attr := simp)] theorem suspendedBallPoles_comp_map {U V : Atom} (f : U ⟶ V) :
    suspendedBallPoles.{u} U ≫ uliftYoneda.map (atomSuspension.map f) = suspendedBallPoles V := by
  refine coprod.hom_ext ?_ ?_ <;>
    simp only [suspendedBallPoles, coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc,
      coprod.inr_desc, ← Functor.map_comp, suspPole_comp_atomSuspension_map]

noncomputable def suspendedBall : Atom ⥤ Under (pointPair.{u}) where
  obj U := Under.mk (suspendedBallPoles U)
  map f := Under.homMk (uliftYoneda.map (atomSuspension.map f)) (suspendedBallPoles_comp_map f)
  map_id U := by
    ext1
    exact (congrArg uliftYoneda.map (atomSuspension.map_id U)).trans (uliftYoneda.map_id _)
  map_comp f g := by
    ext1
    exact (congrArg uliftYoneda.map (atomSuspension.map_comp f g)).trans
      (uliftYoneda.map_comp _ _)

@[simp] theorem suspendedBall_obj_right (U : Atom) :
    (suspendedBall.{u}.obj U).right = ball (atomSuspension.obj U) :=
  rfl

@[simp] theorem suspendedBall_obj_hom (U : Atom) :
    (suspendedBall.{u}.obj U).hom = suspendedBallPoles U :=
  rfl

instance : uliftYoneda.{u}.HasPointwiseLeftKanExtension suspendedBall.{u} :=
  have : HasColimitsOfSize.{0, u} (Under (pointPair.{u})) := hasColimitsOfSizeShrink.{0, u, u, u} _
  inferInstance

noncomputable def bipointedSuspension : DiagSet.{u} ⥤ Under (pointPair.{u}) :=
  uliftYoneda.{u}.leftKanExtension suspendedBall.{u}

noncomputable def bipointedHom : Under (pointPair.{u}) ⥤ DiagSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} suspendedBall.{u}

noncomputable def bipointedSuspensionAdjunction :
    bipointedSuspension.{u} ⊣ bipointedHom.{u} :=
  Presheaf.uliftYonedaAdjunction (uliftYoneda.{u}.leftKanExtension suspendedBall.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit suspendedBall.{u})

noncomputable def bipointedHomObjEquiv (p : Under (pointPair.{u})) (U : Atom) :
    ((bipointedHom.obj p).obj (op U)) ≃
      {f : ball.{u} (atomSuspension.obj U) ⟶ p.right // (suspendedBall.obj U).hom ≫ f = p.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.val f.property
      left_inv _ := rfl
      right_inv _ := rfl }

noncomputable def bipointedSuspensionBallIso (U : Atom) :
    bipointedSuspension.obj (ball.{u} U) ≅ suspendedBall.obj U :=
  (Presheaf.isExtensionAlongULiftYoneda suspendedBall.{u}).app U

@[reassoc] theorem bipointedSuspensionBallIso_inv_naturality {U V : Atom} (f : U ⟶ V) :
    suspendedBall.map f ≫ (bipointedSuspensionBallIso.{u} V).inv =
      (bipointedSuspensionBallIso U).inv ≫ bipointedSuspension.map (uliftYoneda.map f) :=
  (Presheaf.isExtensionAlongULiftYoneda suspendedBall.{u}).inv.naturality f

theorem bipointedSuspensionAdjunction_homEquiv_symm_uliftYonedaEquiv_symm
    {p : Under pointPair.{u}} {U : Atom} (x : (bipointedHom.obj p).obj (op U)) :
    (bipointedSuspensionAdjunction.homEquiv _ _).symm (uliftYonedaEquiv.symm x) =
      (bipointedSuspensionBallIso U).hom ≫ x.down := by
  have h1 : (uliftYonedaEquiv (F := uliftYoneda.{u}.obj U)).symm ⟨𝟙 U⟩ = 𝟙 _ :=
    uliftYonedaEquiv.injective (Equiv.apply_symm_apply _ _)
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{0}
    (uliftYoneda.{u}.leftKanExtension suspendedBall.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit suspendedBall.{u})
    ((bipointedSuspensionBallIso U).hom ≫ x.down) (Z := op U) ⟨𝟙 U⟩
  refine (Equiv.symm_apply_eq _).2 (uliftYonedaEquiv.injective ?_)
  refine (Equiv.apply_symm_apply _ _).trans (h.trans (congrArg ULift.up ?_)).symm
  exact (congrArg (fun g => _ ≫ (uliftYoneda.{u}.leftKanExtension suspendedBall.{u}).map g ≫ _)
    h1).trans ((congrArg (_ ≫ ·) ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.id_comp _))).trans (Iso.inv_hom_id_assoc (bipointedSuspensionBallIso U) x.down))

instance : PreservesColimitsOfSize.{u, u} (bipointedSuspension.{u}) :=
  bipointedSuspensionAdjunction.leftAdjoint_preservesColimits

noncomputable def isInitialBipointedSuspensionObj {E : DiagSet.{u}} (hE : IsInitial E) :
    IsInitial (bipointedSuspension.obj E) :=
  hE.isInitialObj bipointedSuspension

end Atoms.Diagrammatic
