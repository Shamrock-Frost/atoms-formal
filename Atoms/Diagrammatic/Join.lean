import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.Join
import Atoms.Shape.AugmentedJoin

open CategoryTheory CategoryTheory.WithInitial MonoidalCategory Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable instance (X Y : AugmentedAtomᵒᵖ ⥤ Type u) : MonoidalCategory.DayConvolution X Y :=
  .ofHasPointwiseLeftKanExtension X Y

instance : TensorUnitIsStar Atom := ⟨rfl⟩

noncomputable def joinBallIso (U V : Atom) :
    WithInitial.join (ball.{u} U) (ball.{u} V) ≅ ball.{u} (atomJoin U V) :=
  joinULiftYonedaIso U V

@[reassoc] theorem joinInclLeft_comp_joinBallIso_hom (U V : Atom) :
    WithInitial.joinInclLeft (ball.{u} U) (ball.{u} V) ≫ (joinBallIso U V).hom =
      uliftYoneda.map (joinInclLeftHom U V) :=
  uliftYonedaEquiv.injective
    (((uliftYonedaEquiv_joinInclLeft_comp_joinULiftYonedaIso_hom U V
      (starInitial.to (of V))).trans (congrArg ULift.up (AugmentedAtom.inl_of_of U V))).trans
      (uliftYonedaEquiv_uliftYoneda_map _).symm)

@[reassoc] theorem joinInclRight_comp_joinBallIso_hom (U V : Atom) :
    WithInitial.joinInclRight (ball.{u} U) (ball.{u} V) ≫ (joinBallIso U V).hom =
      uliftYoneda.map (joinInclRightHom U V) :=
  uliftYonedaEquiv.injective
    (((uliftYonedaEquiv_joinInclRight_comp_joinULiftYonedaIso_hom U V
      (starInitial.to (of U))).trans (congrArg ULift.up (AugmentedAtom.inr_of_of U V))).trans
      (uliftYonedaEquiv_uliftYoneda_map _).symm)

@[reassoc] theorem joinMap_uliftYoneda_map_comp_joinBallIso_hom {U U' V V' : Atom}
    (f : U ⟶ U') (g : V ⟶ V') :
    WithInitial.joinMap (uliftYoneda.{u}.map f) (uliftYoneda.{u}.map g) ≫
        (joinBallIso U' V').hom =
      (joinBallIso U V).hom ≫ uliftYoneda.map (joinHom f g) :=
  joinMap_uliftYoneda_map_comp_joinULiftYonedaIso_hom f g

namespace DiagSet.Join

scoped notation "𝒥" => Functor.curry.obj
  (WithInitial.joinFunctor (C := Atom) : DiagSet × DiagSet ⥤ DiagSet)

end DiagSet.Join

end Atoms.Diagrammatic
