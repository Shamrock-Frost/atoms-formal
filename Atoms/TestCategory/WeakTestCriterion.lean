import Atoms.TestCategory.IsTest

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

def counitOverLiftsIso (C : Cat.{u, u}) (c : C) :
    NatTrans.overLifts (nerveFunctorObjIso C).hom c ≅ (nerveFunctor A).obj (Cat.of (Over c)) :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun q := q.lift.toCatHom
      invFun H := ⟨(H.toFunctor ⋙ Over.forget c).toCatHom, H.toFunctor, rfl⟩
      left_inv q := NatTrans.OverLift.ext (Cat.Hom.ext q.w.symm) rfl
      right_inv _ := rfl }) (fun _ => rfl)

def counitCostructuredArrowEquivalence (C : Cat.{u, u}) (c : C) :
    CostructuredArrow ((nerveAdjunction A).counit.app C).toFunctor c ≌
      (((nerveFunctor A).obj (Cat.of (Over c))).Elements)ᵒᵖ :=
  (NatTrans.overLiftsEquivalence (nerveFunctorObjIso C).hom c
    (fun a => Over.mkIdIsTerminal a)).trans
    (Cat.equivOfIso ((elementsFunctor A).mapIso (counitOverLiftsIso A C c)))

namespace BasicLocalizer

theorem asphericalFunctor_counit_app
    (h : ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.PshAspherical A ((nerveFunctor A).obj C))
    (C : Cat.{u, u}) : 𝒲.AsphericalFunctor ((nerveAdjunction A).counit.app C) := fun c =>
  𝒲.aspherical_of_equivalence
    (A := (elementsFunctor A).obj ((nerveFunctor A).obj (Cat.of (Over c))))
    (counitCostructuredArrowEquivalence A C c).symm
    (@h (Cat.of (Over c)) (IsTerminal.hasTerminal (C := Over c) Over.mkIdTerminal))

theorem isWeakTest_of_pshAspherical_nerveFunctor_obj
    (h : ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.PshAspherical A ((nerveFunctor A).obj C)) :
    𝒲.IsWeakTest A :=
  ⟨fun C => 𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_counit_app A h C)⟩

end BasicLocalizer

end Atoms.TestCategory
