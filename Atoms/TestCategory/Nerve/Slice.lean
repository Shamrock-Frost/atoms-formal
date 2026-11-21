import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Atoms.TestCategory.Nerve.Adjunction
import Atoms.TestCategory.Presheaf.Aspherical

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

private def nerveFunctorOverEquiv (a : A) (C : Cat.{u, u}) (f : Over a) :
    (Cat.of (Over f.left) ⟶ C) ≃ (Cat.of (Over f) ⟶ C) where
  toFun G := (Over.iteratedSliceForward f).toCatHom ≫ G
  invFun H := (Over.iteratedSliceBackward f).toCatHom ≫ H
  left_inv _ := Cat.Hom.ext rfl
  right_inv H := by
    refine Cat.Hom.ext ?_
    exact (congrArg (· ⋙ H.toFunctor)
      (Over.iteratedSliceForward_comp_iteratedSliceBackward f)).trans (Functor.id_comp _)

def nerveFunctorOverIso (a : A) (C : Cat.{u, u}) :
    (Over.forget a).op ⋙ (nerveFunctor A).obj C ≅ (nerveFunctor (Over a)).obj C :=
  NatIso.ofComponents (fun f => (nerveFunctorOverEquiv A a C f.unop).toIso) (fun _ => by
    ext
    rfl)

namespace BasicLocalizer

theorem pshAspherical_nerveFunctor_over_iff (a : A) (C : Cat.{u, u}) :
    𝒲.PshAspherical (Over a) ((nerveFunctor (Over a)).obj C) ↔
      𝒲.PshAspherical A (yoneda.obj a ⨯ (nerveFunctor A).obj C) := by
  rw [← 𝒲.pshAspherical_iff_of_iso (Over a) (nerveFunctorOverIso A a C),
    𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)]
  let e := elementsOverRestrictEquivalence A a ((nerveFunctor A).obj C)
  exact ⟨𝒲.aspherical_of_equivalence e, 𝒲.aspherical_of_equivalence e.symm⟩

end BasicLocalizer

end Atoms.TestCategory
