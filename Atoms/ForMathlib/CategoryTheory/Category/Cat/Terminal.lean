import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Limits.Unit

namespace CategoryTheory

open Limits Opposite

universe v u

instance Cat.hasTerminal_of (C : Type u) [Category.{v} C] [HasTerminal C] :
    HasTerminal (Cat.of C) :=
  inferInstanceAs (HasTerminal C)

namespace Cat

instance hasTerminal_costructuredArrow_id {B : Cat.{u, u}} (b : B) :
    HasTerminal (Cat.of (CostructuredArrow (Cat.Hom.toFunctor (𝟙 B)) b)) :=
  (CostructuredArrow.mkIdTerminal (S := 𝟭 B) (Y := b)).hasTerminal

instance hasTerminal_opFunctor_obj_discretePUnit :
    HasTerminal (Cat.opFunctor.obj (Cat.of (Discrete PUnit.{u + 1}))) :=
  IsTerminal.hasTerminal
    (X := (show Cat.opFunctor.obj (Cat.of (Discrete PUnit.{u + 1})) from op ⟨⟨⟩⟩))
    (IsTerminal.ofUniqueHom (fun _ => 𝟙 _) (fun _ _ => rfl))

noncomputable def initialPoint (C : Cat.{u, u}) [HasInitial C] :
    Cat.of (Discrete PUnit.{u + 1}) ⟶ C :=
  Cat.Hom.ofFunctor (Functor.fromPUnit.{u} (⊥_ C))

end Cat

end CategoryTheory
