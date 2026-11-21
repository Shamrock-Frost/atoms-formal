import Atoms.TestCategory.Nerve.Injective
import Atoms.TestCategory.WeakTestCriterion
import Atoms.TestCategory.Nerve.Slice

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

theorem pshAspherical_prod_nerveFunctor_obj_of_rlp_le
    (h : (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) (C : Cat.{u, u}) [HasTerminal C]
    (X : Aᵒᵖ ⥤ Type u) (hX : 𝒲.PshAspherical A X) :
    𝒲.PshAspherical A (FunctorToTypes.prod X ((nerveFunctor A).obj C)) := by
  have hp : 𝒲.W ((elementsFunctor A).map
      (FunctorToTypes.prod.fst (F := X) (G := (nerveFunctor A).obj C))) :=
    h _ (rlp_prod_fst_nerveFunctor_obj A C X)
  have e : terminal.from ((elementsFunctor A).obj
      (FunctorToTypes.prod X ((nerveFunctor A).obj C))) =
      (elementsFunctor A).map (FunctorToTypes.prod.fst (F := X) (G := (nerveFunctor A).obj C)) ≫
        terminal.from ((elementsFunctor A).obj X) :=
    terminal.hom_ext _ _
  change 𝒲.W _
  rw [e]
  exact 𝒲.W.comp_mem _ _ hp hX

theorem locallyAspherical_nerveFunctor_obj_of_rlp_le
    (h : (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) (C : Cat.{u, u}) [HasTerminal C] :
    𝒲.LocallyAspherical A ((nerveFunctor A).obj C) := fun a =>
  (𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).2
    (𝒲.pshAspherical_prod_nerveFunctor_obj_of_rlp_le A h C _ (𝒲.pshAspherical_yoneda A a))

theorem isLocalTest_of_locallyAspherical_nerveFunctor_obj
    (h : ∀ (C : Cat.{u, u}) [HasTerminal C], 𝒲.LocallyAspherical A ((nerveFunctor A).obj C)) :
    𝒲.IsLocalTest A :=
  ⟨fun a => 𝒲.isWeakTest_of_pshAspherical_nerveFunctor_obj (Over a)
    (fun D _ => (𝒲.pshAspherical_nerveFunctor_over_iff A a D).2 (h D a))⟩

theorem isLocalTest_of_rlp_le (h : (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) :
    𝒲.IsLocalTest A :=
  𝒲.isLocalTest_of_locallyAspherical_nerveFunctor_obj A
    (fun C _ => 𝒲.locallyAspherical_nerveFunctor_obj_of_rlp_le A h C)

theorem isWeakTest_of_rlp_le (hA : 𝒲.Aspherical (Cat.of A))
    (h : (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) :
    𝒲.IsWeakTest A :=
  𝒲.isWeakTest_of_pshAspherical_nerveFunctor_obj A
    (fun C _ => (𝒲.pshAspherical_iff_wPsh_terminal_from A hA _).2
      (h _ (rlp_terminal_from_nerveFunctor_obj A C)))

theorem isTest_of_rlp_le (hA : 𝒲.Aspherical (Cat.of A))
    (h : (monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) :
    𝒲.IsTest A :=
  { toIsWeakTest := 𝒲.isWeakTest_of_rlp_le A hA h
    toIsLocalTest := 𝒲.isLocalTest_of_rlp_le A h }

end BasicLocalizer

end Atoms.TestCategory
