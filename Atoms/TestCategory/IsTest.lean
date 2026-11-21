import Atoms.TestCategory.Presheaf.Aspherical
import Atoms.TestCategory.Nerve.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Cat.Limit

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

class IsWeakTest : Prop where
  counit_mem (C : Cat.{u, u}) : 𝒲.W ((nerveAdjunction A).counit.app C)

section

variable {A}

theorem aspherical_of_isWeakTest [hA : 𝒲.IsWeakTest A] : 𝒲.Aspherical (Cat.of A) := by
  have : PreservesLimitsOfSize.{0, 0} (nerveFunctor A) :=
    (nerveAdjunction A).rightAdjoint_preservesLimits
  let e := PreservesTerminal.iso (nerveFunctor A) (C := Cat.{u, u})
  have hN : 𝒲.Aspherical ((elementsFunctor A).obj ((nerveFunctor A).obj (⊤_ Cat))) := by
    have h := hA.counit_mem (⊤_ Cat.{u, u})
    rw [terminal.hom_ext ((nerveAdjunction A).counit.app (⊤_ Cat.{u, u})) (terminal.from _)] at h
    exact h
  have hg : 𝒲.W ((elementsFunctor A).map e.hom ≫ elementsTerminalHom A) :=
    𝒲.W.comp_mem _ _
      (isomorphisms_le_of_containsIdentities 𝒲.W _ (isomorphisms.infer_property _))
      (𝒲.W_elementsTerminalHom A)
  exact (𝒲.aspherical_iff_of_W _ hg).1 hN

end

class IsLocalTest : Prop where
  isWeakTest_over (a : A) : 𝒲.IsWeakTest (Over a)

attribute [instance] IsLocalTest.isWeakTest_over

class IsTest : Prop extends 𝒲.IsWeakTest A, 𝒲.IsLocalTest A

def LocallyAspherical (X : Aᵒᵖ ⥤ Type u) : Prop :=
  ∀ a : A, 𝒲.PshAspherical A (yoneda.obj a ⨯ X)

end BasicLocalizer

end Atoms.TestCategory
