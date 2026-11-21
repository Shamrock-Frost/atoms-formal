import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory Limits HomotopicalAlgebra

universe v u

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

theorem exists_weakEquivalence_of_cospan [HasInitial C] [HasTerminal C]
    {A B D : C} [IsCofibrant A] [IsFibrant B]
    (l : A ⟶ D) (r : B ⟶ D) [WeakEquivalence l] [WeakEquivalence r] :
    ∃ f : A ⟶ B, WeakEquivalence f := by
  let φ := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) r
  have : WeakEquivalence φ.p := weakEquivalence_of_precomp_of_fac φ.fac
  let s : CommSq (𝟙 B) φ.i (terminal.from B) (terminal.from φ.Z) :=
    ⟨terminal.hom_ext _ _⟩
  let _ : s.HasLift := (ModelCategory.cm4a φ.i (terminal.from B)).sq_hasLift s
  have : WeakEquivalence s.lift := weakEquivalence_of_precomp_of_fac s.fac_left
  let t : CommSq (initial.to φ.Z) (initial.to A) φ.p l := ⟨initial.hom_ext _ _⟩
  let _ : t.HasLift := (ModelCategory.cm4b (initial.to A) φ.p).sq_hasLift t
  have : WeakEquivalence t.lift := weakEquivalence_of_postcomp_of_fac t.fac_right
  exact ⟨t.lift ≫ s.lift, inferInstance⟩

end HomotopicalAlgebra
