import Atoms.Diagrammatic.Marked.ModelStructure
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.LeftProper

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

theorem weakEquivalence_coinductive_iff (n : ℕ∞) {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map f) ↔
      markedExactCylinder.weakEquivalences (coinductiveGenerators n) f :=
  weakEquivalence_iff _

theorem weakEquivalence_coinductive_of_isPushout (n : ℕ∞) {E D B P : MarkedDiagSet.{u}}
    {j : E ⟶ D} {w : E ⟶ B} {q : D ⟶ P} {j' : B ⟶ P} (h : IsPushout j w q j') [Mono j] :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map w) →
      WeakEquivalence ((MarkedDiagSet.toCoinductive n).map q) := by
  intro hw
  exact (weakEquivalence_coinductive_iff n q).2
    (markedExactCylinder.{u}.weakEquivalences_of_isPushout
      (coinductiveGenerators_le_monomorphisms n) h ((weakEquivalence_coinductive_iff n w).1 hw))

theorem weakEquivalence_coinductive_of_isPushout_of_mono (n : ℕ∞)
    {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : MarkedDiagSet.{u}}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono ψ₁]
    (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map χ₀) →
      WeakEquivalence ((MarkedDiagSet.toCoinductive n).map χ₁) →
        WeakEquivalence ((MarkedDiagSet.toCoinductive n).map χ₂) →
          WeakEquivalence ((MarkedDiagSet.toCoinductive n).map χ') := by
  intro hχ₀ hχ₁ hχ₂
  exact (weakEquivalence_coinductive_iff n χ').2
    (markedExactCylinder.{u}.weakEquivalences_of_isPushout_of_mono
      (coinductiveGenerators_le_monomorphisms n) hF hG χ₀ χ₁ χ₂ χ' h₁ h₂ h₁' h₂'
      ((weakEquivalence_coinductive_iff n χ₀).1 hχ₀) ((weakEquivalence_coinductive_iff n χ₁).1 hχ₁)
      ((weakEquivalence_coinductive_iff n χ₂).1 hχ₂))

end Atoms.Diagrammatic
