import Atoms.Diagrammatic.Marked.Fibrancy
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def MarkedDiagSet.Inductive.toCoinductive (n : ℕ∞) :
    MarkedDiagSet.Inductive.{u} n ⥤ MarkedDiagSet.Coinductive n :=
  𝟭 MarkedDiagSet.{u}

def MarkedDiagSet.Coinductive.toInductive (n : ℕ∞) :
    MarkedDiagSet.Coinductive.{u} n ⥤ MarkedDiagSet.Inductive n :=
  𝟭 MarkedDiagSet.{u}

def MarkedDiagSet.Inductive.toCoinductiveAdjunction (n : ℕ∞) :
    MarkedDiagSet.Inductive.toCoinductive.{u} n ⊣ MarkedDiagSet.Coinductive.toInductive n :=
  Adjunction.id

theorem isFibrant_inductive_of_coinductive (n : ℕ∞) (X : MarkedDiagSet.{u})
    (hX : IsFibrant ((MarkedDiagSet.toCoinductive n).obj X)) :
    IsFibrant ((MarkedDiagSet.toInductive n).obj X) := by
  obtain ⟨hI, hM⟩ := (isFibrant_coinductive_iff_natural n _).1 hX
  have h := hasMarkedRLP_of_natural hM (hasMarkedRLP_inductiveGenerators_natural n hI)
  exact (isFibrant_inductive_iff_isFibrant n _).2
    (isFibrant_markedExactCylinder _ (markedHorns_or_isIso_of_inductiveGenerators n) h
      ((hasMarkedRLP_sup _ _ _).1 ((hasMarkedRLP_sup _ _ _).1 h).1).1
      ((hasMarkedRLP_sup _ _ _).1 h).2)

theorem weakEquivalence_coinductive_of_inductive (n : ℕ∞) {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y)
    (hf : WeakEquivalence ((MarkedDiagSet.toInductive n).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map f) :=
  (weakEquivalence_iff _).2 (ExactCylinder.weakEquivalences_le_of_isFibrant markedExactCylinder
    markedExactCylinder (inductiveGenerators n) (coinductiveGenerators n)
    (fun Z hZ => (isFibrant_inductive_iff_isFibrant n Z).1 (isFibrant_inductive_of_coinductive n Z
      ((isFibrant_coinductive_iff_isFibrant n Z).2 hZ))) f ((weakEquivalence_iff _).1 hf))

private theorem weakEquivalences_inductive_eq_coinductive (n : ℕ) :
    markedExactCylinder.{u}.weakEquivalences (inductiveGenerators n) =
      markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators n) :=
  ExactCylinder.weakEquivalences_eq_of_isFibrant_iff markedExactCylinder.{u} markedExactCylinder.{u}
    (inductiveGenerators n) (coinductiveGenerators n) fun Z =>
      (((isFibrant_inductive_iff_isFibrant n Z).symm.trans
        (isFibrant_inductive_iff_natural n Z)).trans
          (isFibrant_coinductive_iff_natural n Z).symm).trans
        (isFibrant_coinductive_iff_isFibrant n Z)

theorem weakEquivalence_inductive_iff_coinductive (n : ℕ) {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence ((MarkedDiagSet.toInductive n).map f) ↔
      WeakEquivalence ((MarkedDiagSet.toCoinductive n).map f) := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  exact iff_of_eq (congrFun₂ (congrFun (weakEquivalences_inductive_eq_coinductive n) X) Y f)

theorem fibration_inductive_iff_coinductive (n : ℕ) {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y) :
    Fibration ((MarkedDiagSet.toInductive n).map f) ↔
      Fibration ((MarkedDiagSet.toCoinductive n).map f) := by
  rw [fibration_iff, fibration_iff]
  change (monomorphisms MarkedDiagSet.{u} ⊓
      markedExactCylinder.{u}.weakEquivalences (inductiveGenerators n)).rlp f ↔
    (monomorphisms MarkedDiagSet.{u} ⊓
      markedExactCylinder.{u}.weakEquivalences (coinductiveGenerators n)).rlp f
  rw [weakEquivalences_inductive_eq_coinductive]

private theorem monomorphisms_of_cofibrations_inductive (n : ℕ∞) {X Y : MarkedDiagSet.{u}}
    (f : X ⟶ Y)
    (hf : cofibrations (MarkedDiagSet.Inductive.{u} n) ((MarkedDiagSet.toInductive n).map f)) :
    monomorphisms MarkedDiagSet.{u} f :=
  hf

private theorem cofibrations_coinductive_of_monomorphisms (n : ℕ∞) {X Y : MarkedDiagSet.{u}}
    (f : X ⟶ Y)
    (hf : monomorphisms MarkedDiagSet.{u} f) :
    cofibrations (MarkedDiagSet.Coinductive.{u} n) ((MarkedDiagSet.toCoinductive n).map f) :=
  hf

theorem isQuillen_toCoinductiveAdjunction (n : ℕ∞) :
    (MarkedDiagSet.Inductive.toCoinductiveAdjunction.{u} n).IsQuillen where
  cofibrations_le _ _ f hf :=
    cofibrations_coinductive_of_monomorphisms n f (monomorphisms_of_cofibrations_inductive n f hf)
  trivialCofibrations_le _ _ f hf :=
    ⟨cofibrations_coinductive_of_monomorphisms n f
        (monomorphisms_of_cofibrations_inductive n f hf.1),
      (weakEquivalence_iff _).1
        (weakEquivalence_coinductive_of_inductive n f ((weakEquivalence_iff _).2 hf.2))⟩

theorem isQuillenEquivalence_toCoinductiveAdjunction (n : ℕ) :
    (MarkedDiagSet.Inductive.toCoinductiveAdjunction.{u} n).IsQuillenEquivalence :=
  ⟨isQuillen_toCoinductiveAdjunction n,
    fun f => (weakEquivalence_inductive_iff_coinductive n f).symm⟩

end Atoms.Diagrammatic
