import Atoms.Diagrammatic.Marked.FlatEquivalence

open CategoryTheory MorphismProperty HomotopicalAlgebra Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

theorem IsInftyCategory.of_le {m n : ℕ∞} {X : DiagSet.{u}} (hX : IsInftyCategory m X)
    (h : m ≤ n) : IsInftyCategory n X :=
  ⟨hX.1, fun U x hU => hX.2 U x (lt_of_le_of_lt h hU)⟩

theorem weakEquivalences_infty_antitone :
    Antitone (fun n : ℕ∞ => reversibleCylinder.{u}.weakEquivalences (inftyGenerators n)) := by
  intro m n h
  refine ExactCylinder.weakEquivalences_le_of_isFibrant _ _ _ _ fun X hX => ?_
  have hm := (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators m)
    (inftyGenerators_le_monomorphisms m) X).2 hX
  exact (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators n)
    (inftyGenerators_le_monomorphisms n) X).1
    ((isFibrant_infty_iff n X).2 (((isFibrant_infty_iff m X).1 hm).of_le h))

def DiagSet.Infty.changeLevel (n m : ℕ∞) : DiagSet.Infty.{u} n ⥤ DiagSet.Infty m := 𝟭 DiagSet.{u}

def DiagSet.Infty.changeLevelAdjunction (n m : ℕ∞) :
    DiagSet.Infty.changeLevel.{u} n m ⊣ DiagSet.Infty.changeLevel m n := Adjunction.id

theorem isQuillen_changeLevelAdjunction {m n : ℕ∞} (h : m ≤ n) :
    (DiagSet.Infty.changeLevelAdjunction.{u} n m).IsQuillen where
  cofibrations_le _ _ _ hf := hf
  trivialCofibrations_le _ _ f hf := ⟨hf.1, weakEquivalences_infty_antitone h f hf.2⟩

theorem DiagSet.Infty.fibration_of_le {m n : ℕ∞} (h : m ≤ n) {G H : DiagSet.{u}} (p : G ⟶ H)
    [Fibration ((DiagSet.toInfty n).map p)] (hG : IsInftyCategory m G)
    (hH : IsInftyCategory m H) : Fibration ((DiagSet.toInfty m).map p) := by
  let φ := factorizationData (trivialCofibrations (DiagSet.Infty.{u} m)) (fibrations _)
    ((DiagSet.toInfty m).map p)
  have : IsFibrant ((DiagSet.toInfty m).obj H) := (isFibrant_infty_iff m _).2 hH
  have : IsFibrant ((DiagSet.toInfty m).obj G) := (isFibrant_infty_iff m _).2 hG
  have : Fibration φ.p := (fibration_iff _).2 φ.hp
  have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  have : WeakEquivalence ((DiagSet.Infty.changeLevel m n).map φ.i) :=
    (isQuillen_changeLevelAdjunction h).weakEquivalence_map_of_isFibrant φ.i
  have : Cofibration ((DiagSet.Infty.changeLevel m n).map φ.i) := (cofibration_iff _).2 φ.hi.1
  have hlp : HasLiftingProperty (C := DiagSet.Infty.{u} n)
      ((DiagSet.Infty.changeLevel m n).map φ.i) ((DiagSet.toInfty n).map p) :=
    ModelCategory.cm4a _ _
  have sq : CommSq (C := DiagSet.Infty.{u} n) (𝟙 _) ((DiagSet.Infty.changeLevel m n).map φ.i)
      ((DiagSet.toInfty n).map p) ((DiagSet.Infty.changeLevel m n).map φ.p) :=
    ⟨(Category.id_comp _).trans φ.fac.symm⟩
  obtain ⟨⟨l⟩⟩ := hlp.sq_hasLift sq
  exact (fibration_iff _).2 ((fibrations _).of_retract
    { i := Arrow.homMk φ.i (𝟙 _) (by simp)
      r := Arrow.homMk l.l (𝟙 _) (l.fac_right.trans (Category.comp_id _).symm)
      retract := by
        ext
        · exact l.fac_left
        · exact Category.comp_id _ } φ.hp)

end Atoms.Diagrammatic
