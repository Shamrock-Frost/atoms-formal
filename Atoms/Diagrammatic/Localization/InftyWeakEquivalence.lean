import Atoms.Diagrammatic.Localization.MappingPathSpace
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.HomotopyInverse

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}} (f : X ⟶ Y)

private theorem isFibrant_of_isInftyCategory (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) : reversibleCylinder.{u}.IsFibrant (inftyGenerators.{u} n) X :=
  (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder.{u} (inftyGenerators.{u} n)
    (inftyGenerators_le_monomorphisms n) X).1 ((isFibrant_infty_iff n X).2 hX)

theorem weakEquivalence_iff_isOmegaEquivalence (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) :
    WeakEquivalence ((DiagSet.toInfty n).map f) ↔ IsOmegaEquivalence f := by
  have e : (monomorphisms DiagSet.{u}).rlp (reversibleMappingPathSpaceProj f) ↔
      trivialFibrations (DiagSet.Infty.{u} n)
        ((DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f)) := by
    rw [← cofibrations_rlp]
    exact Iff.rfl
  rw [isOmegaEquivalence_iff_rlp_reversibleMappingPathSpaceProj f n hX hY, e]
  have := weakEquivalence_reversibleMappingPathSpaceIncl f n hY
  have := fibration_reversibleMappingPathSpaceProj f n hX hY
  have e' : (DiagSet.toInfty n).map f = (DiagSet.toInfty n).map (reversibleMappingPathSpaceIncl f) ≫
      (DiagSet.toInfty n).map (reversibleMappingPathSpaceProj f) := by
    rw [← Functor.map_comp, reversibleMappingPathSpaceIncl_proj]
  rw [e', weakEquivalence_precomp_iff]
  exact ⟨fun h => ⟨(fibration_iff _).1 inferInstance, (weakEquivalence_iff _).1 h⟩,
    fun h => (weakEquivalence_iff _).2 h.2⟩

theorem isOmegaEquivalence_iff_homotopyEquivalence (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) :
    IsOmegaEquivalence f ↔ ∃ g : Y ⟶ X, reversibleCylinder.Homotopic (f ≫ g) (𝟙 X) ∧
      reversibleCylinder.Homotopic (g ≫ f) (𝟙 Y) := by
  rw [← weakEquivalence_iff_isOmegaEquivalence f n hX hY, weakEquivalence_iff]
  exact ⟨reversibleCylinder.exists_homotopy_inverse_of_weakEquivalences _
      (isFibrant_of_isInftyCategory n hX) (isFibrant_of_isInftyCategory n hY) f,
    fun ⟨g, hfg, hgf⟩ => reversibleCylinder.weakEquivalences_of_homotopic _ f g hfg hgf⟩

theorem IsOmegaEquivalence.equivalent_of_equivalent_mapTo (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) (hf : IsOmegaEquivalence f) {a b : RoundPastingDiagram X}
    (hab : Parallel a b) (h : Equivalent (a.mapTo f) (b.mapTo f)) : Equivalent a b := by
  have hc (c : RoundPastingDiagram X) {W V : DiagSet.{u}} (g : X ⟶ W) (q : W ⟶ V) (r : X ⟶ V)
      (hgq : g ≫ q = r) : (c.mapTo g).mapTo q = c.mapTo r :=
    RoundPastingDiagram.ext ((PastingDiagram.mapTo_comp _ g q).symm.trans (by rw [hgq]; rfl))
  have h' := equivalent_of_rlp_monomorphisms
    ((isOmegaEquivalence_iff_rlp_reversibleMappingPathSpaceProj f n hX hY).1 hf) hY.1
    (hab.mapTo (reversibleMappingPathSpaceIncl f))
    (by rwa [hc a _ _ _ (reversibleMappingPathSpaceIncl_proj f),
      hc b _ _ _ (reversibleMappingPathSpaceIncl_proj f)])
  have e (c : RoundPastingDiagram X) :
      (c.mapTo (reversibleMappingPathSpaceIncl f)).mapTo (pullback.fst _ _) = c :=
    (hc c _ _ _ (reversibleMappingPathSpaceIncl_fst f)).trans
      (RoundPastingDiagram.mapTo_id c)
  exact (congrArg₂ Equivalent (e a) (e b)).mp (h'.map (pullback.fst _ _))

theorem IsOmegaEquivalence.of_comp_left (n : ℕ∞) {g : Y ⟶ Z} (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) (hZ : IsInftyCategory n Z) (hfg : IsOmegaEquivalence (f ≫ g))
    (hg : IsOmegaEquivalence g) : IsOmegaEquivalence f := by
  rw [← weakEquivalence_iff_isOmegaEquivalence f n hX hY]
  have := (weakEquivalence_iff_isOmegaEquivalence g n hY hZ).2 hg
  have := (weakEquivalence_iff_isOmegaEquivalence (f ≫ g) n hX hZ).2 hfg
  rw [Functor.map_comp] at this
  exact weakEquivalence_of_postcomp _ ((DiagSet.toInfty n).map g)

theorem IsOmegaEquivalence.of_comp_right (n : ℕ∞) {g : Y ⟶ Z} (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) (hZ : IsInftyCategory n Z) (hf : IsOmegaEquivalence f)
    (hfg : IsOmegaEquivalence (f ≫ g)) : IsOmegaEquivalence g := by
  rw [← weakEquivalence_iff_isOmegaEquivalence g n hY hZ]
  have := (weakEquivalence_iff_isOmegaEquivalence f n hX hY).2 hf
  have := (weakEquivalence_iff_isOmegaEquivalence (f ≫ g) n hX hZ).2 hfg
  rw [Functor.map_comp] at this
  exact weakEquivalence_of_precomp ((DiagSet.toInfty n).map f) _

theorem IsOmegaEquivalence.of_homotopic (n : ℕ∞) {f g : X ⟶ Y} (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) (h : reversibleCylinder.Homotopic f g)
    (hf : IsOmegaEquivalence f) : IsOmegaEquivalence g := by
  rw [← weakEquivalence_iff_isOmegaEquivalence g n hX hY, weakEquivalence_iff]
  have hf' := (weakEquivalence_iff _).1 ((weakEquivalence_iff_isOmegaEquivalence f n hX hY).2 hf)
  exact fun T hT => (congrArg Function.Bijective
    (reversibleCylinder.precompClasses_eq_of_homotopic h T)).mp (hf' T hT)

theorem IsOmegaEquivalence.of_left_inverse_of_right_inverse (n : ℕ∞) (hX : IsInftyCategory n X)
    (hY : IsInftyCategory n Y) {g h : Y ⟶ X}
    (hg : reversibleCylinder.Homotopic (f ≫ g) (𝟙 X))
    (hh : reversibleCylinder.Homotopic (h ≫ f) (𝟙 Y)) : IsOmegaEquivalence f :=
  (isOmegaEquivalence_iff_homotopyEquivalence f n hX hY).2
    ⟨h, (reversibleCylinder.homotopyInverse_of_left_inverse_of_right_inverse hg hh).2, hh⟩

end Atoms.Diagrammatic
