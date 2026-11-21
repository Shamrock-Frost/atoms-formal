import Atoms.Diagrammatic.Localization.OmegaEquivalence
import Atoms.Diagrammatic.Marked.FlatEquivalence
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.PathObject

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

instance isLeftAdjoint_reversibleCylinder : reversibleCylinder.{u}.I.IsLeftAdjoint :=
  haveI : PreservesColimitsOfSize.{0, u} reversibleCylinder.{u}.I :=
    preservesColimitsOfSize_shrink _
  Presheaf.isLeftAdjoint_of_preservesColimits.{u} _

noncomputable def reversiblePathSpace : DiagSet.{u} ⥤ DiagSet.{u} :=
  reversibleCylinder.{u}.I.rightAdjoint

noncomputable def reversiblePathSpaceAdjunction :
    reversibleCylinder.{u}.I ⊣ reversiblePathSpace.{u} :=
  Adjunction.ofIsLeftAdjoint _

noncomputable def reversiblePathSpaceCellEquiv (X : DiagSet.{u}) (U : Atom) :
    diagram (reversiblePathSpace.obj X) U ≃ (reversibleCylinder.{u}.I.obj (ball.{u} U) ⟶ X) :=
  uliftYonedaEquiv.symm.trans (reversiblePathSpaceAdjunction.homEquiv _ _).symm

namespace ReversiblePathSpace

scoped notation "π̃" =>
  ExactCylinder.pathEndpoint reversibleCylinder reversiblePathSpaceAdjunction

scoped notation "ν̃" =>
  ExactCylinder.pathConstant reversibleCylinder reversiblePathSpaceAdjunction

end ReversiblePathSpace

open scoped ReversiblePathSpace

private theorem isFibrant_reversibleCylinder_of_isInftyCategory (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) : reversibleCylinder.{u}.IsFibrant (inftyGenerators.{u} n) X :=
  (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder.{u} (inftyGenerators.{u} n)
    (inftyGenerators_le_monomorphisms n) X).1 ((isFibrant_infty_iff n X).2 hX)

private theorem isInftyCategory_of_isFibrant_reversibleCylinder (n : ℕ∞) {X : DiagSet.{u}}
    (hX : reversibleCylinder.{u}.IsFibrant (inftyGenerators.{u} n) X) : IsInftyCategory n X :=
  (isFibrant_infty_iff n X).1 ((ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder.{u}
    (inftyGenerators.{u} n) (inftyGenerators_le_monomorphisms n) X).2 hX)

theorem isInftyCategory_reversiblePathSpace_obj (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) : IsInftyCategory n (reversiblePathSpace.obj X) := by
  have hS := inftyGenerators_le_monomorphisms.{u} n
  refine isInftyCategory_of_isFibrant_reversibleCylinder n ?_
  rw [← reversibleCylinder.{u}.rlp_trivialCofibrations_terminal_from_iff _ hS]
  exact reversibleCylinder.{u}.fibrations_terminal_from_obj reversiblePathSpaceAdjunction _ hS
    ((reversibleCylinder.{u}.rlp_trivialCofibrations_terminal_from_iff _ hS X).2
      (isFibrant_reversibleCylinder_of_isInftyCategory n hX))

theorem rlp_monomorphisms_reversiblePathEndpoint_app (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) (α : Bool) :
    (monomorphisms DiagSet.{u}).rlp ((π̃ α).app X) :=
  reversibleCylinder.{u}.rlp_monomorphisms_pathEndpoint_app _ (inftyGenerators.{u} n)
    (isFibrant_reversibleCylinder_of_isInftyCategory n hX) α

theorem trivialFibrations_reversiblePathEndpoint_app (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) (α : Bool) :
    trivialFibrations (DiagSet.Infty.{u} n)
      ((DiagSet.toInfty n).map ((π̃ α).app X)) := by
  rw [← cofibrations_rlp]
  exact rlp_monomorphisms_reversiblePathEndpoint_app n hX α

theorem fibrations_reversiblePathEndpoints_app (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) :
    fibrations (DiagSet.Infty.{u} n) ((DiagSet.toInfty n).map
      (reversibleCylinder.{u}.pathEndpoints reversiblePathSpaceAdjunction X)) := by
  have hS := inftyGenerators_le_monomorphisms.{u} n
  have hXf := isFibrant_reversibleCylinder_of_isInftyCategory n hX
  exact reversibleCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne _ hS _
    (reversibleCylinder.{u}.naiveFibrations_pathEndpoints _ _ hS hXf)
    (reversibleCylinder.{u}.isFibrant_prod _ hXf hXf)

private theorem mapTo_mapTo_of_comp_eq_id {X Y : DiagSet.{u}} {s : Y ⟶ X} {p : X ⟶ Y}
    (hs : s ≫ p = 𝟙 Y) (a : RoundPastingDiagram Y) : (a.mapTo s).mapTo p = a :=
  RoundPastingDiagram.ext (congrArg (PastingDiagram.mk a.shape)
    ((Category.assoc _ _ _).trans ((congrArg (a.map ≫ ·) hs).trans (Category.comp_id _))))

theorem isOmegaEquivalence_of_comp_eq_id {X Y : DiagSet.{u}} {p : X ⟶ Y}
    (hp : (monomorphisms DiagSet.{u}).rlp p) (hY : HasWeakComposites Y) {s : Y ⟶ X}
    (hs : s ≫ p = 𝟙 Y) : IsOmegaEquivalence s := by
  have hsp (V : Atom) (y : diagram Y V) : p.app (op V) (s.app (op V) y) = y := by
    simpa using congrArg (fun φ : Y ⟶ Y => φ.app (op V) y) hs
  have himg (V : Atom) (w : diagram X V) : Equivalent ((cellRound w).mapTo p)
      ((cellRound (s.app (op V) (p.app (op V) w))).mapTo p) := by
    rw [← cellRound_app, ← cellRound_app, hsp]
    exact equivalent_refl _
  refine ⟨fun V hV w => ⟨p.app (op V) w, ?_⟩, fun a b _ V w hw => ?_⟩
  · exact equivalent_of_rlp_monomorphisms hp hY ⟨rfl, Or.inl hV⟩ (himg V w)
  · have hx : HasRoundType (PastingDiagram.ofCell (p.app (op V) w)) a b := by
      have h := hw.mapTo p
      rwa [mapTo_mapTo_of_comp_eq_id hs, mapTo_mapTo_of_comp_eq_id hs,
        ← PastingDiagram.ofCell_app] at h
    have hsx : HasRoundType (PastingDiagram.ofCell (s.app (op V) (p.app (op V) w)))
        (a.mapTo s) (b.mapTo s) := by
      rw [PastingDiagram.ofCell_app]
      exact hx.mapTo s
    exact ⟨p.app (op V) w, hx,
      equivalent_of_rlp_monomorphisms hp hY (HasRoundType.parallel hw hsx) (himg V w)⟩

theorem isOmegaEquivalence_reversiblePathConstant_app (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) : IsOmegaEquivalence (ν̃.app X) :=
  isOmegaEquivalence_of_comp_eq_id (rlp_monomorphisms_reversiblePathEndpoint_app n hX false) hX.1
    (reversibleCylinder.pathConstant_app_comp_pathEndpoint_app _ false X)

theorem exists_reversibleCylinder_extension (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) (α : Bool) {U : Atom}
    (γ : sphere.{u} U ⟶ reversiblePathSpace.obj X) (x : ball.{u} U ⟶ X)
    (h : γ ≫ (π̃ α).app X = sphereInclusion U ≫ x) : ∃ g : ball.{u} U ⟶ reversiblePathSpace.obj X,
      sphereInclusion U ≫ g = γ ∧ g ≫ (π̃ α).app X = x := by
  have := rlp_monomorphisms_reversiblePathEndpoint_app n hX α (sphereInclusion U)
    (monomorphisms.infer_property _)
  have sq : CommSq γ (sphereInclusion U) ((π̃ α).app X) x := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

theorem equivalent_reversiblePathEndpoint_of_equivalent (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) {U V : Atom} {g : diagram (reversiblePathSpace.obj X) U}
    {g' : diagram (reversiblePathSpace.obj X) V} (hg : Parallel (cellRound g) (cellRound g'))
    (α : Bool)
    (h : Equivalent (cellRound (((π̃ α).app X).app (op U) g))
      (cellRound (((π̃ α).app X).app (op V) g'))) :
    Equivalent (cellRound (((π̃ (!α)).app X).app (op U) g))
      (cellRound (((π̃ (!α)).app X).app (op V) g')) := by
  rw [cellRound_app, cellRound_app] at h ⊢
  exact (equivalent_of_rlp_monomorphisms (rlp_monomorphisms_reversiblePathEndpoint_app n hX α)
    hX.1 hg h).map _

theorem equivalent_reversiblePathEndpoint_of_sphereInclusion_comp_eq (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) {U : Atom} {g g' : ball.{u} U ⟶ reversiblePathSpace.obj X}
    (hg : sphereInclusion U ≫ g = sphereInclusion U ≫ g') (α : Bool)
    (h : Equivalent (cellRound (uliftYonedaEquiv (g ≫ (π̃ α).app X)))
      (cellRound (uliftYonedaEquiv (g' ≫ (π̃ α).app X)))) :
    Equivalent (cellRound (uliftYonedaEquiv (g ≫ (π̃ (!α)).app X)))
      (cellRound (uliftYonedaEquiv (g' ≫ (π̃ (!α)).app X))) :=
  equivalent_reversiblePathEndpoint_of_equivalent n hX
    (parallel_cellRound_of_sphereInclusion_comp_eq hg) α h

end Atoms.Diagrammatic
