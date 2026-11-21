import Atoms.Diagrammatic.JoinMonomorphism
import Atoms.Diagrammatic.Joyal.LeibnizJoin
import Atoms.Diagrammatic.Joyal.Quillen
import Atoms.Diagrammatic.Pasting.Paste
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty HomotopicalAlgebra
  Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

section MarkedAbove

theorem weakEquivalence_toInfty_map_iff_markedAbove (n : ℕ) {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence ((DiagSet.toInfty n).map f) ↔
      WeakEquivalence ((MarkedDiagSet.Coinductive.markedAboveFunctor n).map f) := by
  refine ⟨fun h => ?_, weakEquivalence_of_weakEquivalence_markedAboveFunctor_map n f⟩
  have hf := (weakEquivalence_iff _).1 ((weakEquivalence_flat_map_iff n
    ((DiagSet.toInfty n).map f)).2 h)
  have e : (Homotopical.MarkedPresheaf.flat atomMarking).map f ≫ flatToMarkedAbove n Y =
      flatToMarkedAbove n X ≫ (MarkedDiagSet.markedAboveFunctor n).map f :=
    Homotopical.MarkedPresheaf.hom_ext rfl
  have hX := (weakEquivalence_iff _).1 (weakEquivalence_flatToMarkedAbove n X)
  have hY := (weakEquivalence_iff _).1 (weakEquivalence_flatToMarkedAbove n Y)
  exact (weakEquivalence_iff _).2 ((weakEquivalences _).of_precomp _ _ hX
    ((congrArg (fun g => weakEquivalences (MarkedDiagSet.Coinductive n) g) e).mp
      ((weakEquivalences _).comp_mem _ _ hf hY)))

end MarkedAbove

private def closedSubpresheafArrowIsoOfEq {W : Atom} {S S' : LowerSet W.ogp} (h : S = S') :
    Arrow.mk (closedSubpresheaf.{u} W S).ι ≅ Arrow.mk (closedSubpresheaf.{u} W S').ι := by
  subst h
  exact Iso.refl _

noncomputable def toMergerInclusionArrowIso (U : RoundShape) (hU : 0 < U.dimension) :
    Arrow.mk (toMergerInclusion.{u} U hU) ≅
      Arrow.mk (closedSubpresheaf.{u} (toMergerAtom U hU)
        ((toMergerAtom U hU).ogp.boundary ⊤ U.dimension false)).ι := by
  have h : map (toMergerInputIncl U hU) ⊤ =
      (toMergerAtom U hU).ogp.boundary ⊤ U.dimension false :=
    (U.map_inputIncl _).trans (bdry_eq_boundary
      ((toMergerAtom U hU).krullDim_top_eq (dimension_toMergerAtom U hU)) false)
  let e := realize.{u}.mapIso (restrictIso (R := atomToRDCpx.obj (toMergerAtom U hU))
    (U := U.rdc) (toMergerInputIncl U hU)) ≪≫
    realizeRestrictIso _ _ _ rfl ≪≫ realizeSubsetAtomIso (toMergerAtom U hU) _
  refine (Arrow.isoMk (g := Arrow.mk (closedSubpresheaf.{u} (toMergerAtom U hU)
    (map (toMergerInputIncl U hU) ⊤)).ι) e (Iso.refl _) ?_) ≪≫ closedSubpresheafArrowIsoOfEq h
  ext T g
  rfl

theorem weakEquivalence_toInfty_pushoutObjObj_ι_boundary_sphereInclusion (U V : Atom) (k : ℕ)
    (α : Bool) (hα : α = true ∨ 1 ≤ k) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (closedSubpresheaf.{u} U (U.ogp.boundary ⊤ k α)).ι (sphereInclusion.{u} V)).ι) :=
  (weakEquivalence_toInfty_map_iff_markedAbove 1 _).2
    (weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_sphereInclusion 1 U V k α hα)

theorem weakEquivalence_toInfty_pushoutObjObj_ι_toMergerInclusion (U : RoundShape)
    (hU : 0 < U.dimension) (V : Atom) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (toMergerInclusion.{u} U hU) (sphereInclusion.{u} V)).ι) := by
  have := (weakEquivalence_toInfty_pushoutObjObj_ι_boundary_sphereInclusion.{u}
    (toMergerAtom U hU) V U.dimension false (Or.inr hU))
  rw [weakEquivalence_iff] at this ⊢
  exact ((weakEquivalences (DiagSet.Infty.{u} 1)).arrow_mk_iso_iff
    (Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (sphereInclusion.{u} V))
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (toMergerInclusion.{u} U hU) (sphereInclusion V))
      (Functor.PushoutObjObj.ofHasPushout 𝒥 _ _) (toMergerInclusionArrowIso U hU))).2 this

private theorem trivialCofibration_pushoutObjObj_ι_toMergerInclusion (U : RoundShape)
    (hU : 0 < U.dimension) (V : Atom) :
    trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (toMergerInclusion.{u} U hU)
        (sphereInclusion.{u} V)).ι) := by
  refine ⟨(cofibration_iff _).1 ((cofibration_iff _).2 ?_),
    (weakEquivalence_iff _).1 (weakEquivalence_toInfty_pushoutObjObj_ι_toMergerInclusion U hU V)⟩
  have : Mono (toMergerInclusion.{u} U hU) :=
    haveI := mono_realize_map (RDCpx.ofInclusion (P := U.rdc)
      (Q := atomToRDCpx.obj (toMergerAtom U hU)) (toMergerInputIncl U hU))
      (IsInclusion.injective (f := toMergerInputIncl U hU))
    mono_comp _ _
  exact mono_pushoutObjObj_ι_join _ _

theorem weakEquivalence_toInfty_pushoutObjObj_ι_compositor (U : RoundShape)
    (hU : 0 < U.dimension) (V : Atom)
    (h : WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (toWalkingEquivalence.{u} (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU))
      (sphereInclusion.{u} V)).ι)) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout 𝒥
      (toMergerInclusion.{u} U hU ≫
        toWalkingEquivalence (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU))
      (sphereInclusion.{u} V)).ι) := by
  rw [weakEquivalence_iff] at h ⊢
  exact pushoutObjObj_ι_comp_left_mem (P := trivialCofibrations (DiagSet.Infty.{u} 1))
    (W := weakEquivalences (DiagSet.Infty.{u} 1)) (fun _ _ _ hf => hf.2) _ _ _
    (trivialCofibration_pushoutObjObj_ι_toMergerInclusion U hU V) h

end Atoms.Diagrammatic
