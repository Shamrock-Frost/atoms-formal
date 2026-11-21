import Atoms.Diagrammatic.Join
import Atoms.Diagrammatic.Vertex
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.JoinLifting

open CategoryTheory Limits Opposite MorphismProperty Atoms.Shape
open CategoryTheory.WithInitial (join joinInclRight sliceRes slice
  hasLiftingProperty_leibnizSlice_iff)
open scoped Atoms.Diagrammatic.DiagSet.Join

universe u

namespace Atoms.Diagrammatic

def arrowOutput : ball.{u} atomPoint ⟶ ball.{u} (atomGlobe 1) :=
  ballMap (atomGlobeVertex true)

variable {E S : DiagSet.{u}} {x y : E.Vertex}

noncomputable abbrev DiagSet.Edge.sliceTarget (p : E ⟶ S) (e : E.Edge x y) : DiagSet.{u} :=
  pullback ((slice (ball.{u} atomPoint)).map (Under.homMk p (by simp) :
    Under.mk (arrowOutput ≫ uliftYonedaEquiv.symm e.cell) ⟶
      Under.mk (arrowOutput ≫ uliftYonedaEquiv.symm e.cell ≫ p)))
    ((sliceRes arrowOutput).app (Under.mk (uliftYonedaEquiv.symm e.cell ≫ p)))

noncomputable def DiagSet.Edge.leibnizSlice (p : E ⟶ S) (e : E.Edge x y) :
    (slice (ball.{u} (atomGlobe 1))).obj (Under.mk (uliftYonedaEquiv.symm e.cell)) ⟶
      e.sliceTarget p :=
  WithInitial.leibnizSlice arrowOutput p (uliftYonedaEquiv.symm e.cell)

def DiagSet.IsCartesianEdge (p : E ⟶ S) (e : E.Edge x y) : Prop :=
  (monomorphisms DiagSet.{u}).rlp (e.leibnizSlice p)

theorem DiagSet.isCartesianEdge_iff (p : E ⟶ S) (e : E.Edge x y) :
    DiagSet.IsCartesianEdge p e ↔ ∀ ⦃K L : DiagSet.{u}⦄ (i : K ⟶ L) [Mono i]
      (sq : Functor.PushoutObjObj 𝒥 i arrowOutput.{u})
      {a : sq.pt ⟶ E} {b : ((𝒥).obj L).obj (ball.{u} (atomGlobe 1)) ⟶ S} (hsq : CommSq a sq.ι p b),
        joinInclRight K _ ≫ sq.inr ≫ a = uliftYonedaEquiv.symm e.cell → hsq.HasLift := by
  refine ⟨fun h K L i _ sq a b hsq ha ↦ ?_, fun h K L i hi ↦ ?_⟩
  · exact (hasLiftingProperty_leibnizSlice_iff sq p _).1
      (h i (monomorphisms.infer_property i)) hsq ha
  · have : Mono i := hi
    exact (hasLiftingProperty_leibnizSlice_iff
      (Functor.PushoutObjObj.ofHasPushout _ i arrowOutput) p _).2 fun hsq ha ↦ h i _ hsq ha

theorem DiagSet.isCartesianEdge_of_isIso (p : E ⟶ S) [IsIso p] (e : E.Edge x y) :
    DiagSet.IsCartesianEdge p e :=
  (DiagSet.isCartesianEdge_iff p e).2 fun _ _ _ _ _ _ _ hsq _ ↦
    HasLiftingProperty.sq_hasLift hsq

theorem DiagSet.IsCartesianEdge.of_isPullback {E' S' : DiagSet.{u}} {p : E ⟶ S} {p' : E' ⟶ S'}
    {q : E' ⟶ E} {g : S' ⟶ S} (h : IsPullback q p' p g) {x y : E'.Vertex} {e : E'.Edge x y}
    (he : DiagSet.IsCartesianEdge p (e.map q)) : DiagSet.IsCartesianEdge p' e := by
  rw [DiagSet.isCartesianEdge_iff] at he ⊢
  intro K L i _ sq a b hsq ha
  obtain ⟨l⟩ := (he i sq (a := a ≫ q) (b := b ≫ g) ⟨(Category.assoc _ _ _).trans
    ((whisker_eq a h.w).trans ((Category.assoc _ _ _).symm.trans ((hsq.w =≫ g).trans
      (Category.assoc _ _ _))))⟩ (((Category.assoc _ _ _).trans
        (whisker_eq _ (Category.assoc _ _ _))).symm.trans
          ((ha =≫ q).trans (uliftYonedaEquiv_symm_comp _ _)))).exists_lift
  exact ⟨⟨⟨h.lift l.l b l.fac_right, h.hom_ext
    ((Category.assoc _ _ _).trans ((whisker_eq _ (h.lift_fst _ _ _)).trans l.fac_left))
    ((Category.assoc _ _ _).trans ((whisker_eq _ (h.lift_snd _ _ _)).trans hsq.w.symm)),
    h.lift_snd _ _ _⟩⟩⟩

theorem DiagSet.IsCartesianEdge.comp {T : DiagSet.{u}} {p : E ⟶ S} {q : S ⟶ T}
    {e : E.Edge x y} (hp : DiagSet.IsCartesianEdge p e) (hq : DiagSet.IsCartesianEdge q (e.map p)) :
    DiagSet.IsCartesianEdge (p ≫ q) e := by
  rw [DiagSet.isCartesianEdge_iff] at hp hq ⊢
  intro K L i _ sq a b hsq ha
  obtain ⟨l₁⟩ := (hq i sq (a := a ≫ p) (b := b) ⟨(Category.assoc _ _ _).trans hsq.w⟩
    (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).symm.trans
      ((ha =≫ p).trans (uliftYonedaEquiv_symm_comp _ _)))).exists_lift
  obtain ⟨l⟩ := (hp i sq (a := a) (b := l₁.l) ⟨l₁.fac_left.symm⟩ ha).exists_lift
  exact ⟨⟨⟨l.l, l.fac_left, (Category.assoc _ _ _).symm.trans
    ((l.fac_right =≫ q).trans l₁.fac_right)⟩⟩⟩

end Atoms.Diagrammatic
