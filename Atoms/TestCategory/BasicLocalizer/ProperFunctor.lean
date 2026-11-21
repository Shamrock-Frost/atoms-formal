import Atoms.ForMathlib.CategoryTheory.Category.Cat.Fiber
import Atoms.TestCategory.BasicLocalizer.Opposite

open CategoryTheory Limits

namespace Atoms.TestCategory.BasicLocalizer

universe u

variable (𝒲 : BasicLocalizer.{u})

def CoasphericalFunctor {A B : Cat.{u, u}} (u : A ⟶ B) : Prop :=
  ∀ b : B, 𝒲.Aspherical (Cat.of (StructuredArrow b u.toFunctor))

def ProperFunctor {A B : Cat.{u, u}} (u : A ⟶ B) : Prop :=
  ∀ b : B, 𝒲.CoasphericalFunctor
    ((Functor.Fiber.toCostructuredArrow u.toFunctor b).toCatHom :
      Cat.of (Functor.Fiber u.toFunctor b) ⟶ Cat.of (CostructuredArrow u.toFunctor b))

private theorem aspherical_iff_of_isEquivalence {C D : Type u} {_ : Category.{u} C}
    {_ : Category.{u} D} {F : C ⥤ D} (hF : F.IsEquivalence) :
    𝒲.Aspherical (Cat.of C) ↔ 𝒲.Aspherical (Cat.of D) :=
  𝒲.aspherical_iff_of_equivalence (@Functor.asEquivalence _ _ _ _ F hF)

theorem properFunctor_iff_aspherical_fiber {A B : Cat.{u, u}} (u : A ⟶ B) :
    𝒲.ProperFunctor u ↔ ∀ (a : A) (y : Under (u.toFunctor.obj a)),
      𝒲.Aspherical (Cat.of (Functor.Fiber (Under.post (X := a) u.toFunctor) y)) := by
  refine ⟨fun hu a y => ?_, fun h b x => ?_⟩
  · exact (aspherical_iff_of_isEquivalence 𝒲
      (Functor.Fiber.isEquivalence_underPostToStructuredArrow (u := u.toFunctor) (y := y))).2
        (hu y.right (CostructuredArrow.mk y.hom))
  · exact (aspherical_iff_of_isEquivalence 𝒲
      (Functor.Fiber.isEquivalence_underPostToStructuredArrow (u := u.toFunctor)
        (y := Under.mk x.hom))).1 (h x.left (Under.mk x.hom))

theorem properFunctor_of_isPullback {A' A B' B : Cat.{u, u}} {w : A' ⟶ A} {u' : A' ⟶ B'}
    {u : A ⟶ B} {v : B' ⟶ B} (h : IsPullback w u' u v) (hu : 𝒲.ProperFunctor u) :
    𝒲.ProperFunctor u' := by
  rw [properFunctor_iff_aspherical_fiber] at hu ⊢
  intro a' y'
  exact (aspherical_iff_of_isEquivalence 𝒲 (Cat.isEquivalence_mapOfSquare_of_isPullback
    (Cat.isPullback_underPost_of_isPullback h a') y')).2 (hu _ _)

theorem asphericalFunctor_iff_aspherical_fiber_of_properFunctor {A B : Cat.{u, u}} {u : A ⟶ B}
    (hu : 𝒲.ProperFunctor u) :
    𝒲.AsphericalFunctor u ↔ ∀ b : B, 𝒲.Aspherical (Cat.of (Functor.Fiber u.toFunctor b)) :=
  forall_congr' fun b =>
    (𝒲.aspherical_iff_of_W _ (𝒲.W_of_forall_aspherical_structuredArrow _ (hu b))).symm

theorem asphericalFunctor_of_isPullback_of_properFunctor {A' A B' B : Cat.{u, u}} {w : A' ⟶ A}
    {u' : A' ⟶ B'} {u : A ⟶ B} {v : B' ⟶ B} (h : IsPullback w u' u v)
    (hu : 𝒲.ProperFunctor u) (hu' : 𝒲.AsphericalFunctor u) : 𝒲.AsphericalFunctor u' := by
  have hfib := (𝒲.asphericalFunctor_iff_aspherical_fiber_of_properFunctor hu).1 hu'
  refine (𝒲.asphericalFunctor_iff_aspherical_fiber_of_properFunctor
    (𝒲.properFunctor_of_isPullback h hu)).2 fun b' => ?_
  exact (aspherical_iff_of_isEquivalence 𝒲 (Cat.isEquivalence_mapOfSquare_of_isPullback h b')).2
    (hfib _)

theorem asphericalFunctor_of_forall_isPullback_W {A B : Cat.{u, u}} {u : A ⟶ B}
    (hu : 𝒲.ProperFunctor u)
    (hW : ∀ {A' B' : Cat.{u, u}} (w : A' ⟶ A) (u' : A' ⟶ B') (v : B' ⟶ B),
      IsPullback w u' u v → 𝒲.W u') :
    𝒲.AsphericalFunctor u := by
  refine (𝒲.asphericalFunctor_iff_aspherical_fiber_of_properFunctor hu).2 fun b => ?_
  exact (𝒲.aspherical_iff_W _ (𝒲.terminal_aspherical _)).2
    (hW _ _ _ (Cat.isPullback_fiberInclusion_fromPUnit u b))

theorem properFunctor_under_post {A B : Cat.{u, u}} {u : A ⟶ B} (hu : 𝒲.ProperFunctor u)
    (a : A) :
    𝒲.ProperFunctor ((Under.post (X := a) u.toFunctor).toCatHom :
      Cat.of (Under a) ⟶ Cat.of (Under (u.toFunctor.obj a))) := by
  rw [properFunctor_iff_aspherical_fiber] at hu ⊢
  intro z y'
  exact (aspherical_iff_of_isEquivalence 𝒲 (Cat.isEquivalence_mapOfSquare_of_isPullback
    (Cat.isPullback_underPost_underPost u z) y')).2 (hu _ _)

theorem asphericalFunctor_under_post {A B : Cat.{u, u}} {u : A ⟶ B} (hu : 𝒲.ProperFunctor u)
    (a : A) :
    𝒲.AsphericalFunctor ((Under.post (X := a) u.toFunctor).toCatHom :
      Cat.of (Under a) ⟶ Cat.of (Under (u.toFunctor.obj a))) :=
  (𝒲.asphericalFunctor_iff_aspherical_fiber_of_properFunctor (𝒲.properFunctor_under_post hu a)).2
    ((𝒲.properFunctor_iff_aspherical_fiber u).1 hu a)

theorem properFunctor_comp {A B C : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ C}
    (hu : 𝒲.ProperFunctor u) (hv : 𝒲.ProperFunctor v) : 𝒲.ProperFunctor (u ≫ v) := by
  refine (𝒲.properFunctor_iff_aspherical_fiber _).2 fun a y => ?_
  let P := (Under.post (X := a) u.toFunctor).toCatHom
  let Q := (Under.post (X := u.toFunctor.obj a) v.toFunctor).toCatHom
  have hpb := Cat.isPullback_fiberInclusion_mapOfSquare_comp P Q y
  have hL := 𝒲.asphericalFunctor_of_isPullback_of_properFunctor hpb
    (𝒲.properFunctor_under_post hu a) (𝒲.asphericalFunctor_under_post hu a)
  exact (𝒲.aspherical_iff_of_W _ (𝒲.W_of_asphericalFunctor hL)).2
    ((𝒲.properFunctor_iff_aspherical_fiber v).1 hv (u.toFunctor.obj a) y)

end Atoms.TestCategory.BasicLocalizer
