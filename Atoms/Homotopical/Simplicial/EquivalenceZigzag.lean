import Atoms.Homotopical.Simplicial.FullyFaithful
import Atoms.Homotopical.Simplicial.JoyalOp
import Atoms.Homotopical.Simplicial.ZeroObject

open CategoryTheory Simplicial HomotopicalAlgebra

universe u

namespace SSet

theorem IsoVertices.isFinal_iff {X : SSet.{u}} [X.Quasicategory] {x y : X _⦋0⦌}
    (h : IsoVertices x y) : IsFinal x ↔ IsFinal y := by
  obtain ⟨i⟩ := h
  obtain ⟨e, he⟩ := Truncated.HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj X) (x := x) (y := y) i.hom
  obtain ⟨e', he'⟩ := Truncated.HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj X) (x := y) (y := x) i.inv
  exact ⟨isFinal_of_isIso_homMk e (he ▸ Iso.isIso_hom i),
    isFinal_of_isIso_homMk e' (he' ▸ Iso.isIso_inv i)⟩

theorem IsoVertices.isInitialObject_iff {X : SSet.{u}} [X.Quasicategory] {x y : X _⦋0⦌}
    (h : IsoVertices x y) : IsInitialObject x ↔ IsInitialObject y := by
  obtain ⟨i⟩ := h
  obtain ⟨e, he⟩ := Truncated.HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj X) (x := x) (y := y) i.hom
  obtain ⟨e', he'⟩ := Truncated.HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj X) (x := y) (y := x) i.inv
  exact ⟨isInitialObject_of_isIso_homMk e (he ▸ Iso.isIso_hom i),
    isInitialObject_of_isIso_homMk e' (he' ▸ Iso.isIso_inv i)⟩

open modelCategoryJoyal in
theorem modelCategoryJoyal.exists_isoVertices_of_weakEquivalence {X Y : SSet.{u}}
    [X.Quasicategory] [Y.Quasicategory] (f : X ⟶ Y) [WeakEquivalence f] (y : Y _⦋0⦌) :
    ∃ x : X _⦋0⦌, IsoVertices (f.app _ x) y := by
  obtain ⟨x', ⟨i⟩⟩ := (essSurj_of_weakEquivalence f).mem_essImage
    (Truncated.HomotopyCategory.mk y)
  obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective x'
  exact ⟨x, ⟨i⟩⟩

open Atoms.Homotopical modelCategoryJoyal in
theorem modelCategoryJoyal.isoVertices_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (f : X ⟶ Y) [WeakEquivalence f] {x y : X _⦋0⦌}
    (h : IsoVertices (f.app _ x) (f.app _ y)) : IsoVertices x y := by
  have hX := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    X).1 ((isFibrant_iff_quasicategory X).2 inferInstance)
  have hY := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    Y).1 ((isFibrant_iff_quasicategory Y).2 inferInstance)
  obtain ⟨g, hg, -⟩ := joyalInterval.cylinder.exists_homotopy_inverse_of_weakEquivalences _ hX hY f
    ((weakEquivalence_iff f).1 ‹_›)
  have hx : IsoVertices (g.app _ (f.app _ x)) x := isoVertices_of_homotopic hg x
  have hy : IsoVertices (g.app _ (f.app _ y)) y := isoVertices_of_homotopic hg y
  exact hx.symm.trans ((h.map g).trans hy)

open modelCategoryJoyal in
structure EquivalenceZigzag (Q₀ Q₄ : SSet.{u}) where
  left : SSet.{u}
  mid : SSet.{u}
  right : SSet.{u}
  sourceToLeft : Q₀ ⟶ left
  midToLeft : mid ⟶ left
  midToRight : mid ⟶ right
  targetToRight : Q₄ ⟶ right
  quasicategory_source : Q₀.Quasicategory
  quasicategory_left : left.Quasicategory
  quasicategory_mid : mid.Quasicategory
  quasicategory_right : right.Quasicategory
  quasicategory_target : Q₄.Quasicategory
  weakEquivalence_sourceToLeft : WeakEquivalence sourceToLeft
  weakEquivalence_midToLeft : WeakEquivalence midToLeft
  weakEquivalence_midToRight : WeakEquivalence midToRight
  weakEquivalence_targetToRight : WeakEquivalence targetToRight

namespace EquivalenceZigzag

variable {Q₀ Q₄ : SSet.{u}} (z : EquivalenceZigzag Q₀ Q₄)

def Related (x : Q₀ _⦋0⦌) (y : Q₄ _⦋0⦌) : Prop :=
  ∃ v : z.mid _⦋0⦌, IsoVertices (z.sourceToLeft.app _ x) (z.midToLeft.app _ v) ∧
    IsoVertices (z.midToRight.app _ v) (z.targetToRight.app _ y)

open modelCategoryJoyal in
theorem exists_related_right (x : Q₀ _⦋0⦌) : ∃ y : Q₄ _⦋0⦌, z.Related x y := by
  have := z.quasicategory_left
  have := z.quasicategory_mid
  have := z.quasicategory_right
  have := z.quasicategory_target
  have := z.weakEquivalence_midToLeft
  have := z.weakEquivalence_targetToRight
  obtain ⟨v, hv⟩ := exists_isoVertices_of_weakEquivalence z.midToLeft (z.sourceToLeft.app _ x)
  obtain ⟨y, hy⟩ := exists_isoVertices_of_weakEquivalence z.targetToRight (z.midToRight.app _ v)
  exact ⟨y, v, hv.symm, hy.symm⟩

open modelCategoryJoyal in
theorem exists_related_left (y : Q₄ _⦋0⦌) : ∃ x : Q₀ _⦋0⦌, z.Related x y := by
  have := z.quasicategory_source
  have := z.quasicategory_left
  have := z.quasicategory_mid
  have := z.quasicategory_right
  have := z.weakEquivalence_sourceToLeft
  have := z.weakEquivalence_midToRight
  obtain ⟨v, hv⟩ := exists_isoVertices_of_weakEquivalence z.midToRight (z.targetToRight.app _ y)
  obtain ⟨x, hx⟩ := exists_isoVertices_of_weakEquivalence z.sourceToLeft (z.midToLeft.app _ v)
  exact ⟨x, v, hx, hv⟩

open modelCategoryJoyal in
theorem isFinal_iff_of_related {x : Q₀ _⦋0⦌} {y : Q₄ _⦋0⦌} (h : z.Related x y) :
    IsFinal x ↔ IsFinal y := by
  have := z.quasicategory_source
  have := z.quasicategory_left
  have := z.quasicategory_mid
  have := z.quasicategory_right
  have := z.quasicategory_target
  have := z.weakEquivalence_sourceToLeft
  have := z.weakEquivalence_midToLeft
  have := z.weakEquivalence_midToRight
  have := z.weakEquivalence_targetToRight
  obtain ⟨v, hl, hr⟩ := h
  rw [← isFinal_iff_of_weakEquivalence z.sourceToLeft x, hl.isFinal_iff,
    isFinal_iff_of_weakEquivalence z.midToLeft v, ← isFinal_iff_of_weakEquivalence z.midToRight v,
    hr.isFinal_iff, isFinal_iff_of_weakEquivalence z.targetToRight y]

open modelCategoryJoyal in
theorem isInitialObject_iff_of_related {x : Q₀ _⦋0⦌} {y : Q₄ _⦋0⦌} (h : z.Related x y) :
    IsInitialObject x ↔ IsInitialObject y := by
  have := z.quasicategory_source
  have := z.quasicategory_left
  have := z.quasicategory_mid
  have := z.quasicategory_right
  have := z.quasicategory_target
  have := z.weakEquivalence_sourceToLeft
  have := z.weakEquivalence_midToLeft
  have := z.weakEquivalence_midToRight
  have := z.weakEquivalence_targetToRight
  obtain ⟨v, hl, hr⟩ := h
  rw [← isInitialObject_iff_of_weakEquivalence z.sourceToLeft x, hl.isInitialObject_iff,
    isInitialObject_iff_of_weakEquivalence z.midToLeft v,
    ← isInitialObject_iff_of_weakEquivalence z.midToRight v, hr.isInitialObject_iff,
    isInitialObject_iff_of_weakEquivalence z.targetToRight y]

open modelCategoryJoyal in
theorem isoVertices_of_related {A B M : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (e : A ⟶ B) [WeakEquivalence e] (m : M ⟶ B) (p₀ : Q₀ ⟶ A) (pl : z.left ⟶ B) (pm : z.mid ⟶ M)
    (pr : z.right ⟶ B) (p₄ : Q₄ ⟶ A) (h₀ : z.sourceToLeft ≫ pl = p₀ ≫ e)
    (h₁ : z.midToLeft ≫ pl = pm ≫ m) (h₂ : z.midToRight ≫ pr = pm ≫ m)
    (h₃ : z.targetToRight ≫ pr = p₄ ≫ e) {x : Q₀ _⦋0⦌} {y : Q₄ _⦋0⦌} (h : z.Related x y) :
    IsoVertices (p₀.app _ x) (p₄.app _ y) := by
  obtain ⟨v, hl, hr⟩ := h
  have e₀ : pl.app _ (z.sourceToLeft.app _ x) = e.app _ (p₀.app _ x) :=
    congrArg (fun f : Q₀ ⟶ B ↦ f.app _ x) h₀
  have e₁ : pl.app _ (z.midToLeft.app _ v) = m.app _ (pm.app _ v) :=
    congrArg (fun f : z.mid ⟶ B ↦ f.app _ v) h₁
  have e₂ : pr.app _ (z.midToRight.app _ v) = m.app _ (pm.app _ v) :=
    congrArg (fun f : z.mid ⟶ B ↦ f.app _ v) h₂
  have e₃ : pr.app _ (z.targetToRight.app _ y) = e.app _ (p₄.app _ y) :=
    congrArg (fun f : Q₄ ⟶ B ↦ f.app _ y) h₃
  have hl' := hl.map pl
  have hr' := hr.map pr
  rw [e₀, e₁] at hl'
  rw [e₂, e₃] at hr'
  exact isoVertices_of_weakEquivalence e (hl'.trans hr')

end EquivalenceZigzag

end SSet
