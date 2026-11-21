import Atoms.Homotopical.Regular.Completion
import Atoms.Homotopical.EilenbergZilber.Elements

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical.IsMonoSaturatedClass

open EZCategory

universe u

variable {A : Type u} [SmallCategory A] {P : (Aᵒᵖ ⥤ Type u) → Prop}

variable [EZCategory A]

theorem of_cellChain [HasTrivialAutomorphisms A]
    (hP : IsMonoSaturatedClass P) (hrep : ∀ a : A, P (yoneda.obj a)) {X : Aᵒᵖ ⥤ Type u}
    (hX : ∀ (b : A) (x : X.obj (op b)), IsNondegenerate X x → P (boundary b).toFunctor)
    (R : Subfunctor X) (hR : P R.toFunctor) (j : WithTop (CellClass R)) :
    P (cellChain R j).toFunctor := by
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    by_cases hj : Order.IsSuccPrelimit j
    · by_cases hmin : IsMin j
      · rw [hmin.eq_bot, (EZCategory.isUnionChain_cellChain R).bot]
        exact hR
      · have hsup : cellChain R j = ⨆ k : Set.Iio j, cellChain R k.1 :=
          (EZCategory.isUnionChain_cellChain R).eq_iSup_of_isSuccLimit
            (Order.IsSuccLimit.mk hmin hj)
        have hmono : Monotone fun k : Set.Iio j ↦ cellChain R k.1 :=
          fun k k' h ↦ (EZCategory.isUnionChain_cellChain R).mono h
        have h := hP.iSup_subfunctor (Set.Iio j) _ hmono fun k ↦ ih k.1 k.2
        rw [hsup]
        exact h
    · obtain ⟨k, hk, rfl⟩ := Order.not_isSuccPrelimit_iff_succ_eq.1 hj
      induction k using WithTop.recTopCoe with
      | top => exact absurd isMax_top hk
      | coe q =>
        exact hP.of_isPushout (isPushout_boundaryInclusion q).flip inferInstance
          (hP.of_iso (uliftBoundaryIsoBoundary _).symm (hX _ _ (rep q).isNondegenerate))
          (hP.of_iso (uliftYonedaIsoYoneda.{u, u}.app _).symm (hrep _))
          (ih _ (Order.lt_succ_of_not_isMax hk))

theorem of_boundary [HasTrivialAutomorphisms A]
    (hP : IsMonoSaturatedClass P) (hrep : ∀ a : A, P (yoneda.obj a)) (X : Aᵒᵖ ⥤ Type u)
    (hX : ∀ (b : A) (x : X.obj (op b)), Homotopical.EZCategory.IsNondegenerate X x →
      P (Homotopical.EZCategory.boundary b).toFunctor) : P X := by
  have h := hP.of_cellChain hrep hX ⊥ (hP.bot_subfunctor X) ⊤
  rw [cellChain_top] at h
  exact hP.of_iso (@asIso _ _ _ _ (⊤ : Subfunctor X).ι
    ((Subfunctor.eq_top_iff_isIso _).1 rfl)) h

theorem deg_lt_of_isNondegenerate_boundary {a b : A}
    (x : (boundary a).toFunctor.obj (op b)) (hx : IsNondegenerate _ x) : deg b < deg a := by
  obtain ⟨c, p, i, hp, hi, hpi⟩ := exists_factorization x.1
  have hin : ¬IsSplitEpi i := fun h ↦ x.2 (by rw [← hpi]; infer_instance)
  have : IsIso p := hx p hp ⟨⟨i, hin⟩, Subtype.ext hpi⟩
  have hm : Mono x.1 := by rw [← hpi]; infer_instance
  refine lt_of_le_of_ne (deg_le_of_mono _ hm) fun h ↦ x.2 ?_
  have := isIso_of_mono_of_deg_eq _ hm h
  infer_instance

theorem boundary_of_deg_lt [HasTrivialAutomorphisms A]
    (hP : IsMonoSaturatedClass P) (hrep : ∀ a : A, P (yoneda.obj a)) (n : ℕ) :
    ∀ a : A, deg a < n → P (boundary a).toFunctor := by
  induction n with
  | zero => exact fun a h ↦ absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro a ha
    exact hP.of_boundary hrep _ fun b x hx ↦
      ih b ((deg_lt_of_isNondegenerate_boundary x hx).trans_le (Nat.lt_succ_iff.1 ha))

theorem of_representable [HasTrivialAutomorphisms A]
    (hP : IsMonoSaturatedClass P) (hrep : ∀ a : A, P (yoneda.obj a)) (X : Aᵒᵖ ⥤ Type u) : P X :=
  hP.of_boundary hrep X fun b _ _ ↦
    hP.boundary_of_deg_lt hrep _ b (Nat.lt_succ_self _)

end Atoms.Homotopical.IsMonoSaturatedClass

namespace Atoms.Homotopical

universe u

variable {A : Type u} [SmallCategory A] [EZCategory A] [HasTrivialAutomorphisms A]
  {V : MorphismProperty (Aᵒᵖ ⥤ Type u)}

theorem IsAccessibleALocalizer.isRegularALocalizer_of_rigid [hV : IsAccessibleALocalizer V] :
    IsRegularALocalizer V :=
  ⟨hV.isMonoSaturatedClass_isRegular.of_representable IsALocalizer.isRegular_yoneda⟩

instance IsALocalizer.isRegularALocalizer_of_rigid [IsALocalizer V] : IsRegularALocalizer V :=
  have := (isAccessibleALocalizer_generatedALocalizer
    (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type u))).isRegularALocalizer_of_rigid
  IsALocalizer.isRegularALocalizer_of_generatedALocalizer_bot

theorem IsALocalizer.regularCompletion_eq_of_rigid [IsALocalizer V] :
    regularCompletion V = V :=
  le_antisymm (regularCompletion_le le_rfl) (le_regularCompletion V)

end Atoms.Homotopical
