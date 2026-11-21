import Atoms.Homotopical.HomotopyColimit.ColimitInvariance
import Atoms.Homotopical.PresheafSlice

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A B : Type v} [SmallCategory A] [SmallCategory B]

theorem IsALocalizer.isAccessibleALocalizer_of_eq_saturation
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsALocalizer V]
    {J : MorphismProperty (Aᵒᵖ ⥤ Type v)} [J.IsSmall.{v}]
    (hJ : MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V = saturation.{v} J) :
    IsAccessibleALocalizer V := by
  have hJV : J ≤ MorphismProperty.monomorphisms _ ⊓ V := hJ ▸ le_saturation J
  have hG := isALocalizer_generatedALocalizer J
  refine ⟨J, inferInstance, le_antisymm
    (generatedALocalizer_le fun _ _ f hf ↦ (hJV f hf).2) fun X Y f hf ↦ ?_⟩
  let d := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp f
  have hfac : V (d.i ≫ d.p) := by rw [d.fac]; exact hf
  have hi : (MorphismProperty.monomorphisms _ ⊓ V) d.i :=
    ⟨d.hi, V.of_postcomp d.i d.p (hV.rlp_monomorphisms_le _ d.hp) hfac⟩
  rw [hJ] at hi
  have hi' := saturation_le J (MorphismProperty.monomorphisms _ ⊓ generatedALocalizer J)
    (fun _ _ g hg ↦ ⟨(hJV g hg).1, le_generatedALocalizer J g hg⟩) d.i hi
  rw [← d.fac]
  exact (generatedALocalizer J).comp_mem _ _ hi'.2 (hG.rlp_monomorphisms_le _ d.hp)

theorem range_map_range_ι (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v) {K L : Aᵒᵖ ⥤ Type v}
    (i : K ⟶ L) [Mono i] :
    Subfunctor.range (F.map (Subfunctor.range i).ι) = Subfunctor.range (F.map i) := by
  have e : F.map i = F.map (Subfunctor.toRange i) ≫ F.map (Subfunctor.range i).ι := by
    rw [← F.map_comp, Subfunctor.toRange_ι]
  rw [e, Subfunctor.range_comp, Subfunctor.range_eq_top (p := F.map (Subfunctor.toRange i)),
    Subfunctor.image_top]

theorem map_homOfLe_mem_iff (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    (W : MorphismProperty (Bᵒᵖ ⥤ Type v)) [W.RespectsIso] {X : Aᵒᵖ ⥤ Type v}
    {T U : Subfunctor X} (h : T ≤ U) [Mono (F.map T.ι)] [Mono (F.map U.ι)] :
    W (F.map (Subfunctor.homOfLe h)) ↔
      W (Subfunctor.homOfLe (Subfunctor.range_map_ι_le_of_le F h)) := by
  refine MorphismProperty.arrow_mk_iso_iff W (Arrow.isoMk
    (asIso (Subfunctor.toRange (F.map T.ι))) (asIso (Subfunctor.toRange (F.map U.ι))) ?_)
  rw [← cancel_mono (Subfunctor.range (F.map U.ι)).ι]
  simp only [Arrow.mk_hom, asIso_hom, Category.assoc, Subfunctor.homOfLe_ι,
    Subfunctor.toRange_ι, ← F.map_comp]

theorem IsALocalizer.homOfLe_inf_iSup_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsALocalizer V] {J : Type v} [LinearOrder J] [WellFoundedLT J] {X : Aᵒᵖ ⥤ Type v}
    (P : Subfunctor X) {R : J → Subfunctor X} (hR : Monotone R)
    (h : ∀ j, V (Subfunctor.homOfLe (inf_le_right : P ⊓ R j ≤ R j))) :
    V (Subfunctor.homOfLe (inf_le_right : P ⊓ ⨆ j, R j ≤ ⨆ j, R j)) := by
  have hPR : Monotone fun j ↦ P ⊓ R j := fun a b hab ↦ inf_le_inf_left P (hR hab)
  have heq : P ⊓ ⨆ j, R j = ⨆ j, P ⊓ R j := by
    ext U x
    simp only [Subfunctor.min_obj, Subfunctor.iSup_obj, Set.mem_inter_iff, Set.mem_iUnion]
    exact ⟨fun ⟨hP, j, hj⟩ ↦ ⟨j, hP, hj⟩, fun ⟨j, hP, hj⟩ ↦ ⟨hP, j, hj⟩⟩
  have hlubX : IsLUB (Set.range hPR.functor.obj) (P ⊓ ⨆ j, R j) := by
    rw [heq]
    exact isLUB_iSup
  have hlubY : IsLUB (Set.range hR.functor.obj) (⨆ j, R j) := isLUB_iSup
  let φ : hPR.functor ⋙ Subfunctor.toFunctorFunctor X ⟶
      hR.functor ⋙ Subfunctor.toFunctorFunctor X :=
    { app j := Subfunctor.homOfLe (inf_le_right : P ⊓ R j ≤ R j) }
  exact hV.of_isColimit (fun _ _ hab ↦ inferInstanceAs (Mono (Subfunctor.homOfLe (hPR hab))))
    (fun _ _ hab ↦ inferInstanceAs (Mono (Subfunctor.homOfLe (hR hab)))) φ h
    (isColimitOfPreserves (Subfunctor.toFunctorFunctor X)
      (Preorder.colimitCoconeOfIsLUB hPR.functor hlubX).isColimit)
    (isColimitOfPreserves (Subfunctor.toFunctorFunctor X)
      (Preorder.colimitCoconeOfIsLUB hR.functor hlubY).isColimit)
    (Subfunctor.homOfLe (inf_le_right : P ⊓ ⨆ j, R j ≤ ⨆ j, R j)) fun _ ↦ rfl

theorem range_map_ι_iSup_eq (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    [PreservesColimitsOfSize.{v, v} F] {X : Aᵒᵖ ⥤ Type v} {J : Type v} [LinearOrder J]
    [Nonempty J] {S : J → Subfunctor X} (hS : Monotone S) :
    Subfunctor.range (F.map (⨆ j, S j).ι) = ⨆ j, Subfunctor.range (F.map (S j).ι) := by
  refine le_antisymm ?_ (iSup_le fun j ↦ Subfunctor.range_map_ι_le_of_le F (le_iSup S j))
  rintro b z ⟨y, rfl⟩
  obtain ⟨j, y', hy'⟩ := Subfunctor.exists_map_homOfLe_app_eq F hS.functor
    (T := ⨆ j, S j) isLUB_iSup y
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨j, y', ?_⟩
  rw [← hy', ← NatTrans.comp_app_apply, ← F.map_comp, Subfunctor.homOfLe_ι]
  rfl

theorem exists_bounded_enlargement_inverseImage (W : MorphismProperty (Bᵒᵖ ⥤ Type v))
    [hW : IsAccessibleALocalizer W] (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    [PreservesColimitsOfSize.{v, v} F]
    (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f)) :
    ∃ β₀ : Cardinal.{v}, Cardinal.aleph0 ≤ β₀ ∧ ∀ α : Cardinal.{v}, β₀ ≤ α →
      ∀ {K L : Aᵒᵖ ⥤ Type v} (i : K ⟶ L),
        (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ W.inverseImage F) i →
        ∀ J : Subfunctor L, IsBounded (2 ^ α) J.toFunctor →
          ∃ J' : Subfunctor L, J ≤ J' ∧ IsBounded (2 ^ α) J'.toFunctor ∧
            (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ W.inverseImage F)
              (Subfunctor.homOfLe (inf_le_right : Subfunctor.range i ⊓ J' ≤ J')) := by
  obtain ⟨𝕀, S, hSsmall, hS, hWeq⟩ := (IsAccessibleALocalizer.iff_exists_cylinder W).1 hW
  obtain ⟨α₀, hα₀, henl⟩ := 𝕀.exists_bounded_enlargement S hS
  rw [ExactCylinder.trivialCofibrations, hWeq] at henl
  obtain ⟨c, hc, hFb⟩ := exists_isBounded_obj_of_preservesColimits F
  obtain ⟨β₀, hle, hβ₀, hβ₀α⟩ := exists_two_pow_bound A (max α₀ (max c (Cardinal.mk B)))
  refine ⟨β₀, hβ₀, fun α hα K L i hi J hJ ↦ ?_⟩
  have hαβ : α ≤ 2 ^ α := (Cardinal.cantor α).le
  have hrest : max c (Cardinal.mk B) ≤ 2 ^ α :=
    (((le_max_right _ _).trans hle).trans hα).trans hαβ
  have hα₀α : α₀ ≤ α := (le_max_left _ _).trans (hle.trans hα)
  obtain ⟨hβ, -, hA⟩ := hβ₀α α hα
  have hcβ : c ≤ 2 ^ α := (le_max_left _ _).trans hrest
  have hBo : Cardinal.mk B ≤ 2 ^ α := (le_max_right _ _).trans hrest
  have hmi : Mono i := hi.1
  have hFi : (MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v) ⊓ W) (F.map i) :=
    ⟨hF i hmi, hi.2⟩
  have hstep : ∀ T : Subfunctor L, IsBounded (2 ^ α) T.toFunctor →
      ∃ T' : Subfunctor L, ∃ R : Subfunctor (F.obj L), T ≤ T' ∧
        IsBounded (2 ^ α) T'.toFunctor ∧ Subfunctor.range (F.map T.ι) ≤ R ∧
          R ≤ Subfunctor.range (F.map T'.ι) ∧
            W (Subfunctor.homOfLe (inf_le_right : Subfunctor.range (F.map i) ⊓ R ≤ R)) := by
    intro T hT
    obtain ⟨R, hRle, hRb, hRW⟩ := henl α hα₀α (F.map i) hFi (Subfunctor.range (F.map T.ι))
      (isBounded_range _ (hFb _ hcβ _ hT))
    obtain ⟨T'', hT''b, hT''⟩ := exists_isBounded_le_range_map_ι F hβ hA hBo R hRb
    exact ⟨T ⊔ T'', R, le_sup_left, isBounded_sup hβ hT hT''b, hRle,
      hT''.trans (Subfunctor.range_map_ι_le_of_le F le_sup_right), hRW.2⟩
  choose! next Rof hle hb hlo hhi hWR using hstep
  have hJs : ∀ n : ℕ, IsBounded (2 ^ α) (next^[n] J).toFunctor := by
    intro n
    induction n with
    | zero => exact hJ
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hb _ ih
  have hmono : Monotone fun n : ℕ ↦ next^[n] J := monotone_nat_of_le_succ fun n => by
    rw [Function.iterate_succ_apply']
    exact hle _ (hJs n)
  have hmono' : Monotone fun n : ULift.{v} ℕ ↦ next^[n.down] J := fun a b hab ↦ hmono hab
  let Rs : ULift.{v} ℕ → Subfunctor (F.obj L) := fun n ↦ Rof (next^[n.down] J)
  have hnext : ∀ n : ℕ, next (next^[n] J) ≤ ⨆ m : ULift.{v} ℕ, next^[m.down] J := fun n ↦ by
    have := le_iSup (fun m : ULift.{v} ℕ ↦ next^[m.down] J) ⟨n + 1⟩
    rwa [Function.iterate_succ_apply'] at this
  have hRs : Monotone Rs := by
    intro a b hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have h' : a.down + 1 ≤ b.down := h
      refine (hhi _ (hJs _)).trans ((Subfunctor.range_map_ι_le_of_le F ?_).trans
        (hlo _ (hJs _)))
      rw [← Function.iterate_succ_apply' next]
      exact hmono h'
  let J' := ⨆ n : ULift.{v} ℕ, next^[n.down] J
  have hrange : Subfunctor.range (F.map J'.ι) = ⨆ n, Rs n :=
    le_antisymm ((range_map_ι_iSup_eq F hmono').le.trans (iSup_mono fun n ↦ hlo _ (hJs _)))
      (iSup_le fun n ↦ (hhi _ (hJs _)).trans (Subfunctor.range_map_ι_le_of_le F (hnext n.down)))
  have hlim := hW.isALocalizer.homOfLe_inf_iSup_mem (Subfunctor.range (F.map i)) hRs
    fun n ↦ hWR _ (hJs _)
  have hN : Cardinal.mk (ULift.{v} ℕ) ≤ 2 ^ α := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hβ
  refine ⟨J', le_iSup_of_le (ULift.up 0) le_rfl, isBounded_iSup hβ hN _ fun n ↦ hJs _,
    inferInstance, ?_⟩
  have : Mono (F.map (Subfunctor.range i ⊓ J').ι) := hF _ inferInstance
  have : Mono (F.map J'.ι) := hF _ inferInstance
  change W (F.map _)
  rw [map_homOfLe_mem_iff F W]
  refine (Subfunctor.homOfLe_mem_iff_of_eq W _ inf_le_right ?_ hrange).2 hlim
  rw [range_map_ι_inf_of_preservesColimits F hF, range_map_range_ι F i, hrange]

theorem IsALocalizer.inverseImage {W : MorphismProperty (Bᵒᵖ ⥤ Type v)} [hW : IsALocalizer W]
    (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v) [PreservesColimitsOfSize.{v, v} F]
    (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f))
    (htf : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), (monomorphisms (Aᵒᵖ ⥤ Type v)).rlp f →
      (monomorphisms (Bᵒᵖ ⥤ Type v)).rlp (F.map f)) :
    IsALocalizer (W.inverseImage F) where
  hasTwoOutOfThreeProperty := inferInstance
  rlp_monomorphisms_le _ _ f hf := hW.rlp_monomorphisms_le _ (htf f hf)
  isStableUnderCobaseChange := ⟨fun sq hf ↦ ⟨(monomorphisms _).of_isPushout sq hf.1,
    ((monomorphisms (Bᵒᵖ ⥤ Type v) ⊓ W).of_isPushout (F.map_isPushout sq) ⟨hF _ hf.1, hf.2⟩).2⟩⟩
  isStableUnderTransfiniteComposition := ⟨fun J _ _ _ _ ↦ ⟨fun _ _ f hf ↦ by
    have : PreservesWellOrderContinuousOfShape J F := ⟨fun _ _ ↦ inferInstance⟩
    refine ⟨(monomorphisms _).transfiniteCompositionsOfShape_le J _
      (transfiniteCompositionsOfShape_monotone J inf_le_left f hf), ?_⟩
    exact ((monomorphisms (Bᵒᵖ ⥤ Type v) ⊓ W).transfiniteCompositionsOfShape_le J _
      (transfiniteCompositionsOfShape_map_of_preserves J F f
        (transfiniteCompositionsOfShape_monotone J (fun _ _ g hg ↦ ⟨hF g hg.1, hg.2⟩) f
          hf))).2⟩⟩

theorem IsALocalizer.inverseImage_of_adjunction {W : MorphismProperty (Bᵒᵖ ⥤ Type v)}
    [IsALocalizer W] {F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v} {L : (Bᵒᵖ ⥤ Type v) ⥤ Aᵒᵖ ⥤ Type v}
    (adj : L ⊣ F) [PreservesColimitsOfSize.{v, v} F] [L.PreservesMonomorphisms] :
    IsALocalizer (W.inverseImage F) := by
  have : F.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  refine IsALocalizer.inverseImage F (fun f hf ↦ ?_) fun f hf _ _ m hm ↦ ?_
  · have : Mono f := hf
    exact F.map_mono f
  · have : Mono m := hm
    exact (adj.hasLiftingProperty_iff m f).1 (hf _ (L.map_mono m))

theorem IsAccessibleALocalizer.inverseImage {W : MorphismProperty (Bᵒᵖ ⥤ Type v)}
    [IsAccessibleALocalizer W] (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v)
    [PreservesColimitsOfSize.{v, v} F]
    (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f))
    [hV : IsALocalizer (W.inverseImage F)] : IsAccessibleALocalizer (W.inverseImage F) := by
  let Q := MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ W.inverseImage F
  obtain ⟨β₀, hβ₀, henl⟩ := exists_bounded_enlargement_inverseImage W F hF
  obtain ⟨α, hβ₀α, -, hα⟩ := exists_two_pow_bound A β₀
  obtain ⟨-, -, hA⟩ := hα α le_rfl
  obtain ⟨ι, R, -, hrep⟩ := exists_boundedRepresentatives (A := A) (2 ^ α)
  have hQ := eq_saturation_boundedGenerators Q (fun _ _ _ hf ↦ hf.1)
    (fun f g _ hg hf hfg ↦ ⟨hg, (W.inverseImage F).of_precomp f g hf.2 hfg.2⟩)
    (IsBounded (2 ^ α)) R hrep (iSup_boundedSubfunctor_eq_top hA)
    (fun i hi Z hZ ↦ henl α hβ₀α i hi Z hZ)
  exact hV.isAccessibleALocalizer_of_eq_saturation hQ

instance IsALocalizer.inverseImage_sliceForget {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsALocalizer V] (X : Aᵒᵖ ⥤ Type v) :
    IsALocalizer (V.inverseImage (sliceForget X)) :=
  hV.inverseImage (sliceForget X) (fun g hg ↦ ((sliceForget X).mono_map_iff_mono g).2 hg)
    fun f hf ↦ by
    rwa [monomorphisms_eq_inverseImage_sliceForget,
      rlp_inverseImage_sliceForget_of_respectsIso] at hf

instance IsAccessibleALocalizer.inverseImage_sliceForget {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] (X : Aᵒᵖ ⥤ Type v) :
    IsAccessibleALocalizer (V.inverseImage (sliceForget X)) :=
  hV.inverseImage (sliceForget X) (fun g hg ↦ ((sliceForget X).mono_map_iff_mono g).2 hg)

theorem IsAccessibleALocalizer.generatedALocalizer_map {B : Type v} [SmallCategory B]
    (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsAccessibleALocalizer W]
    (F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v) [PreservesColimitsOfSize.{v, v} F]
    (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f)) :
    IsAccessibleALocalizer (generatedALocalizer (W.map F)) := by
  obtain ⟨T, hT, hTW⟩ :=
    (inferInstance : IsAccessibleALocalizer W).exists_trivialCofibrations_eq_saturation
  have hTle : T ≤ MorphismProperty.monomorphisms _ ⊓ W := hTW ▸ le_saturation T
  refine IsAccessibleALocalizer.of_eq (S := functorImage F T) inferInstance (le_antisymm ?_ ?_)
  · refine generatedALocalizer_mono ?_
    rintro _ _ g ⟨K, L, t, ht, e⟩
    exact ⟨K, L, t, (hTle t ht).2, ⟨eqToIso e⟩⟩
  · refine generatedALocalizer_le ?_
    have hsat : saturation.{v} T ≤
        (MorphismProperty.monomorphisms _ ⊓ generatedALocalizer (functorImage F T)).inverseImage
          F := by
      refine saturation_le _ _ fun K L t ht ↦ ⟨hF t (hTle t ht).1, ?_⟩
      exact le_generatedALocalizer _ _ ⟨K, L, t, ht, rfl⟩
    have hmono : MorphismProperty.monomorphisms _ ⊓ W ≤
        (generatedALocalizer (functorImage F T)).inverseImage F :=
      fun _ _ t ht ↦ (hsat t (hTW ▸ ht)).2
    rw [MorphismProperty.map_le_iff]
    intro X Y w hw
    let d := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp w
    have hp : W d.p := IsALocalizer.rlp_monomorphisms_le _ d.hp
    have hi : W d.i := W.of_postcomp _ _ hp (by rw [d.fac]; exact hw)
    have := d.hp _ (MorphismProperty.monomorphisms.infer_property (initial.to Y))
    let sq : CommSq (initial.to d.Z) (initial.to Y) d.p (𝟙 Y) := ⟨initial.hom_ext _ _⟩
    have hs : W sq.lift := W.of_postcomp _ d.p hp (by rw [sq.fac_right]; exact W.id_mem _)
    have hFp : generatedALocalizer (functorImage F T) (F.map d.p) := by
      refine MorphismProperty.of_precomp _ (F.map sq.lift) _
        (hmono _ ⟨mono_of_mono_fac sq.fac_right, hs⟩) ?_
      rw [← F.map_comp, sq.fac_right, F.map_id]
      exact MorphismProperty.id_mem _ _
    rw [MorphismProperty.inverseImage_iff, ← d.fac, F.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (hmono _ ⟨d.hi, hi⟩) hFp

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v

variable {A B : Type v} [SmallCategory A] [SmallCategory B]

theorem weakEquivalences_le_inverseImage_of_map_contraction
    (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (𝕁 : ExactCylinder.{v} (Bᵒᵖ ⥤ Type v)) (T : MorphismProperty (Bᵒᵖ ⥤ Type v))
    [T.IsSmall.{v}] (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    {F : (Aᵒᵖ ⥤ Type v) ⥤ Bᵒᵖ ⥤ Type v} {L : (Bᵒᵖ ⥤ Type v) ⥤ Aᵒᵖ ⥤ Type v} (adj : L ⊣ F)
    [PreservesColimitsOfSize.{v, v} F] [L.PreservesMonomorphisms]
    (hSF : S ≤ (𝕁.weakEquivalences T).inverseImage F)
    (hσ : ∀ X : Aᵒᵖ ⥤ Type v, 𝕁.weakEquivalences T (F.map (𝕀.contraction.app X))) :
    𝕀.weakEquivalences S ≤ (𝕁.weakEquivalences T).inverseImage F := by
  have := 𝕁.isALocalizer_weakEquivalences T hT
  have := IsALocalizer.inverseImage_of_adjunction (W := 𝕁.weakEquivalences T) adj
  exact 𝕀.weakEquivalences_le_of_endpoint_mem S hS hSF fun ε X ↦
    (IsALocalizer.endpoint_mem_iff_contraction_mem 𝕀 ε X).2 (hσ X)

end HomotopicalAlgebra.ExactCylinder
