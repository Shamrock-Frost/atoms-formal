import Atoms.ForMathlib.CategoryTheory.Yoneda
import Atoms.Homotopical.Localizer.InverseImage
import Atoms.Homotopical.Regular.Completion

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {B B' : Type v} [SmallCategory B] [SmallCategory B']

noncomputable def elementsEquivalence (e : B ≌ B') (X : Bᵒᵖ ⥤ Type v) :
    CostructuredArrow yoneda X ≌
      CostructuredArrow yoneda (e.op.congrLeft.functor.obj X) :=
  (CostructuredArrow.post yoneda e.op.congrLeft.functor X).asEquivalence.trans
    ((CostructuredArrow.mapNatIso e.congrLeftOpYonedaIso).trans
      (CostructuredArrow.pre e.functor yoneda _).asEquivalence)

def elementsEquivalenceRepresentablesIso (e : B ≌ B') (X : Bᵒᵖ ⥤ Type v) :
    (elementsEquivalence e X).functor ⋙
        representablesOver (e.op.congrLeft.functor.obj X) ≅
      representablesOver X ⋙ e.op.congrLeft.functor :=
  Functor.isoWhiskerLeft (CostructuredArrow.proj yoneda X) e.congrLeftOpYonedaIso.symm

variable {A A' : Type v} [SmallCategory A] [SmallCategory A']

theorem rlp_monomorphisms_map_of_equivalence (E : (Aᵒᵖ ⥤ Type v) ≌ (A'ᵒᵖ ⥤ Type v))
    {X Y : Aᵒᵖ ⥤ Type v} {p : X ⟶ Y} (hp : (monomorphisms (Aᵒᵖ ⥤ Type v)).rlp p) :
    (monomorphisms (A'ᵒᵖ ⥤ Type v)).rlp (E.functor.map p) := by
  intro _ _ m hm
  have : Mono m := hm
  exact (E.symm.toAdjunction.hasLiftingProperty_iff m p).1
    (hp _ (monomorphisms.infer_property (E.inverse.map m)))

theorem IsALocalizer.inverseImage_of_equivalence (E : (Aᵒᵖ ⥤ Type v) ≌ (A'ᵒᵖ ⥤ Type v))
    {V : MorphismProperty (A'ᵒᵖ ⥤ Type v)} [hV : IsALocalizer V] :
    IsALocalizer (V.inverseImage E.functor) :=
  hV.inverseImage E.functor (fun f (_ : Mono f) ↦ inferInstance)
    fun _ hf ↦ rlp_monomorphisms_map_of_equivalence E hf

theorem isALocalizer_inverseImage_iff (e : B ≌ B') (V : MorphismProperty (B'ᵒᵖ ⥤ Type v))
    [V.RespectsIso] :
    IsALocalizer (V.inverseImage e.op.congrLeft.functor) ↔ IsALocalizer V := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.inverseImage_of_equivalence _⟩
  rw [← inverseImage_inverseImage_congrLeft_op e V]
  exact h.inverseImage_of_equivalence e.symm.op.congrLeft

theorem isAccessibleALocalizer_inverseImage_iff (e : B ≌ B')
    (V : MorphismProperty (B'ᵒᵖ ⥤ Type v)) [V.RespectsIso] :
    IsAccessibleALocalizer (V.inverseImage e.op.congrLeft.functor) ↔
      IsAccessibleALocalizer V := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← inverseImage_inverseImage_congrLeft_op e V]
    have := h.isALocalizer.inverseImage_of_equivalence e.symm.op.congrLeft
    exact h.inverseImage _ (fun f _ ↦ inferInstance)
  · have := (isALocalizer_inverseImage_iff e V).2 h.isALocalizer
    exact h.inverseImage _ (fun f _ ↦ inferInstance)

theorem projectiveCofibrations_initial_to_presheafEquivalence (e : B ≌ B')
    (X : Bᵒᵖ ⥤ Type v) {J : Type v} [SmallCategory J] (K : J ⥤ CostructuredArrow yoneda X)
    [K.IsRightAdjoint] :
    projectiveCofibrations B' J (initial.to (K ⋙
      (projectiveReplacement B (CostructuredArrow yoneda X)).obj (representablesOver X) ⋙
        e.op.congrLeft.functor)) := by
  refine projectiveCofibrations_initial_to_comp _ ?_
  refine projectiveCofibrations_whiskerLeft_of_isRightAdjoint _ ?_
  exact projectiveCofibrations_initial_to_whiskerRight e.op.congrLeft.toAdjunction
    (fun f _ ↦ inferInstance)
    (projectiveCofibrations_initial_to_projectiveReplacement (A := B) (representablesOver X))

theorem isRegular_inverseImage_iff (e : B ≌ B') {V : MorphismProperty (B'ᵒᵖ ⥤ Type v)}
    [hV : IsALocalizer V] {X : Bᵒᵖ ⥤ Type v} {Y : B'ᵒᵖ ⥤ Type v}
    (φ : e.op.congrLeft.functor.obj X ≅ Y) :
    IsRegular (V.inverseImage e.op.congrLeft.functor) X ↔ IsRegular V Y := by
  have hW₀ := isAccessibleALocalizer_generatedALocalizer (⊥ : MorphismProperty (B'ᵒᵖ ⥤ Type v))
  have hW₀V : generatedALocalizer ⊥ ≤ V := generatedALocalizer_le bot_le
  let E := (elementsEquivalence e X).trans (CostructuredArrow.mapIso (S := yoneda) φ)
  let Q := (projectiveReplacement B (CostructuredArrow yoneda X)).obj (representablesOver X)
  let πX : Q ⟶ representablesOver X :=
    (projectiveReplacementπ B (CostructuredArrow yoneda X)).app (representablesOver X)
  let πY : _ ⟶ representablesOver Y :=
    (projectiveReplacementπ B' (CostructuredArrow yoneda Y)).app (representablesOver Y)
  let ρ : E.inverse ⋙ Q ⋙ e.op.congrLeft.functor ⟶ representablesOver Y :=
    Functor.whiskerLeft E.inverse (Functor.whiskerRight πX e.op.congrLeft.functor) ≫
      Functor.whiskerLeft E.inverse (elementsEquivalenceRepresentablesIso e X).inv ≫
        Functor.whiskerRight E.counit (representablesOver Y)
  have hρ : ∀ c, (monomorphisms (B'ᵒᵖ ⥤ Type v)).rlp (ρ.app c) := fun c ↦ by
    change (monomorphisms _).rlp (e.op.congrLeft.functor.map (πX.app (E.inverse.obj c)) ≫
      (elementsEquivalenceRepresentablesIso e X).inv.app (E.inverse.obj c) ≫
        (yoneda.mapIso ((CostructuredArrow.proj yoneda Y).mapIso (E.counitIso.app c))).hom)
    exact (monomorphisms _).rlp.comp_mem _ _
      (rlp_monomorphisms_map_of_equivalence e.op.congrLeft
        (rlp_monomorphisms_projectiveReplacementπ_app (representablesOver X) (E.inverse.obj c)))
      ((monomorphisms _).rlp.comp_mem _ _ (MorphismProperty.rlp_of_isIso _
        ((elementsEquivalenceRepresentablesIso e X).app (E.inverse.obj c)).inv)
        (MorphismProperty.rlp_of_isIso _
          (yoneda.mapIso ((CostructuredArrow.proj yoneda Y).mapIso (E.counitIso.app c))).hom))
  have hP := projectiveCofibrations_initial_to_presheafEquivalence e X E.inverse
  obtain ⟨ℓ, -, hℓ⟩ := exists_lift_of_projectiveCofibrations hP
    (rlp_monomorphisms_projectiveReplacementπ_app (representablesOver Y)) (initial.to _) ρ
    (initial.hom_ext _ _)
  have hℓc : ∀ c, ℓ.app c ≫ πY.app c = ρ.app c := fun c ↦ congr_app hℓ c
  have hℓ₀ : ∀ c, generatedALocalizer ⊥ (ℓ.app c) := fun c ↦ MorphismProperty.of_postcomp _ _ _
    (hW₀.isALocalizer.rlp_monomorphisms_le _ (rlp_monomorphisms_projectiveReplacementπ_app _ c))
    (by rw [hℓc]; exact hW₀.isALocalizer.rlp_monomorphisms_le _ (hρ c))
  have hcol : V (colimMap ℓ) := hW₀V _ (hW₀.colimMap_mem hP
    (projectiveCofibrations_initial_to_projectiveReplacement _) ℓ hℓ₀)
  have key : colimit.pre (Q ⋙ e.op.congrLeft.functor) E.inverse ≫
      (preservesColimitIso e.op.congrLeft.functor Q).inv ≫
        e.op.congrLeft.functor.map (regularizationMap X) ≫ φ.hom =
      colimMap ℓ ≫ regularizationMap Y := by
    refine colimit.hom_ext fun c ↦ ?_
    rw [colimit.ι_pre_assoc, ι_preservesColimitIso_inv_assoc, ← Functor.map_comp_assoc,
      ι_regularizationMap, ι_colimMap_assoc, ι_regularizationMap]
    have hw : yoneda.map (E.counit.app c).left ≫ c.hom =
        ((elementsEquivalence e X).functor.obj (E.inverse.obj c)).hom ≫ φ.hom :=
      CostructuredArrow.w (E.counit.app c)
    have hr : (elementsEquivalenceRepresentablesIso e X).inv.app (E.inverse.obj c) ≫
        ((elementsEquivalence e X).functor.obj (E.inverse.obj c)).hom =
          e.op.congrLeft.functor.map (E.inverse.obj c).hom :=
      Iso.inv_hom_id_app_assoc (elementsEquivalenceRepresentablesIso e X) (E.inverse.obj c) _
    calc e.op.congrLeft.functor.map (πX.app (E.inverse.obj c) ≫ (E.inverse.obj c).hom)
          ≫ φ.hom
        = e.op.congrLeft.functor.map (πX.app (E.inverse.obj c)) ≫
            ((elementsEquivalenceRepresentablesIso e X).inv.app (E.inverse.obj c) ≫
              ((elementsEquivalence e X).functor.obj (E.inverse.obj c)).hom) ≫ φ.hom := by
          rw [hr]
          exact Functor.map_comp_assoc _ _ _ _
      _ = (e.op.congrLeft.functor.map (πX.app (E.inverse.obj c)) ≫
            (elementsEquivalenceRepresentablesIso e X).inv.app (E.inverse.obj c) ≫
              yoneda.map (E.counit.app c).left) ≫ c.hom := by
          refine (congrArg (e.op.congrLeft.functor.map (πX.app (E.inverse.obj c)) ≫ ·)
            ((Category.assoc _ _ _).trans (congrArg
              ((elementsEquivalenceRepresentablesIso e X).inv.app (E.inverse.obj c) ≫ ·)
                hw.symm))).trans ?_
          exact ((Category.assoc _ _ _).trans (congrArg
            (e.op.congrLeft.functor.map (πX.app (E.inverse.obj c)) ≫ ·)
              (Category.assoc _ _ _))).symm
      _ = ρ.app c ≫ c.hom := rfl
      _ = ℓ.app c ≫ πY.app c ≫ c.hom := ((reassoc_of% (hℓc c)) c.hom).symm
  have hpre : V (colimit.pre (Q ⋙ e.op.congrLeft.functor) E.inverse) :=
    hV.isomorphisms_le _ (isomorphisms.infer_property _)
  have hpc : V (preservesColimitIso e.op.congrLeft.functor Q).inv :=
    hV.isomorphisms_le _ (isomorphisms.infer_property _)
  have hφ : V φ.hom := hV.isomorphisms_le _ (isomorphisms.infer_property _)
  change V (e.op.congrLeft.functor.map (regularizationMap X)) ↔ V (regularizationMap Y)
  constructor
  · intro h
    refine MorphismProperty.of_precomp _ _ _ hcol ?_
    rw [← key]
    exact V.comp_mem _ _ hpre (V.comp_mem _ _ hpc (V.comp_mem _ _ h hφ))
  · intro h
    have hd := MorphismProperty.comp_mem _ _ _ hcol h
    rw [← key] at hd
    exact V.of_postcomp _ _ hφ (V.of_precomp _ _ hpc (V.of_precomp _ _ hpre hd))

theorem isRegularALocalizer_inverseImage_iff (e : B ≌ B')
    {V : MorphismProperty (B'ᵒᵖ ⥤ Type v)} [IsALocalizer V] :
    IsRegularALocalizer (V.inverseImage e.op.congrLeft.functor) ↔
      IsRegularALocalizer V :=
  ⟨fun h ↦ ⟨fun Y ↦
      (isRegular_inverseImage_iff e (e.op.congrLeft.counitIso.app Y)).1 (h.isRegular _)⟩,
    fun h ↦ ⟨fun _ ↦ (isRegular_inverseImage_iff e (Iso.refl _)).2 (h.isRegular _)⟩⟩

theorem regularCompletion_inverseImage (e : B ≌ B') (V : MorphismProperty (B'ᵒᵖ ⥤ Type v))
    [V.RespectsIso] :
    regularCompletion (V.inverseImage e.op.congrLeft.functor) =
      (regularCompletion V).inverseImage e.op.congrLeft.functor := by
  have := (isALocalizer_inverseImage_iff e (regularCompletion V)).2 inferInstance
  have : IsRegularALocalizer ((regularCompletion V).inverseImage e.op.congrLeft.functor) :=
    (isRegularALocalizer_inverseImage_iff e).2 inferInstance
  let R := regularCompletion (V.inverseImage e.op.congrLeft.functor)
  refine le_antisymm (regularCompletion_le fun _ _ f hf ↦ le_regularCompletion V _ hf)
    fun X Y f hf ↦ ?_
  have hle : regularCompletion V ≤ R.inverseImage e.symm.op.congrLeft.functor := by
    have := (isALocalizer_inverseImage_iff e.symm R).2 inferInstance
    have : IsRegularALocalizer (R.inverseImage e.symm.op.congrLeft.functor) :=
      (isRegularALocalizer_inverseImage_iff e.symm).2 inferInstance
    refine regularCompletion_le fun _ _ g hg ↦ ?_
    refine le_regularCompletion _ _ ?_
    rw [← inverseImage_inverseImage_congrLeft_op e V] at hg
    exact hg
  exact (map_functor_map_inverse_iff e.op.congrLeft.symm R f).1 (hle _ hf)

theorem IsTestALocalizer.inverseImage_presheafEquivalence (e : B ≌ B')
    {V : MorphismProperty (B'ᵒᵖ ⥤ Type v)} [hV : IsTestALocalizer V] :
    IsTestALocalizer (V.inverseImage e.op.congrLeft.functor) := by
  have := (isALocalizer_inverseImage_iff e V).2 inferInstance
  have : IsRegularALocalizer (V.inverseImage e.op.congrLeft.functor) :=
    (isRegularALocalizer_inverseImage_iff e).2 inferInstance
  refine ⟨fun b ↦ ?_⟩
  have hT : IsTerminal (e.op.congrLeft.functor.obj (⊤_ (Bᵒᵖ ⥤ Type v))) :=
    terminalIsTerminal.isTerminalObj _
  exact (V.arrow_mk_iso_iff (Arrow.isoMk (e.congrLeftOpYonedaIso.app b).symm
    (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _))).1
      (hV.terminal_from_yoneda (e.functor.obj b))

theorem isTestALocalizer_inverseImage_iff (e : B ≌ B') (V : MorphismProperty (B'ᵒᵖ ⥤ Type v))
    [V.RespectsIso] :
    IsTestALocalizer (V.inverseImage e.op.congrLeft.functor) ↔ IsTestALocalizer V := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.inverseImage_presheafEquivalence e⟩
  rw [← inverseImage_inverseImage_congrLeft_op e V]
  exact h.inverseImage_presheafEquivalence e.symm

theorem isRegularALocalizer_of_equivalence (e : B ≌ B')
    (h : ∀ W : MorphismProperty (Bᵒᵖ ⥤ Type v), IsALocalizer W → IsRegularALocalizer W)
    {V : MorphismProperty (B'ᵒᵖ ⥤ Type v)} [hV : IsALocalizer V] : IsRegularALocalizer V := by
  exact (isRegularALocalizer_inverseImage_iff e).1
    (h _ ((isALocalizer_inverseImage_iff e V).2 hV))

end Atoms.Homotopical
