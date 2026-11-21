import Atoms.Homotopical.IteratedSlice
import Atoms.Homotopical.Localizer.Transport

open CategoryTheory Limits Opposite Atoms Atoms.Homotopical MorphismProperty

namespace Atoms.Homotopical

universe v

noncomputable def sliceRepresentablesIso {A : Type v} [SmallCategory A]
    (X : Aᵒᵖ ⥤ Type v) (Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (costructuredArrowSliceEquivalence X Z).functor ⋙
        representablesOver ((sliceForget X).obj Z) ≅
      representablesOver Z ⋙ sliceForget X :=
  (Functor.isoWhiskerRight (costructuredArrowSliceEquivalenceProjIso X Z) yoneda) ≪≫
    (Functor.isoWhiskerLeft (CostructuredArrow.proj yoneda Z)
      (sliceForgetYonedaNatIso X)).symm

theorem sliceRepresentablesIso_inv_comp_hom {A : Type v} [SmallCategory A]
    (X : Aᵒᵖ ⥤ Type v) (Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda Z) :
    (sliceRepresentablesIso X Z).inv.app s ≫
      ((costructuredArrowSliceEquivalence X Z).functor.obj s).hom =
        (sliceForget X).map s.hom := by
  change ((sliceForgetYonedaIso s.left).hom ≫ yoneda.map (𝟙 _)) ≫
    ((sliceForgetYonedaIso s.left).inv ≫ (sliceForget X).map s.hom) = _
  simp

instance isRegularALocalizer_inverseImage_sliceForget {A : Type v} [SmallCategory A]
    (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) [hV : IsAccessibleALocalizer V]
    [hR : IsRegularALocalizer V] (X : Aᵒᵖ ⥤ Type v) :
    IsRegularALocalizer (V.inverseImage (sliceForget X)) := by
  refine ⟨fun Z ↦ ?_⟩
  let U := sliceForget X
  let E := costructuredArrowSliceEquivalence X Z
  let Q := (projectiveReplacement (CostructuredArrow yoneda X)
    (CostructuredArrow yoneda Z)).obj (representablesOver Z)
  let πQ : Q ⟶ representablesOver Z :=
    (projectiveReplacementπ (CostructuredArrow yoneda X) _).app (representablesOver Z)
  let G := E.inverse ⋙ Q ⋙ U
  let ρ : G ⟶ representablesOver (U.obj Z) :=
    Functor.whiskerLeft E.inverse (Functor.whiskerRight πQ U) ≫
      Functor.whiskerLeft E.inverse (sliceRepresentablesIso X Z).inv ≫
        Functor.whiskerRight E.counit (representablesOver (U.obj Z))
  have hG : projectiveCofibrations A _ (initial.to G) := by
    have hG₀ : projectiveCofibrations (CostructuredArrow yoneda X) _
        (initial.to (E.inverse ⋙ Q)) := projectiveCofibrations_initial_to_comp E.inverse
      (projectiveCofibrations_whiskerLeft_of_isRightAdjoint E.inverse
        (projectiveCofibrations_initial_to_projectiveReplacement _))
    exact projectiveCofibrations_initial_to_whiskerRight (sliceForgetAdjunction X)
      (fun f hf => ((sliceForget X).mono_map_iff_mono f).2 hf) hG₀
  have hρ : ∀ c, V (ρ.app c) := by
    intro c
    have hS := hV.inverseImage_sliceForget X
    have hπ : V (U.map (πQ.app (E.inverse.obj c))) :=
      hS.projectiveReplacementπ_app_mem (representablesOver Z) (E.inverse.obj c)
    have hI : V ((sliceRepresentablesIso X Z).inv.app (E.inverse.obj c)) :=
      hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
    have hC : V ((Functor.whiskerRight E.counit
        (representablesOver (U.obj Z))).app c) :=
      hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
    change V ((U.map (πQ.app (E.inverse.obj c)) ≫
      (sliceRepresentablesIso X Z).inv.app (E.inverse.obj c)) ≫
        (Functor.whiskerRight E.counit (representablesOver (U.obj Z))).app c)
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.comp_mem _ _ _ hπ hI) hC
  let d : colimit G ⟶ U.obj Z :=
    colimit.pre (Q ⋙ U) E.inverse ≫
      (preservesColimitIso U Q).inv ≫ U.map (regularizationMap Z)
  have hd : ∀ c, colimit.ι G c ≫ d = ρ.app c ≫ c.hom := by
    intro c
    have hr := sliceRepresentablesIso_inv_comp_hom X Z (E.inverse.obj c)
    have hw : yoneda.map (E.counit.app c).left ≫ c.hom =
        (E.functor.obj (E.inverse.obj c)).hom := CostructuredArrow.w (E.counit.app c)
    have hreg : colimit.ι Q (E.inverse.obj c) ≫ regularizationMap Z =
        πQ.app (E.inverse.obj c) ≫ (E.inverse.obj c).hom :=
      ι_regularizationMap Z (E.inverse.obj c)
    calc
      colimit.ι G c ≫ d =
          U.map (πQ.app (E.inverse.obj c) ≫ (E.inverse.obj c).hom) := by
        change colimit.ι (E.inverse ⋙ (Q ⋙ U)) c ≫
          colimit.pre (Q ⋙ U) E.inverse ≫
            (preservesColimitIso U Q).inv ≫ U.map (regularizationMap Z) = _
        rw [colimit.ι_pre_assoc, ι_preservesColimitIso_inv_assoc]
        exact (U.map_comp _ _).symm.trans (congrArg U.map hreg)
      _ = ρ.app c ≫ c.hom := by
        change U.map (πQ.app (E.inverse.obj c) ≫ (E.inverse.obj c).hom) =
          ((U.map (πQ.app (E.inverse.obj c)) ≫
            (sliceRepresentablesIso X Z).inv.app (E.inverse.obj c)) ≫
              yoneda.map (E.counit.app c).left) ≫ c.hom
        calc
          U.map (πQ.app (E.inverse.obj c) ≫ (E.inverse.obj c).hom) =
              U.map (πQ.app (E.inverse.obj c)) ≫ U.map (E.inverse.obj c).hom :=
            U.map_comp _ _
          _ = U.map (πQ.app (E.inverse.obj c)) ≫
              ((sliceRepresentablesIso X Z).inv.app (E.inverse.obj c) ≫
                (E.functor.obj (E.inverse.obj c)).hom) :=
            congrArg (U.map (πQ.app (E.inverse.obj c)) ≫ ·) hr.symm
          _ = ((U.map (πQ.app (E.inverse.obj c)) ≫
              (sliceRepresentablesIso X Z).inv.app (E.inverse.obj c)) ≫
                yoneda.map (E.counit.app c).left) ≫ c.hom := by
            rw [← hw]
            simp only [Category.assoc]
            rfl
  have hdV : V d := hV.mem_of_isRegular_resolution (hR.isRegular (U.obj Z)) hG ρ hρ d hd
  have hpre : V (colimit.pre (Q ⋙ U) E.inverse) :=
    hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
  have hpc : V (preservesColimitIso U Q).inv :=
    hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
  exact MorphismProperty.of_precomp _ _ _ (MorphismProperty.comp_mem _ _ _ hpre hpc) hdV

end Atoms.Homotopical
