import Atoms.Homotopical.Regular.Descent

open CategoryTheory Limits Opposite Atoms Atoms.Homotopical MorphismProperty

namespace Atoms.Homotopical

universe v

instance IsALocalizer.inverseImage_prod {A : Type v} [SmallCategory A]
    {W : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hW : IsALocalizer W]
    (Z : Aᵒᵖ ⥤ Type v) : IsALocalizer (W.inverseImage (prod.functor.obj Z)) :=
  have : PreservesColimitsOfSize.{v, v} (prod.functor.obj Z) :=
    (Adjunction.ofIsLeftAdjoint (prod.functor.obj Z)).leftAdjoint_preservesColimits
  hW.inverseImage (prod.functor.obj Z) (fun f (_ : Mono f) ↦ (inferInstance : Mono (prod.map _ f)))
    fun f hf ↦ (monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.of_isPullback (.of_prod_snd_with_id f Z) hf

theorem IsAccessibleALocalizer.prod_map_regularizationMap_mem
    {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] [IsRegularALocalizer V]
    (Z X : Aᵒᵖ ⥤ Type v) : V (prod.map (𝟙 Z) (regularizationMap X)) := by
  let F := prod.functor.obj Z
  let Q := (projectiveReplacement A (CostructuredArrow yoneda X)).obj
    (representablesOver X)
  let π : Q ⟶ representablesOver X :=
    (projectiveReplacementπ A _).app (representablesOver X)
  let D := representablesOver X ⋙ F
  let s : Cocone D := F.mapCocone (Presheaf.tautologicalCocone X)
  let p : s.pt ⟶ X := prod.snd
  let t : D ⟶ representablesOver X :=
    { app := fun _ => prod.snd
      naturality := by
        intro c d f
        exact prod.map_snd (𝟙 Z) (yoneda.map f.left) }
  let G := Q ⋙ F
  let α : G ⟶ D := Functor.whiskerRight π F
  have hpb : ∀ c, IsPullback (t.app c : D.obj c ⟶ yoneda.obj c.left)
      (s.ι.app c) c.hom p := fun c => IsPullback.of_prod_snd_with_id c.hom Z
  have hG : projectiveCofibrations A _ (initial.to G) :=
    projectiveCofibrations_initial_to_whiskerRight (Adjunction.ofIsLeftAdjoint F)
      (fun f (_ : Mono f) ↦ (inferInstance : Mono (prod.map _ f)))
      (projectiveCofibrations_initial_to_projectiveReplacement _)
  have hα : ∀ c, V (α.app c) := fun c =>
    hV.isALocalizer.rlp_monomorphisms_le _
      ((monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.of_isPullback (.of_prod_snd_with_id _ Z)
        (rlp_monomorphisms_projectiveReplacementπ_app (representablesOver X) c))
  have hcore : V (colimMap α ≫ colimit.desc D s) :=
    hV.colimMap_desc_mem_of_isPullback D s p t hpb hG α hα
  have heq : (preservesColimitIso F Q).inv ≫ F.map (regularizationMap X) =
      colimMap α ≫ colimit.desc D s := by
    apply colimit.hom_ext
    intro c
    rw [ι_preservesColimitIso_inv_assoc, ← Functor.map_comp,
      ι_regularizationMap]
    erw [Functor.map_comp]
    erw [ι_colimMap_assoc]
    erw [colimit.ι_desc]
    rfl
  have hIso : V (preservesColimitIso F Q).inv :=
    hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
  have hprod : V (F.map (regularizationMap X)) := by
    apply hV.isALocalizer.hasTwoOutOfThreeProperty.of_precomp _ _ hIso
    rw [heq]
    exact hcore
  exact hprod

theorem prod_map_mem_regularCompletion_bot {A : Type v} [SmallCategory A]
    {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y)
    (hf : regularCompletion (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v)) f)
    (Z : Aᵒᵖ ⥤ Type v) :
    regularCompletion (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v))
      (Limits.prod.map (𝟙 Z) f) := by
  let W := regularCompletion (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type v))
  have : IsRegularALocalizer (W.inverseImage (prod.functor.obj Z)) :=
    ⟨fun T ↦ isAccessibleALocalizer_regularCompletion_bot.prod_map_regularizationMap_mem Z T⟩
  have hmin : W ≤ W.inverseImage (prod.functor.obj Z) := regularCompletion_le bot_le
  exact hmin f hf

end Atoms.Homotopical
