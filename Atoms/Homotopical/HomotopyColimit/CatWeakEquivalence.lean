import Atoms.Homotopical.HomotopyColimit.ColimitInvariance
import Mathlib.CategoryTheory.Category.Cat.Terminal

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}

theorem IsAccessibleALocalizer.projectiveReplacementπ_app_mem [hV : IsAccessibleALocalizer V]
    {I : Type v} [SmallCategory I] (F : I ⥤ Aᵒᵖ ⥤ Type v) (i : I) :
    V (((projectiveReplacementπ A I).app F).app i) :=
  hV.isALocalizer.rlp_monomorphisms_le _ (rlp_monomorphisms_projectiveReplacementπ_app F i)

theorem IsAccessibleALocalizer.exists_lift_projectiveReplacementπ [hV : IsAccessibleALocalizer V]
    {I : Type v} [SmallCategory I] {D G : I ⥤ Aᵒᵖ ⥤ Type v}
    (hG : projectiveCofibrations A I (initial.to G)) (α : G ⟶ D) (hα : ∀ i, V (α.app i)) :
    ∃ ℓ : G ⟶ (projectiveReplacement A I).obj D,
      ℓ ≫ (projectiveReplacementπ A I).app D = α ∧ (∀ i, V (ℓ.app i)) ∧ V (colimMap ℓ) := by
  obtain ⟨ℓ, -, hℓ⟩ := exists_lift_of_projectiveCofibrations hG
    (rlp_monomorphisms_projectiveReplacementπ_app D) (initial.to _) α (initial.hom_ext _ _)
  have hℓV : ∀ i, V (ℓ.app i) := fun i ↦ V.of_postcomp _ _
    (hV.projectiveReplacementπ_app_mem D i) (by rw [← NatTrans.comp_app, hℓ]; exact hα i)
  exact ⟨ℓ, hℓ, hℓV, hV.colimMap_mem hG
    (projectiveCofibrations_initial_to_projectiveReplacement D) ℓ hℓV⟩

theorem IsAccessibleALocalizer.hocolimComparison_mem_iff [hV : IsAccessibleALocalizer V]
    {I J : Type v} [SmallCategory I] [SmallCategory J] (u : I ⥤ J) (X : Aᵒᵖ ⥤ Type v)
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (hG : projectiveCofibrations A J (initial.to G))
    (πG : G ⟶ (Functor.const J).obj X) (hπG : ∀ j, V (πG.app j))
    {F : I ⥤ Aᵒᵖ ⥤ Type v} (hF : projectiveCofibrations A I (initial.to F))
    (πF : F ⟶ u ⋙ G) (hπF : ∀ i, V (πF.app i)) :
    V (hocolimComparison u X) ↔ V (colimMap πF ≫ colimit.pre G u) := by
  obtain ⟨ℓ, hℓ, hℓV, hℓc⟩ := hV.exists_lift_projectiveReplacementπ hG πG hπG
  obtain ⟨m, hm, hmV, hmc⟩ := hV.exists_lift_projectiveReplacementπ hF
    (πF ≫ Functor.whiskerLeft u ℓ) fun i ↦ V.comp_mem _ _ (hπF i) (hℓV (u.obj i))
  have key : colimMap m ≫ hocolimComparison u X =
      (colimMap πF ≫ colimit.pre G u) ≫ colimMap ℓ := by
    apply colimit.hom_ext
    intro i
    have hi := congr_app hm i
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hi
    simp [hocolimComparison, reassoc_of% hi]
  constructor
  · intro h
    have hc := V.comp_mem _ _ hmc h
    rw [key] at hc
    exact V.of_postcomp _ _ hℓc hc
  · intro h
    have hc := V.comp_mem _ _ h hℓc
    rw [← key] at hc
    exact V.of_precomp _ _ hmc hc

theorem IsAccessibleALocalizer.catWeakEquivalences_containsIdentities
    [hV : IsAccessibleALocalizer V] : (catWeakEquivalences V).ContainsIdentities := by
  refine ⟨fun C ↦ ?_⟩
  let G₀ := (projectiveReplacement A C).obj ((Functor.const C).obj (⊤_ (Aᵒᵖ ⥤ Type v)))
  change V (hocolimComparison (𝟭 C) _)
  rw [hV.hocolimComparison_mem_iff (𝟭 C) _
    (projectiveCofibrations_initial_to_projectiveReplacement _)
    ((projectiveReplacementπ A C).app _) (hV.projectiveReplacementπ_app_mem _)
    (projectiveCofibrations_initial_to_projectiveReplacement _)
    (𝟙 G₀ : G₀ ⟶ 𝟭 C ⋙ G₀)
    (fun _ ↦ hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))]
  exact hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)

theorem IsAccessibleALocalizer.hocolimComparison_comp_mem_iff [hV : IsAccessibleALocalizer V]
    {I J K : Type v} [SmallCategory I] [SmallCategory J] [SmallCategory K] (u : I ⥤ J)
    (u' : J ⥤ K) (X : Aᵒᵖ ⥤ Type v) :
    ∃ (F : I ⥤ Aᵒᵖ ⥤ Type v) (a : colimit F ⟶ colimit ((projectiveReplacement A J).obj
        (u' ⋙ (projectiveReplacement A K).obj ((Functor.const K).obj X)))),
      (V (hocolimComparison u X) ↔ V a) ∧
        (V (hocolimComparison (u ⋙ u') X) ↔ V (a ≫ hocolimComparison u' X)) := by
  let G₀ := (projectiveReplacement A K).obj ((Functor.const K).obj X)
  let G := (projectiveReplacement A J).obj (u' ⋙ G₀)
  let πJ := (projectiveReplacementπ A J).app (u' ⋙ G₀)
  let π₀ := (projectiveReplacementπ A K).app ((Functor.const K).obj X)
  let πG : G ⟶ (Functor.const J).obj X := πJ ≫ Functor.whiskerLeft u' π₀
  let F := (projectiveReplacement A I).obj (u ⋙ G)
  let πF := (projectiveReplacementπ A I).app (u ⋙ G)
  have hF := projectiveCofibrations_initial_to_projectiveReplacement (A := A) (u ⋙ G)
  refine ⟨F, colimMap πF ≫ colimit.pre G u, ?_, ?_⟩
  · exact hV.hocolimComparison_mem_iff u X
      (projectiveCofibrations_initial_to_projectiveReplacement _) πG
      (fun j ↦ V.comp_mem _ _ (hV.projectiveReplacementπ_app_mem _ j)
        (hV.projectiveReplacementπ_app_mem _ (u'.obj j)))
      hF πF (hV.projectiveReplacementπ_app_mem _)
  · rw [hV.hocolimComparison_mem_iff (u ⋙ u') X
      (projectiveCofibrations_initial_to_projectiveReplacement _) π₀
      (hV.projectiveReplacementπ_app_mem _) hF
      (πF ≫ Functor.whiskerLeft u πJ : F ⟶ (u ⋙ u') ⋙ G₀)
      (fun i ↦ V.comp_mem _ _ (hV.projectiveReplacementπ_app_mem _ i)
        (hV.projectiveReplacementπ_app_mem _ (u.obj i)))]
    have key : colimMap (πF ≫ Functor.whiskerLeft u πJ : F ⟶ (u ⋙ u') ⋙ G₀) ≫
        colimit.pre G₀ (u ⋙ u') = (colimMap πF ≫ colimit.pre G u) ≫ hocolimComparison u' X := by
      apply colimit.hom_ext
      intro i
      simp only [Functor.id_obj, ι_colimMap_assoc, Functor.comp_obj, NatTrans.comp_app,
        Functor.whiskerLeft_app, colimit.ι_pre, Category.assoc, hocolimComparison,
        colimit.ι_pre_assoc, G, πJ]
      rfl
    rw [key]

theorem IsAccessibleALocalizer.catWeakEquivalences_hasTwoOutOfThreeProperty
    [hV : IsAccessibleALocalizer V] : (catWeakEquivalences V).HasTwoOutOfThreeProperty := by
  refine
    { comp_mem := fun {I J K} u u' hu hu' ↦ ?_
      of_postcomp := fun {I J K} u u' hu' huu' ↦ ?_
      of_precomp := fun {I J K} u u' hu huu' ↦ ?_ }
  all_goals
    obtain ⟨F, a, h1, h2⟩ := hV.hocolimComparison_comp_mem_iff u.toFunctor u'.toFunctor
      (⊤_ (Aᵒᵖ ⥤ Type v))
  · exact h2.2 (V.comp_mem _ _ (h1.1 hu) hu')
  · exact h1.2 (V.of_postcomp _ _ hu' (h2.1 huu'))
  · exact V.of_precomp _ _ (h1.1 hu) (h2.1 huu')

theorem IsAccessibleALocalizer.catWeakEquivalences_of_isRightAdjoint
    [hV : IsAccessibleALocalizer V] {I J : Cat.{v, v}} (u : I ⟶ J) [u.toFunctor.IsRightAdjoint] :
    catWeakEquivalences V u := by
  let G₀ := (projectiveReplacement A J).obj ((Functor.const J).obj (⊤_ (Aᵒᵖ ⥤ Type v)))
  have hF : projectiveCofibrations A I (initial.to (u.toFunctor ⋙ G₀)) :=
    projectiveCofibrations_initial_to_comp u.toFunctor
      (projectiveCofibrations_whiskerLeft_of_isRightAdjoint u.toFunctor
        (projectiveCofibrations_initial_to_projectiveReplacement _))
  have := Functor.final_of_adjunction (Adjunction.ofIsRightAdjoint u.toFunctor)
  change V (hocolimComparison u.toFunctor _)
  rw [hV.hocolimComparison_mem_iff u.toFunctor _
    (projectiveCofibrations_initial_to_projectiveReplacement _)
    ((projectiveReplacementπ A J).app _) (hV.projectiveReplacementπ_app_mem _) hF
    (𝟙 (u.toFunctor ⋙ G₀))
    (fun _ ↦ hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))]
  exact hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)

noncomputable def starAdjunctionFromPUnitTerminal (D : Type v) [Category.{v} D] [HasTerminal D] :
    Functor.star.{v} D ⊣ Functor.fromPUnit.{v} (⊤_ D) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X _ ↦
        { toFun := fun _ ↦ terminal.from X
          invFun := fun _ ↦ Discrete.eqToHom (Subsingleton.elim _ _)
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ terminal.hom_ext _ _ }
      homEquiv_naturality_left_symm := fun _ _ ↦ Subsingleton.elim _ _
      homEquiv_naturality_right := fun _ _ ↦ terminal.hom_ext _ _ }

theorem IsAccessibleALocalizer.catWeakEquivalences_terminal_from [hV : IsAccessibleALocalizer V]
    (D : Cat.{v, v}) [HasTerminal D] : catWeakEquivalences V (terminal.from D) := by
  let P := Cat.of (Discrete PUnit.{v + 1})
  let r : P ⟶ D := (Functor.fromPUnit.{v} (⊤_ D)).toCatHom
  let e : P ≅ ⊤_ Cat.{v, v} := Cat.isTerminalDiscretePUnit.uniqueUpToIso terminalIsTerminal
  have : r.toFunctor.IsRightAdjoint := ⟨_, ⟨starAdjunctionFromPUnitTerminal D⟩⟩
  have : e.hom.toFunctor.IsRightAdjoint := ⟨_, ⟨(Cat.equivOfIso e).symm.toAdjunction⟩⟩
  refine (hV.catWeakEquivalences_hasTwoOutOfThreeProperty).of_precomp r (terminal.from D)
    (hV.catWeakEquivalences_of_isRightAdjoint r) ?_
  rw [terminal.hom_ext (r ≫ terminal.from D) e.hom]
  exact hV.catWeakEquivalences_of_isRightAdjoint e.hom

section LocalCriterion

variable {I J S : Type v} [SmallCategory I] [SmallCategory J] [SmallCategory S]

@[simps]
def whiskerLeftProjPre (u : I ⥤ J) (w : J ⥤ S) {P : I ⥤ Aᵒᵖ ⥤ Type v}
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) (s : S) :
    CostructuredArrow.proj (u ⋙ w) s ⋙ P ⟶
      CostructuredArrow.pre u w s ⋙ CostructuredArrow.proj w s ⋙ G where
  app X := π.app X.left
  naturality _ _ f := π.naturality f.left

noncomputable def lanComparisonApp (u : I ⥤ J) (w : J ⥤ S) {P : I ⥤ Aᵒᵖ ⥤ Type v}
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) (s : S) :
    colimit (CostructuredArrow.proj (u ⋙ w) s ⋙ P) ⟶
      colimit (CostructuredArrow.proj w s ⋙ G) :=
  colimMap (whiskerLeftProjPre u w π s) ≫
    colimit.pre (CostructuredArrow.proj w s ⋙ G) (CostructuredArrow.pre u w s)

@[reassoc]
theorem ι_lanComparisonApp (u : I ⥤ J) (w : J ⥤ S) {P : I ⥤ Aᵒᵖ ⥤ Type v}
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) (s : S) (X : CostructuredArrow (u ⋙ w) s) :
    colimit.ι (CostructuredArrow.proj (u ⋙ w) s ⋙ P) X ≫ lanComparisonApp u w π s =
      π.app X.left ≫ colimit.ι (CostructuredArrow.proj w s ⋙ G)
        ((CostructuredArrow.pre u w s).obj X) := by
  rw [lanComparisonApp, ι_colimMap_assoc, colimit.ι_pre, whiskerLeftProjPre_app]
  rfl

@[reassoc]
theorem ι_pointwiseLeftKanExtension_map (L : I ⥤ S) (F : I ⥤ Aᵒᵖ ⥤ Type v) {s s' : S}
    (f : s ⟶ s') (X : CostructuredArrow L s) :
    colimit.ι (CostructuredArrow.proj L s ⋙ F) X ≫ (L.pointwiseLeftKanExtension F).map f =
      colimit.ι (CostructuredArrow.proj L s' ⋙ F) ((CostructuredArrow.map f).obj X) := by
  simp only [Functor.pointwiseLeftKanExtension_map]
  exact colimit.ι_desc _ _

noncomputable def lanComparison (u : I ⥤ J) (w : J ⥤ S) {P : I ⥤ Aᵒᵖ ⥤ Type v}
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) :
    (u ⋙ w).pointwiseLeftKanExtension P ⟶ w.pointwiseLeftKanExtension G where
  app s := lanComparisonApp u w π s
  naturality s s' f := colimit.hom_ext fun X ↦ by
    refine ((Category.assoc _ _ _).symm.trans
      (ι_pointwiseLeftKanExtension_map_assoc (u ⋙ w) P f X _)).trans ?_
    refine ((ι_lanComparisonApp u w π s' _).trans ?_).trans
      (ι_lanComparisonApp_assoc u w π s X _).symm
    exact whisker_eq (π.app X.left)
      (ι_pointwiseLeftKanExtension_map w G f ((CostructuredArrow.pre u w s).obj X)).symm

theorem pointwiseLeftKanExtensionUnit_app_lanComparison_app (u : I ⥤ J) (w : J ⥤ S)
    {P : I ⥤ Aᵒᵖ ⥤ Type v} {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) (i : I) :
    ((u ⋙ w).pointwiseLeftKanExtensionUnit P).app i ≫ (lanComparison u w π).app (w.obj (u.obj i)) =
      π.app i ≫ (w.pointwiseLeftKanExtensionUnit G).app (u.obj i) := by
  simp only [Functor.pointwiseLeftKanExtensionUnit_app]
  exact ι_lanComparisonApp u w π _ _

theorem colimMap_comp_colimit_pre_eq (u : I ⥤ J) (w : J ⥤ S) {P : I ⥤ Aᵒᵖ ⥤ Type v}
    {G : J ⥤ Aᵒᵖ ⥤ Type v} (π : P ⟶ u ⋙ G) :
    colimMap π ≫ colimit.pre G u =
      (((u ⋙ w).pointwiseLeftKanExtension P).colimitIsoOfIsLeftKanExtension
          ((u ⋙ w).pointwiseLeftKanExtensionUnit P)).inv ≫
        colimMap (lanComparison u w π) ≫
          ((w.pointwiseLeftKanExtension G).colimitIsoOfIsLeftKanExtension
            (w.pointwiseLeftKanExtensionUnit G)).hom := by
  refine colimit.hom_ext fun i ↦ ?_
  rw [ι_colimMap_assoc, colimit.ι_pre, Functor.ι_colimitIsoOfIsLeftKanExtension_inv_assoc,
    ι_colimMap_assoc, ← Category.assoc]
  erw [pointwiseLeftKanExtensionUnit_app_lanComparison_app u w π i]
  erw [Category.assoc, Functor.ι_colimitIsoOfIsLeftKanExtension_hom]

end LocalCriterion

theorem IsAccessibleALocalizer.catWeakEquivalences_of_forall_pre [hV : IsAccessibleALocalizer V]
    {I J S : Cat.{v, v}} (u : I ⟶ J) (w : J ⟶ S)
    (h : ∀ s : S, catWeakEquivalences V
      (CostructuredArrow.pre u.toFunctor w.toFunctor s).toCatHom) :
    catWeakEquivalences V u := by
  let T := ⊤_ (Aᵒᵖ ⥤ Type v)
  let G := (projectiveReplacement A J).obj ((Functor.const J).obj T)
  let π₀ := (projectiveReplacementπ A J).app ((Functor.const J).obj T)
  let P := (projectiveReplacement A I).obj (u.toFunctor ⋙ G)
  let π := (projectiveReplacementπ A I).app (u.toFunctor ⋙ G)
  have hG : projectiveCofibrations A J (initial.to G) :=
    projectiveCofibrations_initial_to_projectiveReplacement _
  have hP : projectiveCofibrations A I (initial.to P) :=
    projectiveCofibrations_initial_to_projectiveReplacement _
  change V (hocolimComparison u.toFunctor T)
  rw [hV.hocolimComparison_mem_iff u.toFunctor T hG π₀ (hV.projectiveReplacementπ_app_mem _) hP π
    (hV.projectiveReplacementπ_app_mem _), colimMap_comp_colimit_pre_eq u.toFunctor w.toFunctor π]
  refine V.comp_mem _ _ (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
    (V.comp_mem _ _ ?_ (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)))
  refine hV.colimMap_mem (projectiveCofibrations_initial_to_pointwiseLeftKanExtension _ hP)
    (projectiveCofibrations_initial_to_pointwiseLeftKanExtension _ hG) _ fun s ↦ ?_
  have hs := h s
  change V (hocolimComparison (CostructuredArrow.pre u.toFunctor w.toFunctor s) T) at hs
  let πG : CostructuredArrow.proj w.toFunctor s ⋙ G ⟶ (Functor.const _).obj T :=
    { app := fun X ↦ π₀.app X.left
      naturality := fun _ _ f ↦ π₀.naturality f.left }
  rw [hV.hocolimComparison_mem_iff _ T
    (projectiveCofibrations_initial_to_comp _
      (projectiveCofibrations_whiskerLeft_proj w.toFunctor s hG))
    πG (fun X ↦ hV.projectiveReplacementπ_app_mem _ X.left)
    (projectiveCofibrations_initial_to_comp _
      (projectiveCofibrations_whiskerLeft_proj (u.toFunctor ⋙ w.toFunctor) s hP))
    (whiskerLeftProjPre u.toFunctor w.toFunctor π s)
    (fun X ↦ hV.projectiveReplacementπ_app_mem _ X.left)] at hs
  exact hs

end Atoms.Homotopical
