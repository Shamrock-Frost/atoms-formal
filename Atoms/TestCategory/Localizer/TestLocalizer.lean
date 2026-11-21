import Atoms.Homotopical.HomotopyColimit.CatWeakEquivalence
import Atoms.TestCategory.LocalTestCriterion

open CategoryTheory Limits MorphismProperty Opposite Atoms.Homotopical

namespace Atoms.TestCategory

universe u

variable {C : Type u} [SmallCategory C] {V : MorphismProperty (Cᵒᵖ ⥤ Type u)}

noncomputable abbrev elementsReplacement (X : Cᵒᵖ ⥤ Type u) :
    (X.Elements)ᵒᵖ ⥤ Cᵒᵖ ⥤ Type u :=
  (CategoryOfElements.costructuredArrowYonedaEquivalence X).functor ⋙
    (projectiveReplacement C _).obj (representablesOver X)

theorem projectiveCofibrations_initial_to_elementsReplacement (X : Cᵒᵖ ⥤ Type u) :
    projectiveCofibrations C _ (initial.to (elementsReplacement X)) := by
  let e := CategoryOfElements.costructuredArrowYonedaEquivalence X
  have : e.functor.IsRightAdjoint := ⟨_, ⟨e.symm.toAdjunction⟩⟩
  exact projectiveCofibrations_initial_to_comp e.functor
    (projectiveCofibrations_whiskerLeft_of_isRightAdjoint e.functor
      (projectiveCofibrations_initial_to_projectiveReplacement _))

theorem mem_terminal_from_elementsReplacement_obj [hV : IsAccessibleALocalizer V]
    [ht : IsTestALocalizer V] (X : Cᵒᵖ ⥤ Type u) (i : (X.Elements)ᵒᵖ) :
    V (terminal.from ((elementsReplacement X).obj i)) := by
  have e : terminal.from ((elementsReplacement X).obj i) =
      ((projectiveReplacementπ C _).app (representablesOver X)).app
        ((CategoryOfElements.costructuredArrowYonedaEquivalence X).functor.obj i) ≫
          terminal.from (yoneda.obj (unop (unop i).1)) := terminal.hom_ext _ _
  rw [e]
  exact V.comp_mem _ _ (hV.projectiveReplacementπ_app_mem _ _) (ht.terminal_from_yoneda _)

theorem ι_elementsReplacement_regularizationMap (X : Cᵒᵖ ⥤ Type u) (i : (X.Elements)ᵒᵖ) :
    colimit.ι (elementsReplacement X) i ≫
        colimit.pre ((projectiveReplacement C _).obj (representablesOver X))
          (CategoryOfElements.costructuredArrowYonedaEquivalence X).functor ≫
            regularizationMap X =
      ((projectiveReplacementπ C _).app (representablesOver X)).app
          ((CategoryOfElements.costructuredArrowYonedaEquivalence X).functor.obj i) ≫
        yonedaEquiv.symm (unop i).2 :=
  (colimit.ι_pre_assoc (F := (projectiveReplacement C _).obj (representablesOver X))
    (E := (CategoryOfElements.costructuredArrowYonedaEquivalence X).functor) (k := i)
    (h := regularizationMap X)).trans (ι_regularizationMap X _)

theorem mem_colimit_pre_regularizationMap (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [hV : IsAccessibleALocalizer V] [ht : IsTestALocalizer V] (X : Cᵒᵖ ⥤ Type u) :
    V (colimit.pre ((projectiveReplacement C _).obj (representablesOver X))
      (CategoryOfElements.costructuredArrowYonedaEquivalence X).functor ≫
        regularizationMap X) := by
  exact V.comp_mem _ _ (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
    (ht.isRegular X)

theorem catWeakEquivalences_elementsFunctor_map_iff
    [hV : IsAccessibleALocalizer V] [IsTestALocalizer V] {X Y : Cᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) : catWeakEquivalences V ((elementsFunctor C).map f) ↔ V f := by
  let eX := CategoryOfElements.costructuredArrowYonedaEquivalence X
  let eY := CategoryOfElements.costructuredArrowYonedaEquivalence Y
  let u : (X.Elements)ᵒᵖ ⥤ (Y.Elements)ᵒᵖ := (CategoryOfElements.map f).op
  let πX := (projectiveReplacementπ C _).app (representablesOver X)
  let πY := (projectiveReplacementπ C _).app (representablesOver Y)
  let p : u ⋙ elementsReplacement Y ⟶ u ⋙ eY.functor ⋙ representablesOver Y :=
    Functor.whiskerLeft (u ⋙ eY.functor) πY
  let g : elementsReplacement X ⟶ u ⋙ eY.functor ⋙ representablesOver Y :=
    Functor.whiskerLeft eX.functor πX
  obtain ⟨l, -, hl⟩ := exists_lift_of_projectiveCofibrations
    (projectiveCofibrations_initial_to_elementsReplacement X) (p := p)
    (fun i ↦ rlp_monomorphisms_projectiveReplacementπ_app (representablesOver Y)
      (eY.functor.obj (u.obj i)))
    (initial.to _) g (initial.hom_ext _ _)
  have hl' : ∀ i, l.app i ≫ πY.app (eY.functor.obj (u.obj i)) = πX.app (eX.functor.obj i) :=
    fun i ↦ congr_app hl i
  have hπF : ∀ i, V (l.app i) := fun i ↦ V.of_postcomp _ _
    (hV.projectiveReplacementπ_app_mem _ (eY.functor.obj (u.obj i)))
    (by rw [hl' i]; exact hV.projectiveReplacementπ_app_mem _ _)
  change V (hocolimComparison u _) ↔ V f
  rw [hV.hocolimComparison_mem_iff u _ (projectiveCofibrations_initial_to_elementsReplacement Y)
    (FunctorToTypes.toConstTerminal _) (mem_terminal_from_elementsReplacement_obj Y)
    (projectiveCofibrations_initial_to_elementsReplacement X) l hπF]
  have sq : (colimMap l ≫ colimit.pre (elementsReplacement Y) u) ≫
      (colimit.pre ((projectiveReplacement C _).obj (representablesOver Y)) eY.functor ≫
        regularizationMap Y) =
      (colimit.pre ((projectiveReplacement C _).obj (representablesOver X)) eX.functor ≫
        regularizationMap X) ≫ f := by
    apply colimit.hom_ext
    intro i
    simp only [Category.assoc, ι_colimMap_assoc, colimit.ι_pre_assoc]
    rw [ι_elementsReplacement_regularizationMap Y (u.obj i),
      reassoc_of% (ι_elementsReplacement_regularizationMap X i), reassoc_of% (hl' i)]
    exact congrArg (πX.app (eX.functor.obj i) ≫ ·)
      (yonedaEquiv_symm_naturality_right _ f (unop i).2).symm
  rw [← V.postcomp_iff _ _ (mem_colimit_pre_regularizationMap V Y), sq,
    V.precomp_iff _ _ (mem_colimit_pre_regularizationMap V X)]

theorem catWeakEquivalences_star_elementsFunctor_obj_iff (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [hV : IsAccessibleALocalizer V] [IsTestALocalizer V] (X : Cᵒᵖ ⥤ Type u) :
    catWeakEquivalences V (Functor.star.{u} (X.Elements)ᵒᵖ).toCatHom ↔ V (terminal.from X) := by
  let s := Functor.star.{u} (X.Elements)ᵒᵖ
  let P := Discrete PUnit.{u + 1}
  let T := ⊤_ (Cᵒᵖ ⥤ Type u)
  let G := (projectiveReplacement C P).obj ((Functor.const P).obj T)
  let πG := (projectiveReplacementπ C P).app ((Functor.const P).obj T)
  obtain ⟨l, -, hl⟩ := exists_lift_of_projectiveCofibrations
    (projectiveCofibrations_initial_to_elementsReplacement X) (p := Functor.whiskerLeft s πG)
    (fun i ↦ rlp_monomorphisms_projectiveReplacementπ_app _ (s.obj i))
    (initial.to _)
    (FunctorToTypes.toConstTerminal (elementsReplacement X) : _ ⟶ s ⋙ (Functor.const P).obj T)
    (initial.hom_ext _ _)
  have hπF : ∀ i, V (l.app i) := fun i ↦ V.of_postcomp _ _
    (hV.projectiveReplacementπ_app_mem _ (s.obj i))
    (by
      rw [← Functor.whiskerLeft_app s πG, ← NatTrans.comp_app, hl]
      exact mem_terminal_from_elementsReplacement_obj X i)
  change V (hocolimComparison s T) ↔ _
  rw [hV.hocolimComparison_mem_iff s T (projectiveCofibrations_initial_to_projectiveReplacement _)
    πG (hV.projectiveReplacementπ_app_mem _)
    (projectiveCofibrations_initial_to_elementsReplacement X) l hπF]
  let pt : P := ⟨PUnit.unit⟩
  have hpt : IsTerminal pt :=
    IsTerminal.ofUniqueHom (fun _ ↦ Discrete.eqToHom (Subsingleton.elim _ _))
      (fun _ _ ↦ Subsingleton.elim _ _)
  have := isIso_ι_of_isTerminal hpt G
  have hG : V (terminal.from (colimit G)) := by
    rw [terminal.hom_ext (terminal.from _) (inv (colimit.ι G pt) ≫ πG.app pt)]
    exact V.comp_mem _ _ (hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
      (hV.projectiveReplacementπ_app_mem _ _)
  have sq : (colimMap l ≫ colimit.pre G s) ≫ terminal.from (colimit G) =
      (colimit.pre ((projectiveReplacement C _).obj (representablesOver X))
        (CategoryOfElements.costructuredArrowYonedaEquivalence X).functor ≫
          regularizationMap X) ≫ terminal.from X := terminal.hom_ext _ _
  rw [← V.postcomp_iff _ _ hG, sq, V.precomp_iff _ _ (mem_colimit_pre_regularizationMap V X)]

theorem catWeakEquivalences_terminal_from_elementsFunctor_obj_iff
    [hV : IsAccessibleALocalizer V] [IsTestALocalizer V] (X : Cᵒᵖ ⥤ Type u) :
    catWeakEquivalences V (terminal.from ((elementsFunctor C).obj X)) ↔
      V (terminal.from X) := by
  have h3 := hV.catWeakEquivalences_hasTwoOutOfThreeProperty
  let s : (elementsFunctor C).obj X ⟶ Cat.of (Discrete PUnit.{u + 1}) :=
    (Functor.star.{u} (X.Elements)ᵒᵖ).toCatHom
  let e : Cat.of (Discrete PUnit.{u + 1}) ≅ ⊤_ Cat.{u, u} :=
    Cat.isTerminalDiscretePUnit.uniqueUpToIso terminalIsTerminal
  have : e.hom.toFunctor.IsRightAdjoint := ⟨_, ⟨(Cat.equivOfIso e).symm.toAdjunction⟩⟩
  have he := hV.catWeakEquivalences_of_isRightAdjoint e.hom
  rw [terminal.hom_ext (terminal.from _) (s ≫ e.hom),
    ← catWeakEquivalences_star_elementsFunctor_obj_iff V X]
  exact ⟨fun h ↦ (catWeakEquivalences V).of_postcomp _ _ he h,
    fun h ↦ (catWeakEquivalences V).comp_mem _ _ h he⟩

theorem catWeakEquivalences_terminal_from_cat [hV : IsAccessibleALocalizer V]
    [IsTestALocalizer V] : catWeakEquivalences V (terminal.from (Cat.of C)) := by
  have h3 := hV.catWeakEquivalences_hasTwoOutOfThreeProperty
  let T := ⊤_ (Cᵒᵖ ⥤ Type u)
  let i : Cat.of C ⟶ (elementsFunctor C).obj T := (elementsTerminalEquivalence C).inverse.toCatHom
  have : i.toFunctor.IsRightAdjoint := ⟨_, ⟨(elementsTerminalEquivalence C).toAdjunction⟩⟩
  have hT : V (terminal.from T) := by
    rw [terminal.hom_ext (terminal.from T) (𝟙 T)]
    exact hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _)
  rw [terminal.hom_ext (terminal.from (Cat.of C)) (i ≫ terminal.from _)]
  exact (catWeakEquivalences V).comp_mem _ _ (hV.catWeakEquivalences_of_isRightAdjoint i)
    ((catWeakEquivalences_terminal_from_elementsFunctor_obj_iff T).2 hT)

theorem catWeakEquivalences_counit_app [hV : IsAccessibleALocalizer V]
    [IsTestALocalizer V] (D : Cat.{u, u}) :
    catWeakEquivalences V ((nerveAdjunction C).counit.app D) := by
  have h3 := hV.catWeakEquivalences_hasTwoOutOfThreeProperty
  refine hV.catWeakEquivalences_of_forall_pre _ (𝟙 D) fun d ↦ ?_
  let S := Cat.of (CostructuredArrow ((nerveAdjunction C).counit.app D).toFunctor d)
  let T := Cat.of (CostructuredArrow (𝟭 D) d)
  let N := (nerveFunctor C).obj (Cat.of (Over d))
  let E := counitCostructuredArrowEquivalence C D d
  let e : S ⟶ (elementsFunctor C).obj N := E.functor.toCatHom
  have : e.toFunctor.IsRightAdjoint := ⟨_, ⟨E.symm.toAdjunction⟩⟩
  have : HasTerminal T := inferInstanceAs (HasTerminal (CostructuredArrow (𝟭 D) ((𝟭 D).obj d)))
  have : HasTerminal (Cat.of (Over d)) := inferInstanceAs (HasTerminal (Over d))
  have hS : catWeakEquivalences V (terminal.from S) := by
    rw [terminal.hom_ext (terminal.from S) (e ≫ terminal.from _)]
    exact (catWeakEquivalences V).comp_mem _ _ (hV.catWeakEquivalences_of_isRightAdjoint e)
      ((catWeakEquivalences_terminal_from_elementsFunctor_obj_iff N).2
        (IsALocalizer.rlp_monomorphisms_le _ (rlp_terminal_from_nerveFunctor_obj C _)))
  let p : S ⟶ T := (CostructuredArrow.pre ((nerveAdjunction C).counit.app D).toFunctor
    (𝟭 D) d).toCatHom
  change catWeakEquivalences V p
  refine (catWeakEquivalences V).of_postcomp p (terminal.from T)
    (hV.catWeakEquivalences_terminal_from T) ?_
  rw [terminal.hom_ext (p ≫ terminal.from T) (terminal.from S)]
  exact hS

theorem catWeakEquivalences_eq_inverseImage_nerveFunctor [hV : IsAccessibleALocalizer V]
    [IsTestALocalizer V] : catWeakEquivalences V = V.inverseImage (nerveFunctor C) := by
  have := hV.catWeakEquivalences_hasTwoOutOfThreeProperty
  have := hV.catWeakEquivalences_containsIdentities
  refine MorphismProperty.ext _ _ fun A B u ↦ ?_
  rw [MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction C) (catWeakEquivalences V)
    catWeakEquivalences_counit_app u, catWeakEquivalences_elementsFunctor_map_iff,
    MorphismProperty.inverseImage_iff]

def BasicLocalizer.ofTestALocalizer (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [hV : IsAccessibleALocalizer V] [IsTestALocalizer V] : BasicLocalizer.{u} where
  W := V.inverseImage (nerveFunctor C)
  containsIdentities := inferInstance
  hasTwoOutOfThree := inferInstance
  isStableUnderRetracts := inferInstance
  terminal_aspherical D _ := by
    rw [← catWeakEquivalences_eq_inverseImage_nerveFunctor]
    exact hV.catWeakEquivalences_terminal_from D
  quillenA f g h := by
    rw [← catWeakEquivalences_eq_inverseImage_nerveFunctor] at h ⊢
    exact hV.catWeakEquivalences_of_forall_pre f g h

theorem BasicLocalizer.ofTestALocalizer_wPsh (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [IsAccessibleALocalizer V] [IsTestALocalizer V] :
    (BasicLocalizer.ofTestALocalizer V).wPsh C = V := by
  refine MorphismProperty.ext _ _ fun X Y f ↦ ?_
  change V.inverseImage (nerveFunctor C) ((elementsFunctor C).map f) ↔ V f
  rw [← catWeakEquivalences_eq_inverseImage_nerveFunctor]
  exact catWeakEquivalences_elementsFunctor_map_iff f

theorem isTest_ofTestALocalizer (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [IsAccessibleALocalizer V] [IsTestALocalizer V] :
    BasicLocalizer.IsTest (BasicLocalizer.ofTestALocalizer V) C := by
  refine BasicLocalizer.isTest_of_rlp_le _ C ?_ ?_
  · change V.inverseImage (nerveFunctor C) (terminal.from (Cat.of C))
    rw [← catWeakEquivalences_eq_inverseImage_nerveFunctor]
    exact catWeakEquivalences_terminal_from_cat
  · rw [BasicLocalizer.ofTestALocalizer_wPsh]
    exact IsALocalizer.rlp_monomorphisms_le

end Atoms.TestCategory
