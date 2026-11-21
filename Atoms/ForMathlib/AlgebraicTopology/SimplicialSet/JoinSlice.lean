import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSubcomplex

open CategoryTheory Limits Simplicial Opposite MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.DayConvolution

universe u

namespace SSet

noncomputable def joinLeftUnder (T : SSet.{u}) : SSet.{u} ⥤ Under T where
  obj X := Under.mk (joinInclLeft T X)
  map f := Under.homMk (joinMap (𝟙 T) f) (by simp [joinInclLeft_comp_joinMap])
  map_id X := by ext1; exact joinFunctor.map_id (T, X)
  map_comp f g := by
    ext1
    exact joinFunctor.map_comp (X := (T, _)) (Y := (T, _)) (Z := (T, _)) (𝟙 T, f) (𝟙 T, g)

noncomputable def joinRightUnder (T : SSet.{u}) : SSet.{u} ⥤ Under T where
  obj X := Under.mk (joinInclRight X T)
  map f := Under.homMk (joinMap f (𝟙 T)) (by simp [joinInclRight_comp_joinMap])
  map_id X := by ext1; exact joinFunctor.map_id (X, T)
  map_comp f g := by
    ext1
    exact joinFunctor.map_comp (X := (_, T)) (Y := (_, T)) (Z := (_, T)) (f, 𝟙 T) (g, 𝟙 T)

instance isEmpty_obj_bot (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    IsEmpty (((⊥ : X.Subcomplex) : SSet.{u}).obj n) :=
  ⟨fun x ↦ x.2⟩

theorem isIso_joinInclRight_of_isEmpty (X Y : SSet.{u}) [∀ n, IsEmpty (X.obj n)] :
    IsIso (joinInclRight X Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance n),
    fun t ↦ ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, h⟩, x, y⟩, rfl⟩ :=
    (AugmentedSimplexCategory.bijective_map_unit_app _ _ (.of n.unop)).2 t
  cases a with
  | of k => exact isEmptyElim (α := X.obj (op k)) x
  | star =>
    obtain rfl : b = .of n.unop := h
    refine ⟨y, (congrArg _ (Prod.ext (Subsingleton.elim
      (α := (trivialAugmentation.obj X).obj (op .star)) _ x) rfl)).trans
        (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
          (op (WithInitial.of n.unop)) _).symm⟩

theorem isIso_joinInclLeft_of_isEmpty (X Y : SSet.{u}) [∀ n, IsEmpty (Y.obj n)] :
    IsIso (joinInclLeft X Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance n),
    fun t ↦ ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, h⟩, x, y⟩, rfl⟩ :=
    (AugmentedSimplexCategory.bijective_map_unit_app _ _ (.of n.unop)).2 t
  cases b with
  | of k => exact isEmptyElim (α := Y.obj (op k)) y
  | star =>
    cases a with
    | star => cases h
    | of k =>
      obtain rfl : k = n.unop := WithInitial.of.inj h
      exact ⟨x, (congrArg _ (Prod.ext rfl (Subsingleton.elim
        (α := (trivialAugmentation.obj Y).obj (op .star)) _ y))).trans
          (Functor.map_id_apply (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)
            (op (WithInitial.of n.unop)) _).symm⟩

private lemma preservesColimitsOfShape_trivialAugmentation (K : Type u) [Category.{u} K]
    [IsConnected K] : PreservesColimitsOfShape K trivialAugmentation.{u} := by
  apply preservesColimitsOfShape_of_evaluation
  rintro ⟨c⟩
  cases c with
  | of k =>
    exact preservesColimitsOfShape_of_natIso (F := (evaluation _ (Type u)).obj (op k))
      (NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ rfl))
  | star =>
    refine ⟨fun {F} ↦ ⟨fun {c} _ ↦ ⟨?_⟩⟩⟩
    let φ : F ⋙ trivialAugmentation ⋙ (evaluation _ (Type u)).obj (op .star) ≅
        Types.constPUnitFunctor.{u} K :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
        ext x
        rfl)
    refine IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv φ _).symm (Types.isColimitPUnitCocone K))
      (Cocone.ext (Iso.refl _) (fun j ↦ ?_))
    ext x
    rfl

private noncomputable def joinRightUnderCompForgetIso (T : SSet.{u}) :
    trivialAugmentation ⋙ DayConvolution.convolutionLeft (trivialAugmentation.obj T) ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj AugmentedSimplexCategory.inclusion.op ≅
        joinRightUnder T ⋙ Under.forget T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
    ((congrArg (Functor.whiskerLeft _) (congrArg (DayConvolution.map _)
      (trivialAugmentation.map_id T).symm)).trans (Category.id_comp _).symm))

private noncomputable def joinLeftUnderCompForgetIso (T : SSet.{u}) :
    trivialAugmentation ⋙ DayConvolution.convolutionRight (trivialAugmentation.obj T) ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj AugmentedSimplexCategory.inclusion.op ≅
        joinLeftUnder T ⋙ Under.forget T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
    ((congrArg (Functor.whiskerLeft _) (congrArg (DayConvolution.map · _)
      (trivialAugmentation.map_id T).symm)).trans (Category.id_comp _).symm))

instance preservesColimitsOfSize_joinRightUnder (T : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (joinRightUnder T) where
  preservesColimitsOfShape {J} _ :=
    have : IsIso ((joinRightUnder T).obj (⊥ : T.Subcomplex)).hom :=
      isIso_joinInclRight_of_isEmpty _ _
    WithInitial.preservesColimitsOfShape_of_isIso_hom (Subcomplex.isInitialBot (X := T)) _
      (fun K _ _ ↦
      have := preservesColimitsOfShape_trivialAugmentation K
      have := (DayConvolution.convolutionLeftAdjunction
        (trivialAugmentation.obj T)).leftAdjoint_preservesColimits
      preservesColimitsOfShape_of_natIso (joinRightUnderCompForgetIso T)) J

instance preservesColimitsOfSize_joinLeftUnder (T : SSet.{u}) :
    PreservesColimitsOfSize.{u, u} (joinLeftUnder T) where
  preservesColimitsOfShape {J} _ :=
    have : IsIso ((joinLeftUnder T).obj (⊥ : T.Subcomplex)).hom :=
      isIso_joinInclLeft_of_isEmpty _ _
    WithInitial.preservesColimitsOfShape_of_isIso_hom (Subcomplex.isInitialBot (X := T)) _
      (fun K _ _ ↦
      have := preservesColimitsOfShape_trivialAugmentation K
      have := (DayConvolution.convolutionRightAdjunction
        (trivialAugmentation.obj T)).leftAdjoint_preservesColimits
      preservesColimitsOfShape_of_natIso (joinLeftUnderCompForgetIso T)) J

noncomputable def coslice (T : SSet.{u}) : Under T ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (uliftYoneda.{u} ⋙ joinLeftUnder T)

noncomputable def slice (T : SSet.{u}) : Under T ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (uliftYoneda.{u} ⋙ joinRightUnder T)

noncomputable def joinLeftUnderAdjunction (T : SSet.{u}) : joinLeftUnder T ⊣ coslice T :=
  have : PreservesColimitsOfSize.{0, u} (joinLeftUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinLeftUnder T)
    (Iso.refl _)
  Presheaf.uliftYonedaAdjunction.{0} (joinLeftUnder T) (Iso.refl _).hom

noncomputable def joinRightUnderAdjunction (T : SSet.{u}) : joinRightUnder T ⊣ slice T :=
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinRightUnder T)
    (Iso.refl _)
  Presheaf.uliftYonedaAdjunction.{0} (joinRightUnder T) (Iso.refl _).hom

noncomputable def sliceπ {T : SSet.{u}} (t : Under T) : (slice T).obj t ⟶ t.right :=
  joinInclLeft _ T ≫ ((joinRightUnderAdjunction T).counit.app t).right

@[reassoc]
theorem slice_map_sliceπ {T : SSet.{u}} {t t' : Under T} (φ : t ⟶ t') :
    (slice T).map φ ≫ sliceπ t' = sliceπ t ≫ φ.right := by
  have h := congrArg CommaMorphism.right ((joinRightUnderAdjunction T).counit.naturality φ)
  simp only [Functor.comp_map, Under.comp_right, Functor.id_map] at h
  exact ((joinInclLeft_comp_joinMap_assoc _ _ _).symm.trans
    (congrArg (joinInclLeft _ T ≫ ·) h)).trans (Category.assoc _ _ _).symm

theorem comp_sliceπ {K T : SSet.{u}} {t : Under T} (ψ : K ⟶ (slice T).obj t) :
    ψ ≫ sliceπ t =
      joinInclLeft K T ≫ (((joinRightUnderAdjunction T).homEquiv _ _).symm ψ).right := by
  rw [Adjunction.homEquiv_counit, Under.comp_right, sliceπ]
  exact (joinInclLeft_comp_joinMap_assoc ψ (𝟙 T) _).symm

theorem isIso_sliceπ_of_isEmpty {T : SSet.{u}} [∀ n, IsEmpty (T.obj n)] (t : Under T) :
    IsIso (sliceπ t) := by
  have : IsIso (joinInclLeft t.right T) := isIso_joinInclLeft_of_isEmpty _ _
  let i : join t.right T ⟶ t.right := inv (joinInclLeft t.right T)
  let s : t.right ⟶ (slice T).obj t := (joinRightUnderAdjunction T).homEquiv _ _
    (Under.homMk i (by ext _ x; exact isEmptyElim x))
  have hs : s ≫ sliceπ t = 𝟙 _ := by
    rw [comp_sliceπ, Equiv.symm_apply_apply]
    exact IsIso.hom_inv_id (joinInclLeft t.right T)
  refine ⟨s, ?_, hs⟩
  have : IsIso (joinInclLeft ((slice T).obj t) T) := isIso_joinInclLeft_of_isEmpty _ _
  apply ((joinRightUnderAdjunction T).homEquiv _ _).symm.injective
  apply Under.UnderMorphism.ext
  refine (cancel_epi (joinInclLeft _ T)).1 (((comp_sliceπ _).symm.trans ?_).trans (comp_sliceπ _))
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

noncomputable def cosliceObjEquiv (T : SSet.{u}) (t : Under T) (n : ℕ) :
    ((coslice T).obj t).obj (op ⦋n⦌) ≃
      {f : join T Δ[n] ⟶ t.right // joinInclLeft T Δ[n] ≫ f = t.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.1 f.2
      left_inv _ := rfl
      right_inv _ := rfl }

noncomputable def sliceObjEquiv (T : SSet.{u}) (t : Under T) (n : ℕ) :
    ((slice T).obj t).obj (op ⦋n⦌) ≃
      {f : join Δ[n] T ⟶ t.right // joinInclRight Δ[n] T ≫ f = t.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.1 f.2
      left_inv _ := rfl
      right_inv _ := rfl }

theorem yonedaEquiv_symm_comp_sliceπ {T : SSet.{u}} {t : Under T} {n : ℕ}
    (σ : ((slice T).obj t) _⦋n⦌) :
    yonedaEquiv.symm σ ≫ sliceπ t = joinInclLeft Δ[n] T ≫ (sliceObjEquiv T t n σ).1 := by
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinRightUnder T)
    (Iso.refl _)
  let g : (joinRightUnder T).obj Δ[n] ⟶ t :=
    Under.homMk (sliceObjEquiv T t n σ).1 (sliceObjEquiv T t n σ).2
  have h : (uliftYonedaEquiv.symm (ULift.up (𝟙 ⦋n⦌)) : Δ[n] ⟶ Δ[n]) = 𝟙 _ :=
    uliftYonedaEquiv.symm_apply_eq.2 rfl
  have h' : yonedaEquiv ((joinRightUnderAdjunction T).homEquiv _ _ g) = σ := by
    refine (Presheaf.uliftYonedaAdjunction_homEquiv_app _ _ g (ULift.up (𝟙 ⦋n⦌))).trans ?_
    rw [h]
    exact congrArg ULift.up ((Category.id_comp _).trans ((congrArg (· ≫ g)
      ((joinRightUnder T).map_id _)).trans (Category.id_comp g)))
  rw [comp_sliceπ, ← (Equiv.eq_symm_apply _).2 h', Equiv.symm_apply_apply]
  rfl

end SSet
