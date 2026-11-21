import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.Join
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Presheaf

open CategoryTheory MonoidalCategory Opposite Limits
open scoped MonoidalCategory.DayConvolution

universe w u

namespace CategoryTheory.WithInitial

variable {C : Type w} [SmallCategory C]

theorem preservesColimitsOfShape_of_isIso_hom {T I : Cᵒᵖ ⥤ Type (max w u)} (hI : IsInitial I)
    (G : (Cᵒᵖ ⥤ Type (max w u)) ⥤ Under T) [IsIso (G.obj I).hom]
    (hG : ∀ (K : Type (max w u)) [Category.{max w u} K] [IsConnected K],
      PreservesColimitsOfShape K (G ⋙ Under.forget T))
    (J : Type (max w u)) [Category.{max w u} J] : PreservesColimitsOfShape J G := by
  have : IsConnected (WithInitial J) := isConnected_of_isInitial _ WithInitial.starInitial
  have := hG (WithInitial J)
  have : PreservesColimitsOfShape J
      (Under.map (G.obj I).hom : Under ((G ⋙ Under.forget T).obj I) ⥤ Under T) :=
    inferInstanceAs (PreservesColimitsOfShape J (Under.map (G.obj I).hom))
  have : PreservesColimitsOfShape J
      (Under.post (X := I) (G ⋙ Under.forget T) ⋙ Under.map (G.obj I).hom) :=
    comp_preservesColimitsOfShape _ _
  have : PreservesColimitsOfShape J ((Under.equivalenceOfIsInitial hI).inverse ⋙
      Under.post (X := I) (G ⋙ Under.forget T) ⋙ Under.map (G.obj I).hom) :=
    comp_preservesColimitsOfShape _ _
  exact preservesColimitsOfShape_of_natIso (F := (Under.equivalenceOfIsInitial hI).inverse ⋙
    Under.post (G ⋙ Under.forget T) ⋙ Under.map (G.obj I).hom)
    (NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _)
      ((Category.comp_id _).trans (Under.w (G.map (hI.to X)))))
      (fun _ ↦ Under.UnderMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))

variable [MonoidalCategory (WithInitial C)]
  [∀ P Q : (WithInitial C)ᵒᵖ ⥤ Type (max w u), DayConvolution P Q] [TensorUnitIsStar C]

noncomputable def joinLeftUnder (T : Cᵒᵖ ⥤ Type (max w u)) :
    (Cᵒᵖ ⥤ Type (max w u)) ⥤ Under T where
  obj X := Under.mk (joinInclLeft T X)
  map f := Under.homMk (joinMap (𝟙 T) f)
    ((joinInclLeft_comp_joinMap (𝟙 T) f).trans (Category.id_comp _))
  map_id X := by ext1; exact joinFunctor.map_id (T, X)
  map_comp f g := by
    ext1
    exact joinFunctor.map_comp (X := (T, _)) (Y := (T, _)) (Z := (T, _)) (𝟙 T, f) (𝟙 T, g)

noncomputable def joinRightUnder (T : Cᵒᵖ ⥤ Type (max w u)) :
    (Cᵒᵖ ⥤ Type (max w u)) ⥤ Under T where
  obj X := Under.mk (joinInclRight X T)
  map f := Under.homMk (joinMap f (𝟙 T))
    ((joinInclRight_comp_joinMap f (𝟙 T)).trans (Category.id_comp _))
  map_id X := by ext1; exact joinFunctor.map_id (X, T)
  map_comp f g := by
    ext1
    exact joinFunctor.map_comp (X := (_, T)) (Y := (_, T)) (Z := (_, T)) (f, 𝟙 T) (g, 𝟙 T)

private noncomputable def joinRightUnderCompForgetIso (T : Cᵒᵖ ⥤ Type (max w u)) :
    trivialAugmentation ⋙ DayConvolution.convolutionLeft (trivialAugmentation.obj T) ⋙
      (Functor.whiskeringLeft _ _ (Type (max w u))).obj (incl.op : Cᵒᵖ ⥤ _) ≅
        joinRightUnder T ⋙ Under.forget T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
    ((congrArg (Functor.whiskerLeft _) (congrArg (DayConvolution.map _)
      (trivialAugmentation.map_id T).symm)).trans (Category.id_comp _).symm))

private noncomputable def joinLeftUnderCompForgetIso (T : Cᵒᵖ ⥤ Type (max w u)) :
    trivialAugmentation ⋙ DayConvolution.convolutionRight (trivialAugmentation.obj T) ⋙
      (Functor.whiskeringLeft _ _ (Type (max w u))).obj (incl.op : Cᵒᵖ ⥤ _) ≅
        joinLeftUnder T ⋙ Under.forget T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans
    ((congrArg (Functor.whiskerLeft _) (congrArg (DayConvolution.map · _)
      (trivialAugmentation.map_id T).symm)).trans (Category.id_comp _).symm))

private def emptyPresheaf : Cᵒᵖ ⥤ Type (max w u) := (Functor.const _).obj PEmpty

private instance (c : Cᵒᵖ) : IsEmpty ((emptyPresheaf.{w, u} (C := C)).obj c) :=
  inferInstanceAs (IsEmpty PEmpty)

private def isInitialEmptyPresheaf : IsInitial (emptyPresheaf.{w, u} (C := C)) :=
  IsInitial.ofUniqueHom
    (fun X ↦ { app _ := TypeCat.ofHom PEmpty.elim, naturality _ _ _ := by ext ⟨⟩ })
    (fun X f ↦ by ext _ ⟨⟩)

instance preservesColimitsOfSize_joinRightUnder (T : Cᵒᵖ ⥤ Type (max w u)) :
    PreservesColimitsOfSize.{max w u, max w u} (joinRightUnder T) where
  preservesColimitsOfShape {J} _ :=
    have : IsIso ((joinRightUnder T).obj emptyPresheaf).hom :=
      isIso_joinInclRight_of_isEmpty _ _
    preservesColimitsOfShape_of_isIso_hom isInitialEmptyPresheaf _ (fun _ _ _ ↦
      have := (DayConvolution.convolutionLeftAdjunction
        (trivialAugmentation.obj T)).leftAdjoint_preservesColimits
      preservesColimitsOfShape_of_natIso (joinRightUnderCompForgetIso T)) J

instance preservesColimitsOfSize_joinLeftUnder (T : Cᵒᵖ ⥤ Type (max w u)) :
    PreservesColimitsOfSize.{max w u, max w u} (joinLeftUnder T) where
  preservesColimitsOfShape {J} _ :=
    have : IsIso ((joinLeftUnder T).obj emptyPresheaf).hom :=
      isIso_joinInclLeft_of_isEmpty _ _
    preservesColimitsOfShape_of_isIso_hom isInitialEmptyPresheaf _ (fun _ _ _ ↦
      have := (DayConvolution.convolutionRightAdjunction
        (trivialAugmentation.obj T)).leftAdjoint_preservesColimits
      preservesColimitsOfShape_of_natIso (joinLeftUnderCompForgetIso T)) J

private noncomputable def joinLeftUnderCompForgetIsoCurry (T : Cᵒᵖ ⥤ Type (max w u)) :
    joinLeftUnder T ⋙ Under.forget T ≅ (Functor.curry.obj joinFunctor).obj T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

private noncomputable def joinRightUnderCompForgetIsoCurry (T : Cᵒᵖ ⥤ Type (max w u)) :
    joinRightUnder T ⋙ Under.forget T ≅ (Functor.curry.obj joinFunctor).flip.obj T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

instance preservesColimitsOfShape_curry_joinFunctor_obj (T : Cᵒᵖ ⥤ Type (max w u))
    (K : Type (max w u)) [Category.{max w u} K] [IsConnected K] :
    PreservesColimitsOfShape K ((Functor.curry.obj joinFunctor).obj T) :=
  preservesColimitsOfShape_of_natIso (joinLeftUnderCompForgetIsoCurry T)

instance preservesColimitsOfShape_curry_joinFunctor_flip_obj (T : Cᵒᵖ ⥤ Type (max w u))
    (K : Type (max w u)) [Category.{max w u} K] [IsConnected K] :
    PreservesColimitsOfShape K ((Functor.curry.obj joinFunctor).flip.obj T) :=
  preservesColimitsOfShape_of_natIso (joinRightUnderCompForgetIsoCurry T)

instance preservesColimitsOfShape_walkingSpan_curry_joinFunctor_obj
    (T : Cᵒᵖ ⥤ Type (max w u)) :
    PreservesColimitsOfShape WalkingSpan ((Functor.curry.obj joinFunctor).obj T) :=
  have : PreservesColimitsOfSize.{0, 0} (joinLeftUnder T) := preservesColimitsOfSize_shrink _
  preservesColimitsOfShape_of_natIso (joinLeftUnderCompForgetIsoCurry T)

instance preservesColimitsOfShape_walkingSpan_curry_joinFunctor_flip_obj
    (T : Cᵒᵖ ⥤ Type (max w u)) :
    PreservesColimitsOfShape WalkingSpan ((Functor.curry.obj joinFunctor).flip.obj T) :=
  have : PreservesColimitsOfSize.{0, 0} (joinRightUnder T) := preservesColimitsOfSize_shrink _
  preservesColimitsOfShape_of_natIso (joinRightUnderCompForgetIsoCurry T)

noncomputable def coslice (T : Cᵒᵖ ⥤ Type (max w u)) : Under T ⥤ (Cᵒᵖ ⥤ Type (max w u)) :=
  Presheaf.restrictedULiftYoneda.{w} (uliftYoneda.{max w u} ⋙ joinLeftUnder T)

noncomputable def slice (T : Cᵒᵖ ⥤ Type (max w u)) : Under T ⥤ (Cᵒᵖ ⥤ Type (max w u)) :=
  Presheaf.restrictedULiftYoneda.{w} (uliftYoneda.{max w u} ⋙ joinRightUnder T)

noncomputable def joinLeftUnderAdjunction (T : Cᵒᵖ ⥤ Type (max w u)) :
    joinLeftUnder T ⊣ coslice T :=
  have : PreservesColimitsOfSize.{w, max w u} (joinLeftUnder T) :=
    preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0} (joinLeftUnder T) (Iso.refl _)
  Presheaf.uliftYonedaAdjunction.{0} (joinLeftUnder T) (Iso.refl _).hom

noncomputable def joinRightUnderAdjunction (T : Cᵒᵖ ⥤ Type (max w u)) :
    joinRightUnder T ⊣ slice T :=
  have : PreservesColimitsOfSize.{w, max w u} (joinRightUnder T) :=
    preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0} (joinRightUnder T) (Iso.refl _)
  Presheaf.uliftYonedaAdjunction.{0} (joinRightUnder T) (Iso.refl _).hom

noncomputable def cosliceObjEquiv (T : Cᵒᵖ ⥤ Type (max w u)) (t : Under T) (c : C) :
    ((coslice T).obj t).obj (op c) ≃
      {f : join T (uliftYoneda.{max w u}.obj c) ⟶ t.right //
        joinInclLeft T (uliftYoneda.{max w u}.obj c) ≫ f = t.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.1 f.2
      left_inv _ := rfl
      right_inv _ := rfl }

noncomputable def sliceObjEquiv (T : Cᵒᵖ ⥤ Type (max w u)) (t : Under T) (c : C) :
    ((slice T).obj t).obj (op c) ≃
      {f : join (uliftYoneda.{max w u}.obj c) T ⟶ t.right //
        joinInclRight (uliftYoneda.{max w u}.obj c) T ≫ f = t.hom} :=
  Equiv.ulift.trans
    { toFun f := ⟨f.right, Under.w f⟩
      invFun f := Under.homMk f.1 f.2
      left_inv _ := rfl
      right_inv _ := rfl }

end CategoryTheory.WithInitial
