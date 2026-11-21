import Atoms.Diagrammatic.Joyal.GrayTensorCartesian
import Atoms.ForMathlib.CategoryTheory.Adjunction.Mates

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

noncomputable abbrev faceNerveRight : MarkedSSet.{u} ⥤ DiagSet.{u} :=
  (MarkedPresheaf.nerve markedFaceNerveSite (fun x => epi_markedFaceNerveSite_map_toSelf x) ⋙
    MarkedDiagSet.toCoinductive 1) ⋙ DiagSet.Infty.forget 1

theorem isInftyCategory_faceNerveRight_obj (C : MarkedSSet.{u}) [IsFibrant C] :
    IsInftyCategory 1 (faceNerveRight.obj C) :=
  (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj C)

section Conjugate

variable (X : DiagSet.{u}) {T H : DiagSet.{u} ⥤ DiagSet.{u}} (adj : T ⊣ H)
  (e : T ⋙ faceNerve ≅ faceNerve ⋙ MonoidalCategory.tensorLeft (faceNerve.obj X))

private noncomputable def faceNerveConjugateIso :
    ihom (faceNerve.obj X) ⋙ faceNerveRight ≅ faceNerveRight ⋙ H :=
  conjugateIsoEquiv ((faceNerveAdjunction.{u} : faceNerve ⊣ faceNerveRight).comp
      (ihom.adjunction (faceNerve.obj X)))
    (adj.comp (faceNerveAdjunction.{u} : faceNerve ⊣ faceNerveRight)) e

private noncomputable def faceNerveConjugateComparison (Y : DiagSet.{u}) :
    faceNerve.obj (H.obj Y) ⟶ (ihom (faceNerve.obj X)).obj (faceNerve.obj Y) :=
  (ihom.adjunction (faceNerve.obj X)).homEquiv _ _
    (e.inv.app (H.obj Y) ≫ faceNerve.map (adj.counit.app Y))

private theorem homEquiv_faceNerveConjugateComparison_comp (Y : DiagSet.{u}) {W : MarkedSSet.{u}}
    (j : faceNerve.obj Y ⟶ W) :
    faceNerveAdjunction.homEquiv _ _
        (faceNerveConjugateComparison X adj e Y ≫ (ihom (faceNerve.obj X)).map j) =
      H.map (faceNerveAdjunction.homEquiv _ _ j) ≫ (faceNerveConjugateIso X adj e).inv.app W := by
  let adjF : faceNerve.{u} ⊣ faceNerveRight := faceNerveAdjunction
  let adj₁ := adjF.comp (ihom.adjunction (faceNerve.obj X))
  let adj₂ := adj.comp adjF
  have hc (f : faceNerve.obj (T.obj (H.obj Y)) ⟶ W) :
      adj₁.homEquiv _ W (e.inv.app _ ≫ f) =
        adj₂.homEquiv _ W f ≫ (conjugateEquiv adj₂ adj₁ e.inv).app W := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
      (conjugateEquiv adj₂ adj₁ e.inv).naturality, ← Category.assoc, unit_conjugateEquiv,
      Category.assoc, Functor.map_comp]
  have h := hc (faceNerve.map (adj.counit.app Y) ≫ j)
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv] at h
  simp only [Equiv.trans_apply] at h
  have hε : adj.homEquiv (H.obj Y) Y (adj.counit.app Y) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  rw [← Category.assoc (e.inv.app _),
    (ihom.adjunction (faceNerve.obj X)).homEquiv_naturality_right, adjF.homEquiv_naturality_left,
    adj.homEquiv_naturality_right] at h
  dsimp only [Functor.id_obj] at h
  rw [hε, Category.id_comp] at h
  exact h

private theorem weakEquivalence_faceNerveConjugateComparison_comp
    (hH : ∀ {Y Y' : DiagSet.{u}} (g : Y ⟶ Y'), IsInftyCategory 1 Y → IsInftyCategory 1 Y' →
      WeakEquivalence ((DiagSet.toInfty 1).map g) →
        WeakEquivalence ((DiagSet.toInfty 1).map (H.map g)))
    {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) {W : MarkedSSet.{u}} [IsFibrant W]
    (j : faceNerve.obj Y ⟶ W) [WeakEquivalence j] :
    WeakEquivalence (faceNerveConjugateComparison X adj e Y ≫ (ihom (faceNerve.obj X)).map j) := by
  have hQ := isQuillenEquivalence_faceNerveAdjunction.{u}
  have hj : WeakEquivalence ((DiagSet.toInfty 1).map (faceNerveAdjunction.homEquiv Y W j)) :=
    (hQ.weakEquivalence_iff (A := (DiagSet.toInfty 1).obj Y) j).1 ‹_›
  have hRW : IsInftyCategory 1 (faceNerveRight.obj W) :=
    (isFibrant_infty_iff 1 _).1 (isQuillen_faceNerveAdjunction.isFibrant_obj W)
  have := hH _ hY hRW hj
  have hW : WeakEquivalence ((DiagSet.toInfty 1).map (H.map (faceNerveAdjunction.homEquiv Y W j) ≫
      (faceNerveConjugateIso X adj e).inv.app W)) := by
    rw [Functor.map_comp]
    infer_instance
  have := (MarkedSSet.isQuillen_ihomAdjunction (faceNerve.obj X)).isFibrant_obj W
  have : IsCofibrant (C := DiagSet.Infty.{u} 1) (H.obj Y) := DiagSet.Infty.isCofibrant 1 _
  refine (hQ.weakEquivalence_iff (A := H.obj Y) (X := (ihom (faceNerve.obj X)).obj W)
    (faceNerveConjugateComparison X adj e Y ≫ (ihom (faceNerve.obj X)).map j)).2 ?_
  rw [homEquiv_faceNerveConjugateComparison_comp]
  exact hW

end Conjugate

private noncomputable def faceNerveGrayTensorRightIso (X : DiagSet.{u}) :
    grayTensorRight X ⋙ faceNerve ≅ faceNerve ⋙ MonoidalCategory.tensorLeft (faceNerve.obj X) :=
  faceNerveGrayTensorEvalIso X ≪≫ faceNerveProdRightIso X ≪≫
    Functor.isoWhiskerLeft faceNerve (CartesianMonoidalCategory.tensorLeftIsoProd _).symm

noncomputable def grayHomRightFaceNerveIso (X : DiagSet.{u}) :
    ihom (faceNerve.obj X) ⋙ faceNerveRight ≅ faceNerveRight ⋙ grayHomRight X :=
  faceNerveConjugateIso X (grayTensorRightAdjunction X) (faceNerveGrayTensorRightIso X)

private theorem faceNerveGrayTensorRightIso_hom_app (X T : DiagSet.{u}) :
    (faceNerveGrayTensorRightIso X).hom.app T =
      CartesianMonoidalCategory.lift (faceNerve.map (grayTensorSnd T X))
        (faceNerve.map (grayTensorFst T X)) := by
  have h : (faceNerveGrayTensorEvalIso X).hom.app T = faceNerveGrayTensorIso.hom.app (T, X) := by
    simp only [faceNerveGrayTensorIso, faceNerveGrayTensorCurryIso, Iso.trans_hom, eqToIso.hom,
      NatTrans.comp_app, eqToHom_app, Functor.mapIso_hom, Functor.uncurry_map_app,
      NatIso.ofComponents_hom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have e : (faceNerveGrayTensorRightIso X).hom.app T =
      prod.lift (faceNerve.map (grayTensorFst T X)) (faceNerve.map (grayTensorSnd T X)) ≫
        (prod.braiding (faceNerve.obj T) (faceNerve.obj X)).hom ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd (faceNerve.obj X)).inv.app
            (faceNerve.obj T) :=
    congrArg (· ≫ _) (h.trans (faceNerveGrayTensorIso_hom_app T X))
  have hfst : (prod.braiding (faceNerve.obj T) (faceNerve.obj X)).hom ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd (faceNerve.obj X)).inv.app (faceNerve.obj T) ≫
        CartesianMonoidalCategory.fst _ _ = prod.snd :=
    (congrArg (_ ≫ ·) (IsLimit.conePointUniqueUpToIso_inv_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct (faceNerve.obj X) (faceNerve.obj T))
      (limit.isLimit _) (Discrete.mk WalkingPair.left))).trans (prod.lift_fst _ _)
  have hsnd : (prod.braiding (faceNerve.obj T) (faceNerve.obj X)).hom ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd (faceNerve.obj X)).inv.app (faceNerve.obj T) ≫
        CartesianMonoidalCategory.snd _ _ = prod.fst :=
    (congrArg (_ ≫ ·) (IsLimit.conePointUniqueUpToIso_inv_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct (faceNerve.obj X) (faceNerve.obj T))
      (limit.isLimit _) (Discrete.mk WalkingPair.right))).trans (prod.lift_snd _ _)
  rw [e]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (prod.lift _ _ ≫ ·)
      ((Category.assoc _ _ _).trans hfst)).trans ((prod.lift_snd _ _).trans
        (CartesianMonoidalCategory.lift_fst _ _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (prod.lift _ _ ≫ ·)
      ((Category.assoc _ _ _).trans hsnd)).trans ((prod.lift_fst _ _).trans
        (CartesianMonoidalCategory.lift_snd _ _).symm))

theorem homEquiv_curry_comp_grayHomRightFaceNerveIso_hom_app (X : DiagSet.{u}) {T : DiagSet.{u}}
    {W : MarkedSSet.{u}} (g : faceNerve.obj X ⊗ faceNerve.obj T ⟶ W) :
    faceNerveAdjunction.homEquiv T _ (MonoidalClosed.curry g) ≫
        (grayHomRightFaceNerveIso X).hom.app W =
      (grayTensorRightAdjunction X).homEquiv T _ (faceNerveAdjunction.homEquiv _ W
        (CartesianMonoidalCategory.lift (faceNerve.map (grayTensorSnd T X))
          (faceNerve.map (grayTensorFst T X)) ≫ g)) := by
  let adjF : faceNerve.{u} ⊣ faceNerveRight := faceNerveAdjunction
  have h := homEquiv_conjugateEquiv_app (adjF.comp (ihom.adjunction (faceNerve.obj X)))
    ((grayTensorRightAdjunction X).comp adjF) (faceNerveGrayTensorRightIso X).hom (c := T) g
  rw [faceNerveGrayTensorRightIso_hom_app] at h
  exact h.symm

theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayHomRight_map (X : DiagSet.{u})
    {Y Y' : DiagSet.{u}} (hY : IsInftyCategory 1 Y) (hY' : IsInftyCategory 1 Y') (g : Y ⟶ Y')
    [WeakEquivalence ((DiagSet.toInfty 1).map g)] :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRight X).map g)) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant ((DiagSet.toInfty 1).obj Y') := (isFibrant_infty_iff 1 _).2 hY'
  (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one X).weakEquivalence_map_of_isFibrant
    ((DiagSet.toInfty 1).map g)

noncomputable def faceNerveGrayHomComparison (X Y : DiagSet.{u}) :
    faceNerve.obj ((grayHomRight X).obj Y) ⟶ (ihom (faceNerve.obj X)).obj (faceNerve.obj Y) :=
  faceNerveConjugateComparison X (grayTensorRightAdjunction X) (faceNerveGrayTensorRightIso X) Y

theorem faceNerveAdjunction_homEquiv_faceNerveGrayHomComparison_comp (X Y : DiagSet.{u})
    {W : MarkedSSet.{u}} (j : faceNerve.obj Y ⟶ W) :
    faceNerveAdjunction.homEquiv _ _
        (faceNerveGrayHomComparison X Y ≫ (ihom (faceNerve.obj X)).map j) =
      (grayHomRight X).map (faceNerveAdjunction.homEquiv _ _ j) ≫
        (grayHomRightFaceNerveIso X).inv.app W :=
  homEquiv_faceNerveConjugateComparison_comp X _ _ Y j

theorem weakEquivalence_faceNerveGrayHomComparison (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) {W : MarkedSSet.{u}} [IsFibrant W] (j : faceNerve.obj Y ⟶ W)
    [WeakEquivalence j] :
    WeakEquivalence (faceNerveGrayHomComparison X Y ≫ (ihom (faceNerve.obj X)).map j) :=
  weakEquivalence_faceNerveConjugateComparison_comp X _ _
    (fun g hY hY' _ => DiagSet.Infty.weakEquivalence_toInfty_one_grayHomRight_map X hY hY' g) hY j

theorem weakEquivalence_faceNerve_functorCategory (pseudo : Bool) (X : DiagSet.{u})
    {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) {W : MarkedSSet.{u}} [IsFibrant W]
    (j : faceNerve.obj Y ⟶ W) [WeakEquivalence j] :
    ∃ e : faceNerve.obj (functorCategory pseudo X Y) ≅ faceNerve.obj ((grayHomRight X).obj Y),
      WeakEquivalence
        (e.hom ≫ faceNerveGrayHomComparison X Y ≫ (ihom (faceNerve.obj X)).map j) := by
  have := weakEquivalence_faceNerveGrayHomComparison X hY j
  have he : Nonempty (functorCategory pseudo X Y ≅ (grayHomRight X).obj Y) := by
    cases pseudo
    · exact ⟨functorCategoryGrayIso X Y⟩
    · have := isIso_functorCategoryPseudoToGray X hY
      exact ⟨asIso (functorCategoryPseudoToGray X Y) ≪≫ functorCategoryGrayIso X Y⟩
  obtain ⟨e⟩ := he
  exact ⟨faceNerve.mapIso e, inferInstance⟩

private noncomputable def faceNerveGrayTensorLeftIso (X : DiagSet.{u}) :
    grayTensorLeft X ⋙ faceNerve ≅ faceNerve ⋙ MonoidalCategory.tensorLeft (faceNerve.obj X) :=
  faceNerveGrayTensorCurryIso.app X ≪≫ faceNerveProdLeftIso X ≪≫
    Functor.isoWhiskerLeft faceNerve (CartesianMonoidalCategory.tensorLeftIsoProd _).symm

noncomputable def grayHomLeftFaceNerveIso (X : DiagSet.{u}) :
    ihom (faceNerve.obj X) ⋙ faceNerveRight ≅ faceNerveRight ⋙ grayHomLeft X :=
  faceNerveConjugateIso X (grayTensorLeftAdjunction X) (faceNerveGrayTensorLeftIso X)

theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayHomLeft_map (X : DiagSet.{u})
    {Y Y' : DiagSet.{u}} (hY : IsInftyCategory 1 Y) (hY' : IsInftyCategory 1 Y') (g : Y ⟶ Y')
    [WeakEquivalence ((DiagSet.toInfty 1).map g)] :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomLeft X).map g)) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant ((DiagSet.toInfty 1).obj Y') := (isFibrant_infty_iff 1 _).2 hY'
  (DiagSet.Infty.isQuillen_grayTensorLeftAdjunction_one X).weakEquivalence_map_of_isFibrant
    ((DiagSet.toInfty 1).map g)

noncomputable def faceNerveGrayHomLeftComparison (X Y : DiagSet.{u}) :
    faceNerve.obj ((grayHomLeft X).obj Y) ⟶ (ihom (faceNerve.obj X)).obj (faceNerve.obj Y) :=
  faceNerveConjugateComparison X (grayTensorLeftAdjunction X) (faceNerveGrayTensorLeftIso X) Y

theorem faceNerveAdjunction_homEquiv_faceNerveGrayHomLeftComparison_comp (X Y : DiagSet.{u})
    {W : MarkedSSet.{u}} (j : faceNerve.obj Y ⟶ W) :
    faceNerveAdjunction.homEquiv _ _
        (faceNerveGrayHomLeftComparison X Y ≫ (ihom (faceNerve.obj X)).map j) =
      (grayHomLeft X).map (faceNerveAdjunction.homEquiv _ _ j) ≫
        (grayHomLeftFaceNerveIso X).inv.app W :=
  homEquiv_faceNerveConjugateComparison_comp X _ _ Y j

theorem weakEquivalence_faceNerveGrayHomLeftComparison (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) {W : MarkedSSet.{u}} [IsFibrant W] (j : faceNerve.obj Y ⟶ W)
    [WeakEquivalence j] :
    WeakEquivalence (faceNerveGrayHomLeftComparison X Y ≫ (ihom (faceNerve.obj X)).map j) :=
  weakEquivalence_faceNerveConjugateComparison_comp X _ _
    (fun g hY hY' _ => DiagSet.Infty.weakEquivalence_toInfty_one_grayHomLeft_map X hY hY' g) hY j

end Atoms.Diagrammatic
