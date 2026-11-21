import Atoms.Diagrammatic.Joyal.GrayTensorModel
import Atoms.Diagrammatic.Joyal.MarkedGrayTensorModel
import Atoms.Diagrammatic.Marked.CylinderTensor
import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.PathObject
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.FunctorialCylinder

open CategoryTheory Limits Opposite HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

private theorem weakEquivalence_toCoinductive_isIso_comp {n : ℕ∞} {A B C : MarkedDiagSet.{u}}
    (e : A ⟶ B) [IsIso e] (g : B ⟶ C)
    (hg : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map g)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (e ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

private theorem weakEquivalence_toCoinductive_comp_isIso {n : ℕ∞} {A B C : MarkedDiagSet.{u}}
    (g : A ⟶ B) (e : B ⟶ C) [IsIso e]
    (hg : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map g)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (g ≫ e)) := by
  rw [Functor.map_comp]
  infer_instance

private theorem weakEquivalence_toCoinductive_one_tensorLeft_map_of_mono
    (Z : MarkedDiagSet.{u}) {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y') [Mono f]
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map ((tensorLeft false Z).map f)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
    (initial.to Z) f
  have : IsIso ((tensorLeft false (⊥_ MarkedDiagSet.{u})).map f) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorRight false Y) _)
      (initialIsInitial.isInitialObj (tensorRight false Y') _) _
  have : IsIso sq.inl := sq.isPushout.isIso_inl_of_isIso this
  have h : (tensorLeft false Z).map f = sq.inl ≫ sq.ι := sq.inl_ι.symm
  rw [h]
  exact weakEquivalence_toCoinductive_isIso_comp _ _
    (MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_pushoutProduct (initial.to Z) f
      (Or.inr hf))

private theorem weakEquivalence_toCoinductive_one_tensorRight_map_of_mono
    (Z : MarkedDiagSet.{u}) {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y') [Mono f]
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map ((tensorRight false Z).map f)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
    f (initial.to Z)
  have : IsIso ((tensorRight false (⊥_ MarkedDiagSet.{u})).map f) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorLeft false Y) _)
      (initialIsInitial.isInitialObj (tensorLeft false Y') _) _
  have : IsIso sq.inr := sq.isPushout.isIso_inr_of_isIso this
  have h : (tensorRight false Z).map f = sq.inr ≫ sq.ι := sq.inr_ι.symm
  rw [h]
  exact weakEquivalence_toCoinductive_isIso_comp _ _
    (MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_pushoutProduct f (initial.to Z)
      (Or.inl hf))

private theorem weakEquivalence_isIso_comp {n : ℕ∞} {A B C : DiagSet.{u}} (e : A ⟶ B) [IsIso e]
    (g : B ⟶ C) (hg : WeakEquivalence ((DiagSet.toInfty n).map g)) :
    WeakEquivalence ((DiagSet.toInfty n).map (e ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

private theorem weakEquivalence_toCoinductive_one_map_of_mono
    (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    (hF : ∀ {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y') [Mono f],
      WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f) →
        WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map (F.map f)))
    {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y')
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map (F.map f)) := by
  have (W : MarkedDiagSet.Coinductive.{u} 1) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    let W' : MarkedDiagSet.{u} := W
    exact MorphismProperty.monomorphisms.infer_property (initial.to W')
  let F' : MarkedDiagSet.Coinductive.{u} 1 ⥤ MarkedDiagSet.Coinductive.{u} 1 := F
  rw [weakEquivalence_iff]
  exact F'.map_mem_of_cofibrant (weakEquivalences _) (fun A B i _ _ hi hw => by
      have : @Mono MarkedDiagSet.{u} _ A B i := (cofibration_iff i).1 hi
      exact (weakEquivalence_iff _).1 (hF i hw)) ((MarkedDiagSet.toCoinductive 1).map f)

theorem MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_tensorLeft_map
    (Z : MarkedDiagSet.{u}) {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y')
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map ((tensorLeft false Z).map f)) :=
  weakEquivalence_toCoinductive_one_map_of_mono _
    (weakEquivalence_toCoinductive_one_tensorLeft_map_of_mono Z) f hf

theorem MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_tensorRight_map
    (Z : MarkedDiagSet.{u}) {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y')
    (hf : WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map f)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive 1).map ((tensorRight false Z).map f)) :=
  weakEquivalence_toCoinductive_one_map_of_mono _
    (weakEquivalence_toCoinductive_one_tensorRight_map_of_mono Z) f hf

private theorem uliftYoneda_map_atomGlobeVertex_app_ne (U : Atomᵒᵖ)
    (t t' : (ball.{u} atomPoint).obj U) :
    (uliftYoneda.{u}.map (atomGlobeVertex false)).app U t ≠
      (uliftYoneda.{u}.map (atomGlobeVertex true)).app U t' := by
  intro h
  have h' := congrArg (fun c : ULift (U.unop ⟶ atomGlobe 1) =>
    (FiniteOGP.ofOGPIso (globe 1)).inv (c.down U.unop.top)) h
  simp only [uliftYoneda_map_app, TypeCat.ofHom_apply, ConcreteCategory.comp_apply,
    atomGlobeVertex_apply, Iso.hom_inv_id_apply] at h'
  exact Bool.false_ne_true (SuspCarrier.pole.inj h')

private instance mono_coprodDesc_uliftYoneda_map_atomGlobeVertex :
    Mono (coprod.desc (uliftYoneda.{u}.map (atomGlobeVertex false))
      (uliftYoneda.{u}.map (atomGlobeVertex true))) :=
  have := isTerminalBallAtomPoint.{u}.mono_from (uliftYoneda.{u}.map (atomGlobeVertex false))
  have := isTerminalBallAtomPoint.{u}.mono_from (uliftYoneda.{u}.map (atomGlobeVertex true))
  FunctorToTypes.mono_coprodDesc_of_disjoint _ _ fun U =>
    Set.disjoint_range_iff.2 (uliftYoneda_map_atomGlobeVertex_app_ne U)

private noncomputable abbrev unitUnderlyingIso :
    MarkedPresheaf.forget.{u, 0} (D := atomMarking).obj markedTensorUnit.{u} ≅
      ball.{u} atomPoint :=
  Iso.refl _

private noncomputable abbrev globeUnderlyingIso :
    ball.{u} (atomGlobe 1) ≅ MarkedPresheaf.forget.{u, 0} (D := atomMarking).obj
      markedInterval.{u} :=
  ballIsoForgetYoneda (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)

private instance mono_coprodDesc_markedIntervalVertex :
    Mono (coprod.desc (markedIntervalVertex.{u} false) (markedIntervalVertex.{u} true)) := by
  refine (MarkedPresheaf.mono_iff _).2 ?_
  have h : (MarkedPresheaf.forget.{u, 0} (D := atomMarking)).map
      (coprod.desc (markedIntervalVertex.{u} false) (markedIntervalVertex.{u} true)) =
      inv (coprodComparison (MarkedPresheaf.forget.{u, 0} (D := atomMarking)) markedTensorUnit.{u}
        markedTensorUnit.{u}) ≫ coprod.map unitUnderlyingIso.hom unitUnderlyingIso.hom ≫
          coprod.desc (uliftYoneda.{u}.map (atomGlobeVertex false))
            (uliftYoneda.{u}.map (atomGlobeVertex true)) ≫
          globeUnderlyingIso.hom := by
    rw [IsIso.eq_inv_comp]
    ext1
    · rw [coprodComparison_inl_assoc, ← Functor.map_comp, coprod.inl_desc, coprod.inl_map_assoc,
        coprod.inl_desc_assoc]
      exact (MarkedPresheaf.forget_map_homMk _ _).trans (Category.id_comp _).symm
    · rw [coprodComparison_inr_assoc, ← Functor.map_comp, coprod.inr_desc, coprod.inr_map_assoc,
        coprod.inr_desc_assoc]
      exact (MarkedPresheaf.forget_map_homMk _ _).trans (Category.id_comp _).symm
  rw [h]
  infer_instance

private theorem preservesColimit_tensorRight_pair (X : MarkedDiagSet.{u}) :
    PreservesColimit (pair markedTensorUnit.{u} markedTensorUnit.{u}) (tensorRight false X) :=
  inferInstance

private noncomputable def markedTensorLeftUnitorNatIso :
    tensorLeft false markedTensorUnit.{u} ≅ 𝟭 MarkedDiagSet.{u} :=
  NatIso.ofComponents (markedTensorLeftUnitor false) (markedTensorLeftUnitor_naturality false)

private theorem markedTensorMap_from_comp_leftUnitor_hom (Y X : MarkedDiagSet.{u}) :
    markedTensorMap false (isTerminalMarkedTensorUnit.from Y) (𝟙 X) ≫
      (markedTensorLeftUnitor false X).hom = markedTensorSnd false Y X :=
  MarkedPresheaf.hom_ext rfl

private theorem weakEquivalence_toCoinductive_markedTensorSnd (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      (markedTensorSnd false markedInterval X)) := by
  have hw : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      (markedExactCylinder.contraction.app X)) :=
    (weakEquivalence_iff _).2 (ExactCylinder.weakEquivalences_contraction_app markedExactCylinder
      (coinductiveGenerators n) (coinductiveGenerators_le_monomorphisms n) X)
  have := weakEquivalence_toCoinductive_isIso_comp (n := n)
    ((markedCylinderIsoTensorLeft.{u} false).inv.app X) _ hw
  rwa [markedCylinderIsoTensorLeft_inv_app_comp_contraction_app] at this

noncomputable def MarkedDiagSet.Coinductive.leftMarkedCylinder (n : ℕ∞) :
    FunctorialCylinder (MarkedDiagSet.Coinductive.{u} n) :=
  FunctorialCylinder.ofInterval (C := MarkedDiagSet.Coinductive.{u} n)
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) isTerminalMarkedTensorUnit
    markedTensorLeftUnitorNatIso (J := markedInterval) (markedIntervalVertex false)
    (markedIntervalVertex true) (fun X => preservesColimit_tensorRight_pair X)
    (fun (X : MarkedDiagSet.{u}) => by
      have h := weakEquivalence_toCoinductive_comp_isIso _ (markedTensorLeftUnitor false X).inv
        (weakEquivalence_toCoinductive_markedTensorSnd n X)
      rw [← markedTensorMap_from_comp_leftUnitor_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] at h
      exact h)
    (fun (X : MarkedDiagSet.{u}) => (cofibration_iff _).2 (mono_markedTensorMap false
      (coprod.desc (markedIntervalVertex false) (markedIntervalVertex true)) (𝟙 X)))

theorem MarkedDiagSet.Coinductive.leftMarkedCylinder_I_obj (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    (leftMarkedCylinder n).I.obj X = markedTensor false markedInterval X := rfl

theorem MarkedDiagSet.Coinductive.leftMarkedCylinder_i₀_app (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    (leftMarkedCylinder n).i₀.app X =
      (markedTensorLeftUnitor false X).inv ≫
        markedTensorMap false (markedIntervalVertex false) (𝟙 X) := rfl

theorem MarkedDiagSet.Coinductive.leftMarkedCylinder_i₁_app (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    (leftMarkedCylinder n).i₁.app X =
      (markedTensorLeftUnitor false X).inv ≫
        markedTensorMap false (markedIntervalVertex true) (𝟙 X) := rfl

theorem MarkedDiagSet.Coinductive.leftMarkedCylinder_π_app (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    (leftMarkedCylinder n).π.app X = markedTensorSnd false markedInterval X :=
  markedTensorMap_from_comp_leftUnitor_hom _ X

private theorem preservesColimit_tensorLeft_pair (X : MarkedDiagSet.{u}) :
    PreservesColimit (pair markedTensorUnit.{u} markedTensorUnit.{u}) (tensorLeft false X) :=
  inferInstance

private noncomputable def markedTensorRightUnitorNatIso :
    tensorRight false markedTensorUnit.{u} ≅ 𝟭 MarkedDiagSet.{u} :=
  NatIso.ofComponents (markedTensorRightUnitor false) (markedTensorRightUnitor_naturality false)

private theorem markedTensorMap_from_comp_rightUnitor_hom (X Y : MarkedDiagSet.{u}) :
    markedTensorMap false (𝟙 X) (isTerminalMarkedTensorUnit.from Y) ≫
      (markedTensorRightUnitor false X).hom = markedTensorFst false X Y :=
  MarkedPresheaf.hom_ext rfl

private theorem weakEquivalence_toCoinductive_markedInterval_from (n : ℕ∞) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      (isTerminalMarkedTensorUnit.from markedInterval.{u})) := by
  have h := weakEquivalence_toCoinductive_isIso_comp (n := n)
    (markedTensorRightUnitor false markedInterval.{u}).inv _
    (weakEquivalence_toCoinductive_markedTensorSnd n markedTensorUnit.{u})
  rwa [isTerminalMarkedTensorUnit.hom_ext ((markedTensorRightUnitor false markedInterval.{u}).inv ≫
    markedTensorSnd false markedInterval.{u} markedTensorUnit.{u})
    (isTerminalMarkedTensorUnit.from markedInterval.{u})] at h

noncomputable def MarkedDiagSet.Coinductive.rightMarkedCylinderOne :
    FunctorialCylinder (MarkedDiagSet.Coinductive.{u} 1) :=
  FunctorialCylinder.ofInterval (C := MarkedDiagSet.Coinductive.{u} 1)
    (Functor.curry.obj (markedTensorBifunctor.{u} false)).flip isTerminalMarkedTensorUnit
    markedTensorRightUnitorNatIso (J := markedInterval) (markedIntervalVertex false)
    (markedIntervalVertex true) (fun X => preservesColimit_tensorLeft_pair X)
    (fun (X : MarkedDiagSet.{u}) =>
      MarkedDiagSet.Coinductive.weakEquivalence_toCoinductive_one_tensorLeft_map X _
        (weakEquivalence_toCoinductive_markedInterval_from 1))
    (fun (X : MarkedDiagSet.{u}) => (cofibration_iff _).2 (mono_markedTensorMap false (𝟙 X)
      (coprod.desc (markedIntervalVertex false) (markedIntervalVertex true))))

theorem MarkedDiagSet.Coinductive.rightMarkedCylinderOne_I_obj (X : MarkedDiagSet.{u}) :
    rightMarkedCylinderOne.I.obj X = markedTensor false X markedInterval := rfl

theorem MarkedDiagSet.Coinductive.rightMarkedCylinderOne_i₀_app (X : MarkedDiagSet.{u}) :
    rightMarkedCylinderOne.i₀.app X =
      (markedTensorRightUnitor false X).inv ≫
        markedTensorMap false (𝟙 X) (markedIntervalVertex false) := rfl

theorem MarkedDiagSet.Coinductive.rightMarkedCylinderOne_i₁_app (X : MarkedDiagSet.{u}) :
    rightMarkedCylinderOne.i₁.app X =
      (markedTensorRightUnitor false X).inv ≫
        markedTensorMap false (𝟙 X) (markedIntervalVertex true) := rfl

theorem MarkedDiagSet.Coinductive.rightMarkedCylinderOne_π_app (X : MarkedDiagSet.{u}) :
    rightMarkedCylinderOne.π.app X = markedTensorFst false X markedInterval :=
  markedTensorMap_from_comp_rightUnitor_hom X _

noncomputable def reversibleArrowVertex (ε : Bool) : ball.{u} atomPoint ⟶ reversibleArrow.{u} :=
  uliftYoneda.map (atomGlobeVertex ε) ≫ toWalkingEquivalence (atomGlobe 1) _

instance mono_coprodDesc_reversibleArrowVertex :
    Mono (coprod.desc (reversibleArrowVertex.{u} false) (reversibleArrowVertex.{u} true)) := by
  have h : coprod.desc (reversibleArrowVertex.{u} false) (reversibleArrowVertex.{u} true) =
      coprod.desc (uliftYoneda.{u}.map (atomGlobeVertex false))
        (uliftYoneda.{u}.map (atomGlobeVertex true)) ≫
        toWalkingEquivalence (atomGlobe 1) ((dimension_atomGlobe 1).symm ▸ Nat.one_pos) := by
    ext1 <;> simp [reversibleArrowVertex] <;> rfl
  rw [h]
  have : Mono (toWalkingEquivalence.{u} (atomGlobe 1)
      ((dimension_atomGlobe 1).symm ▸ Nat.one_pos)) :=
    inferInstanceAs (Mono (topInversionData _ _).toLocalization)
  exact @mono_comp _ _ _ _ _ _ inferInstance _ this

private noncomputable def reversibleCylinderPointIso :
    reversibleCylinder.{u}.I.obj (ball.{u} atomPoint) ≅ reversibleArrow.{u} :=
  Loc.mapIso ((markedCylinderIsoTensorLeft.{u} false).app markedTensorUnit ≪≫
    markedTensorRightUnitor false markedInterval.{u} ≪≫
    (markedAtomIsoYoneda (atomGlobe 1) markable_atomGlobe_one).symm) ≪≫
    locMarkedAtomIso (atomGlobe 1) markable_atomGlobe_one

theorem DiagSet.Infty.weakEquivalence_toInfty_reversibleArrow_from (n : ℕ∞) :
    WeakEquivalence ((DiagSet.toInfty n).map
      (isTerminalBallAtomPoint.from reversibleArrow.{u})) := by
  have hw : WeakEquivalence ((DiagSet.toInfty n).map
      (reversibleCylinder.{u}.contraction.app (ball.{u} atomPoint))) :=
    (weakEquivalence_iff _).2 (reversibleCylinder.contraction_mem_weakEquivalences
      (inftyGenerators n) (inftyGenerators_le_monomorphisms n) _)
  have := reversibleCylinderPointIso.{u}.inv
  have h := weakEquivalence_isIso_comp (n := n) reversibleCylinderPointIso.{u}.inv _ hw
  rwa [isTerminalBallAtomPoint.hom_ext (reversibleCylinderPointIso.{u}.inv ≫
    reversibleCylinder.{u}.contraction.app (ball.{u} atomPoint))
    (isTerminalBallAtomPoint.from reversibleArrow.{u})] at h

private theorem preservesColimit_grayTensorRight_pair (X : DiagSet.{u}) :
    PreservesColimit (pair (ball.{u} atomPoint) (ball.{u} atomPoint)) (grayTensorRight X) :=
  inferInstance

private theorem preservesColimit_grayTensorLeft_pair (X : DiagSet.{u}) :
    PreservesColimit (pair (ball.{u} atomPoint) (ball.{u} atomPoint)) (grayTensorLeft X) :=
  inferInstance

private theorem mono_curry_map_app {A B : DiagSet.{u}} (f : A ⟶ B) [Mono f] (X : DiagSet.{u}) :
    Mono (((Functor.curry.obj grayTensorBifunctor.{u}).map f).app X) :=
  mono_grayTensorBifunctor_map f (𝟙 X)

private theorem mono_curry_flip_map_app {A B : DiagSet.{u}} (f : A ⟶ B) [Mono f]
    (X : DiagSet.{u}) : Mono (((Functor.curry.obj grayTensorBifunctor.{u}).flip.map f).app X) :=
  mono_grayTensorBifunctor_map (𝟙 X) f

private noncomputable def grayLeftUnitorNatIso :
    grayTensorLeft (ball.{u} atomPoint) ≅ 𝟭 DiagSet.{u} :=
  NatIso.ofComponents GrayDiagSet.leftUnitor fun f => GrayDiagSet.leftUnitor_naturality f

private noncomputable def grayRightUnitorNatIso :
    grayTensorRight (ball.{u} atomPoint) ≅ 𝟭 DiagSet.{u} :=
  NatIso.ofComponents GrayDiagSet.rightUnitor fun f => GrayDiagSet.rightUnitor_naturality f

noncomputable def DiagSet.Infty.leftReversibleCylinderOne :
    FunctorialCylinder (DiagSet.Infty.{u} 1) :=
  FunctorialCylinder.ofInterval (C := DiagSet.Infty.{u} 1)
    (Functor.curry.obj grayTensorBifunctor.{u}) isTerminalBallAtomPoint grayLeftUnitorNatIso
    (J := reversibleArrow) (reversibleArrowVertex false) (reversibleArrowVertex true)
    (fun (X : DiagSet.{u}) => preservesColimit_grayTensorRight_pair X)
    (fun (X : DiagSet.{u}) =>
      DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map X _
        (DiagSet.Infty.weakEquivalence_toInfty_reversibleArrow_from 1))
    (fun (X : DiagSet.{u}) => (cofibration_iff _).2 (mono_curry_map_app
      (coprod.desc (reversibleArrowVertex.{u} false) (reversibleArrowVertex.{u} true)) X))

noncomputable def DiagSet.Infty.rightReversibleCylinderOne :
    FunctorialCylinder (DiagSet.Infty.{u} 1) :=
  FunctorialCylinder.ofInterval (C := DiagSet.Infty.{u} 1)
    (Functor.curry.obj grayTensorBifunctor.{u}).flip isTerminalBallAtomPoint grayRightUnitorNatIso
    (J := reversibleArrow) (reversibleArrowVertex false) (reversibleArrowVertex true)
    (fun (X : DiagSet.{u}) => preservesColimit_grayTensorLeft_pair X)
    (fun (X : DiagSet.{u}) =>
      DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map X _
        (DiagSet.Infty.weakEquivalence_toInfty_reversibleArrow_from 1))
    (fun (X : DiagSet.{u}) => (cofibration_iff _).2 (mono_curry_flip_map_app
      (coprod.desc (reversibleArrowVertex.{u} false) (reversibleArrowVertex.{u} true)) X))

theorem DiagSet.Infty.leftReversibleCylinderOne_I_obj (X : DiagSet.{u}) :
    leftReversibleCylinderOne.I.obj X = grayTensor reversibleArrow X := rfl

theorem DiagSet.Infty.leftReversibleCylinderOne_i₀_app (X : DiagSet.{u}) :
    leftReversibleCylinderOne.i₀.app X = (GrayDiagSet.leftUnitor X).inv ≫
      grayTensorBifunctor.map ((reversibleArrowVertex false, 𝟙 X) :
        (ball atomPoint, X) ⟶ (reversibleArrow, X)) := rfl

theorem DiagSet.Infty.leftReversibleCylinderOne_i₁_app (X : DiagSet.{u}) :
    leftReversibleCylinderOne.i₁.app X = (GrayDiagSet.leftUnitor X).inv ≫
      grayTensorBifunctor.map ((reversibleArrowVertex true, 𝟙 X) :
        (ball atomPoint, X) ⟶ (reversibleArrow, X)) := rfl

theorem DiagSet.Infty.leftReversibleCylinderOne_π_app (X : DiagSet.{u}) :
    leftReversibleCylinderOne.π.app X = grayTensorSnd reversibleArrow X := rfl

theorem DiagSet.Infty.rightReversibleCylinderOne_I_obj (X : DiagSet.{u}) :
    rightReversibleCylinderOne.I.obj X = grayTensor X reversibleArrow := rfl

theorem DiagSet.Infty.rightReversibleCylinderOne_i₀_app (X : DiagSet.{u}) :
    rightReversibleCylinderOne.i₀.app X = (GrayDiagSet.rightUnitor X).inv ≫
      grayTensorBifunctor.map ((𝟙 X, reversibleArrowVertex false) :
        (X, ball atomPoint) ⟶ (X, reversibleArrow)) := rfl

theorem DiagSet.Infty.rightReversibleCylinderOne_i₁_app (X : DiagSet.{u}) :
    rightReversibleCylinderOne.i₁.app X = (GrayDiagSet.rightUnitor X).inv ≫
      grayTensorBifunctor.map ((𝟙 X, reversibleArrowVertex true) :
        (X, ball atomPoint) ⟶ (X, reversibleArrow)) := rfl

theorem DiagSet.Infty.rightReversibleCylinderOne_π_app (X : DiagSet.{u}) :
    rightReversibleCylinderOne.π.app X = grayTensorFst X reversibleArrow := rfl

end Atoms.Diagrammatic
