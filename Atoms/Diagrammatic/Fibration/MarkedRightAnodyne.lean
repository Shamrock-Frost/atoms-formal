import Atoms.Diagrammatic.Marked.GrayTensorHorn
import Atoms.Diagrammatic.Fibration.CartesianYoneda
import Atoms.Diagrammatic.Marked.CylinderTensor
import Atoms.Diagrammatic.Marked.GrayTensorEntireLifting
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Leibniz
import Atoms.ForMathlib.CategoryTheory.Sites.Separated
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Atoms.Shape
  Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open MarkedPresheaf (forget)

namespace MarkedDiagSet

inductive rightCylinderMaps : MorphismProperty MarkedDiagSet.{u}
  | mk {A B : MarkedDiagSet.{u}} (g : A ⟶ B) [Mono g] : rightCylinderMaps
      (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false)) g
        (markedIntervalVertex true)).ι

noncomputable def markingInclusionArrowIso (U : Atom) (hU : 0 < U.dimension) :
    CategoryTheory.Arrow.mk (markingToMarkedBall.{u} U hU) ≅
      CategoryTheory.Arrow.mk (markingInclusion U hU) :=
  CategoryTheory.Arrow.isoMk (flatBallIso U).symm
    ((markedAtomIsoYoneda U hU ≪≫ yonedaMarkedIso U hU).symm)
    (MarkedPresheaf.hom_ext (by ext V x; rfl))

theorem rlp_rightCylinderMaps_of_generators {Y T : MarkedDiagSet.{u}} (y : Y ⟶ T)
    (hs : ∀ U : Atom, HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      ((MarkedPresheaf.flat atomMarking).map (sphereInclusion U))
      (markedIntervalVertex true)).ι y)
    (hm : ∀ (U : Atom) (hU : 0 < U.dimension), HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
        (markingInclusion U hU) (markedIntervalVertex true)).ι y) :
    rightCylinderMaps.rlp y := by
  let G := Functor.curry.obj (markedTensorBifunctor.{u} false)
  let α := G.flip.map (markedIntervalVertex.{u} true)
  let P := (MorphismProperty.ofHoms (fun _ : Unit => y)).llp
  have hp {A B : MarkedDiagSet.{u}} (f : A ⟶ B) : P f ↔ HasLiftingProperty f y := by
    constructor
    · intro h
      exact h y (.mk ())
    · intro h X Z g hg
      cases hg
      exact h
  have : ∀ W, PreservesColimitsOfSize.{u, u} (G.flip.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfSize (tensorRight false W))
  have : ∀ W, PreservesColimitsOfShape WalkingSpan (G.flip.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfShape WalkingSpan (tensorRight false W))
  have := NatTrans.isSaturated_leibnizPreimage.{u} α P
  have hbox {A B : MarkedDiagSet.{u}} (f : A ⟶ B) :
      NatTrans.leibnizPreimage α P f ↔
        HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout G f
          (markedIntervalVertex true)).ι y :=
    (P.arrow_mk_iso_iff (arrowIsoPushoutDescSymm _ _ _ _ _)).trans (hp _)
  have hmono : MorphismProperty.monomorphisms MarkedDiagSet.{u} =
      saturation.{u} (functorImage (MarkedPresheaf.flat atomMarking) sphereInclusions ⊔
        MarkedPresheaf.markingMaps atomMarking) :=
    (MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps atomMarking
      monomorphisms_eq_saturation_sphereInclusions.symm).symm
  intro A B f hf
  cases hf with
  | mk g =>
    apply (hbox g).1
    refine saturation_le.{u} _ (NatTrans.leibnizPreimage α P) ?_ g
      ((congrArg (fun Q : MorphismProperty MarkedDiagSet.{u} => Q g) hmono).mp
        (MorphismProperty.monomorphisms.infer_property g))
    rintro X Z j (⟨K, L, t, ht, e⟩ | ⟨U, hU⟩)
    · cases ht with
      | mk U =>
        exact ((NatTrans.leibnizPreimage α P).arrow_mk_iso_iff (eqToIso e).symm).2
          ((hbox _).2 (hs U))
    · exact ((NatTrans.leibnizPreimage α P).arrow_mk_iso_iff
        (markingMapArrowIso U hU ≪≫ markingInclusionArrowIso U hU)).2
          ((hbox _).2 (hm U hU))

inductive markedRightGenerators : MorphismProperty MarkedDiagSet.{u}
  | flat {K L : DiagSet.{u}} (j : K ⟶ L)
      (hj : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map j)) :
      markedRightGenerators ((MarkedPresheaf.flat atomMarking).map j)
  | localization {A B : MarkedDiagSet.{u}} (a : A ⟶ B) (ha : localizationGenerators a) :
      markedRightGenerators a
  | marking {A B : MarkedDiagSet.{u}} (a : A ⟶ B) (ha : markingGeneratorsAbove 1 a) :
      markedRightGenerators a
  | cylinder {A B : MarkedDiagSet.{u}} (a : A ⟶ B) (ha : rightCylinderMaps a) :
      markedRightGenerators a

def markedRightFibrations : MorphismProperty MarkedDiagSet.{u} := markedRightGenerators.rlp

def markedRightAnodyne : MorphismProperty MarkedDiagSet.{u} :=
  saturation.{u} markedRightGenerators

def cellularMarkedRightAnodyne : MorphismProperty MarkedDiagSet.{u} :=
  saturation.{u} rightCylinderMaps

instance isSaturated_markedRightAnodyne : IsSaturated.{u} markedRightAnodyne.{u} :=
  isSaturated_saturation _

instance isSaturated_cellularMarkedRightAnodyne :
    IsSaturated.{u} cellularMarkedRightAnodyne.{u} :=
  isSaturated_saturation _

theorem cellularMarkedRightAnodyne_le_markedRightAnodyne :
    cellularMarkedRightAnodyne.{u} ≤ markedRightAnodyne :=
  saturation_le _ _ fun _ _ _ h ↦ le_saturation _ _ (markedRightGenerators.cylinder _ h)

theorem markedRightFibrations_le_rlp_rightCylinderMaps :
    markedRightFibrations.{u} ≤ rightCylinderMaps.rlp :=
  fun _ _ _ h _ _ _ ha ↦ h _ (markedRightGenerators.cylinder _ ha)

theorem cellularMarkedRightAnodyne_pushoutProduct_of_rightCylinderMaps {K L A B : MarkedDiagSet.{u}}
    (m : K ⟶ L) [Mono m] (a : A ⟶ B) (ha : rightCylinderMaps a) :
    cellularMarkedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) m a).ι := by
  obtain ⟨g⟩ := ha
  have := mono_markedPushoutProduct m g
  let e : CategoryTheory.Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false))
        (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor.{u} false)) m g).ι
        (markedIntervalVertex true)).ι ≅
      CategoryTheory.Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) m
        (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor.{u} false)) g
          (markedIntervalVertex true)).ι).ι :=
    (MarkedTensorDiagSet.ofTensor false).mapArrow.mapIso
      (MonoidalCategory.Arrow.PushoutProduct.associator (C := GrayMarkedDiagSet.{u})
        (CategoryTheory.Arrow.mk ((MarkedTensorDiagSet.toTensor false).map m))
        (CategoryTheory.Arrow.mk ((MarkedTensorDiagSet.toTensor false).map g))
        (CategoryTheory.Arrow.mk
          ((MarkedTensorDiagSet.toTensor false).map (markedIntervalVertex true))))
  exact (cellularMarkedRightAnodyne.arrow_mk_iso_iff e).1
    (le_saturation _ _ (rightCylinderMaps.mk _))

theorem cellularMarkedRightAnodyne_pushoutProduct {K L A B : MarkedDiagSet.{u}} (m : K ⟶ L)
    [Mono m] (i : A ⟶ B) (hi : cellularMarkedRightAnodyne i) :
    cellularMarkedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) m i).ι :=
  pushoutObjObj_ι_mem_of_saturation.{u} (Functor.curry.obj (markedTensorBifunctor.{u} false))
    cellularMarkedRightAnodyne (monomorphisms MarkedDiagSet.{u}) rightCylinderMaps
    (fun _ _ _ _ f₁ f₂ h₁ h₂ ↦
      have : Mono f₁ := h₁
      cellularMarkedRightAnodyne_pushoutProduct_of_rightCylinderMaps f₁ f₂ h₂)
    (le_saturation _ _ (monomorphisms.infer_property m)) hi

theorem hasLiftingProperty_pushoutProduct_flat_map_of_cellularMarkedRightAnodyne
    {A B S Y : MarkedDiagSet.{u}} (i : A ⟶ B)
    (hi : cellularMarkedRightAnodyne i) (y : Y ⟶ S) (hy : rightCylinderMaps.rlp y)
    {K L : DiagSet.{u}} (m : K ⟶ L) [Mono m] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) i).ι y :=
  have : Mono ((MarkedPresheaf.flat atomMarking).map m) := inferInstance
  saturation_le.{u} _ rightCylinderMaps.rlp.llp (le_llp_rlp _) _
    (cellularMarkedRightAnodyne_pushoutProduct ((MarkedPresheaf.flat atomMarking).map m) i hi)
    _ hy

theorem rlp_monomorphisms_markedGrayMapOverRestrict_of_cellularMarkedRightAnodyne
    {A B S Y : MarkedDiagSet.{u}} (i : A ⟶ B)
    (hi : cellularMarkedRightAnodyne i) (b : B ⟶ S) (y : Y ⟶ S)
    (hy : rightCylinderMaps.rlp y) :
    (monomorphisms DiagSet.{u}).rlp (markedGrayMapOverRestrict i b y) :=
  fun _ _ m hm ↦
    have : Mono m := hm
    hasLiftingProperty_markedGrayMapOverRestrict i b y m
      (hasLiftingProperty_pushoutProduct_flat_map_of_cellularMarkedRightAnodyne i hi y hy m)

theorem markedRightAnodyne_le_llp_markedRightFibrations :
    markedRightAnodyne.{u} ≤ markedRightFibrations.llp :=
  saturation_le.{u} _ markedRightGenerators.rlp.llp (le_llp_rlp _)

private theorem flat_map_comp_markedTensorFlatIso_inv {X X' Y Y' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (MarkedPresheaf.flat atomMarking).map (grayTensorBifunctor.map (f, g)) ≫
      (markedTensorFlatIso X' Y').inv =
    (markedTensorFlatIso X Y).inv ≫
      markedTensorMap false ((MarkedPresheaf.flat atomMarking).map f)
        ((MarkedPresheaf.flat atomMarking).map g) := by
  have h₁ {A B : DiagSet.{u}} (k : A ⟶ B) :
      forget.map ((MarkedPresheaf.flat atomMarking).map k) = k := rfl
  have h₂ (A B : DiagSet.{u}) : forget.map (markedTensorFlatIso A B).inv = 𝟙 (grayTensor A B) :=
    rfl
  refine MarkedPresheaf.hom_ext ?_
  rw [Functor.map_comp, Functor.map_comp, forget_map_markedTensorMap, h₁, h₁, h₁, h₂, h₂]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private noncomputable def flatCurryTensorIso :
    Functor.curry.obj grayTensorBifunctor.{u} ⋙
        (Functor.whiskeringRight DiagSet.{u} DiagSet.{u} MarkedDiagSet.{u}).obj
          (MarkedPresheaf.flat atomMarking) ≅
      MarkedPresheaf.flat atomMarking ⋙ Functor.curry.obj (markedTensorBifunctor.{u} false) ⋙
        (Functor.whiskeringLeft DiagSet.{u} MarkedDiagSet.{u} MarkedDiagSet.{u}).obj
          (MarkedPresheaf.flat atomMarking) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (markedTensorFlatIso X Y).symm)
    fun g ↦ flat_map_comp_markedTensorFlatIso_inv (𝟙 X) g) fun f ↦ by
      ext Y : 2
      exact flat_map_comp_markedTensorFlatIso_inv f (𝟙 Y)

theorem markedRightAnodyne_pushoutProduct_flat_map {K L A B : DiagSet.{u}} (m : K ⟶ L) [Mono m]
    (j : A ⟶ B) (hj : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map j)) :
    markedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) ((MarkedPresheaf.flat atomMarking).map j)).ι := by
  have hjm : Mono j := hj.1
  have hmono := mono_pushoutProduct m j
  have hw := DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct m j
    (Or.inr ((weakEquivalence_iff _).2 hj.2))
  exact (markedRightAnodyne.arrow_mk_iso_iff (Functor.PushoutObjObj.mapArrowIso
    (G₃ := MarkedPresheaf.flat atomMarking)
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) m j)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) flatCurryTensorIso)).1
    (le_saturation _ _ (markedRightGenerators.flat _ ⟨hmono, (weakEquivalence_iff _).1 hw⟩))

theorem markedRightAnodyne_pushoutProduct_of_isIso_forget {K L A B : MarkedDiagSet.{u}}
    (m : K ⟶ L) (a : A ⟶ B) [IsIso (forget.map a)] (ha : markedRightAnodyne a) :
    markedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) m a).ι := by
  let T : MorphismProperty MarkedDiagSet.{u} :=
    markingGeneratorsAbove 1 ⊔ MorphismProperty.ofHoms (fun _ : Unit ↦ a)
  have : T.IsSmall.{u} := by
    have : (markingGeneratorsAbove.{u} 1).IsSmall.{u} :=
      MorphismProperty.isSmall_ofHoms _
    have : (MorphismProperty.ofHoms (fun _ : Unit ↦ a)).IsSmall.{u} :=
      MorphismProperty.isSmall_ofHoms _
    exact MorphismProperty.isSmall_sup _ _
  have hT : T ≤ markedRightAnodyne := by
    intro X Y f hf
    rcases hf with hf | hf
    · exact le_saturation _ _ (markedRightGenerators.marking f hf)
    · obtain ⟨⟨⟩⟩ := hf
      exact ha
  have hbox : T.rlp.llp (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) m a).ι := by
    intro Y S y hy
    have hmark : (markingGeneratorsAbove 1).rlp y :=
      fun _ _ g hg ↦ hy g (Or.inl hg)
    have : HasLiftingProperty a y := hy a (Or.inr (MorphismProperty.ofHoms.mk ()))
    exact hasLiftingProperty_pushoutProduct_of_isIso_forget m a y hmark
  exact saturation_le.{u} T markedRightAnodyne hT _
    ((saturation_eq_llp_rlp T).symm ▸ hbox)

private theorem markedRightAnodyne_pushoutProduct_flat_map_of_generators {K L : DiagSet.{u}}
    (m : K ⟶ L) [Mono m] {A B : MarkedDiagSet.{u}} (a : A ⟶ B)
    (ha : markedRightGenerators a) :
    markedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) a).ι := by
  cases ha with
  | flat j hj => exact markedRightAnodyne_pushoutProduct_flat_map m j hj
  | localization a ha =>
    have ha' := le_saturation _ _ (markedRightGenerators.localization a ha)
    obtain ⟨⟨U, hU⟩⟩ := ha
    exact markedRightAnodyne_pushoutProduct_of_isIso_forget _ _ ha'
  | marking a ha =>
    have ha' := le_saturation _ _ (markedRightGenerators.marking a ha)
    obtain ⟨⟨U, hU⟩⟩ := ha
    exact markedRightAnodyne_pushoutProduct_of_isIso_forget _ _ ha'
  | cylinder a ha =>
    have : Mono ((MarkedPresheaf.flat atomMarking).map m) := inferInstance
    exact cellularMarkedRightAnodyne_le_markedRightAnodyne _
      (cellularMarkedRightAnodyne_pushoutProduct_of_rightCylinderMaps _ a ha)

theorem markedRightAnodyne_pushoutProduct_flat_map_of_markedRightAnodyne
    {A B : MarkedDiagSet.{u}} (i : A ⟶ B) (hi : markedRightAnodyne i)
    {K L : DiagSet.{u}} (m : K ⟶ L) [Mono m] :
    markedRightAnodyne (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) i).ι :=
  pushoutObjObj_ι_mem_of_saturation.{u} (Functor.curry.obj (markedTensorBifunctor.{u} false))
    markedRightAnodyne
    (MorphismProperty.ofHoms fun m : Σ K L : DiagSet.{u}, {m : K ⟶ L // Mono m} ↦
      (MarkedPresheaf.flat atomMarking).map m.2.2.1)
    markedRightGenerators
    (fun _ _ _ _ _ f₂ h₁ h₂ ↦ by
      obtain ⟨⟨K, L, m, hm⟩⟩ := h₁
      exact markedRightAnodyne_pushoutProduct_flat_map_of_generators m f₂ h₂)
    (le_saturation _ _ (MorphismProperty.ofHoms.mk
      (⟨K, L, m, inferInstance⟩ : Σ K L : DiagSet.{u}, {m : K ⟶ L // Mono m}))) hi

theorem hasLiftingProperty_pushoutProduct_flat_map_of_markedRightAnodyne
    {A B S Y : MarkedDiagSet.{u}} (i : A ⟶ B) (hi : markedRightAnodyne i) (y : Y ⟶ S)
    (hy : markedRightFibrations y) {K L : DiagSet.{u}} (m : K ⟶ L) [Mono m] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) i).ι y :=
  markedRightAnodyne_le_llp_markedRightFibrations _
    (markedRightAnodyne_pushoutProduct_flat_map_of_markedRightAnodyne i hi m) y hy

theorem rlp_monomorphisms_markedGrayMapOverRestrict_of_markedRightAnodyne
    {A B S Y : MarkedDiagSet.{u}} (i : A ⟶ B) (hi : markedRightAnodyne i) (b : B ⟶ S) (y : Y ⟶ S)
    (hy : markedRightFibrations y) :
    (monomorphisms DiagSet.{u}).rlp (markedGrayMapOverRestrict i b y) :=
  fun _ _ m hm ↦
    have : Mono m := hm
    hasLiftingProperty_markedGrayMapOverRestrict i b y m
      (hasLiftingProperty_pushoutProduct_flat_map_of_markedRightAnodyne i hi y hy m)

noncomputable def pushoutProductIntervalVertexArrowIsoOfIsInitial {X : MarkedDiagSet.{u}}
    (f : X ⟶ markedTensorUnit) (h : IsInitial X) :
    CategoryTheory.Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f
      (markedIntervalVertex true)).ι ≅ CategoryTheory.Arrow.mk (markedIntervalVertex.{u} true) := by
  let F := Functor.curry.obj (markedTensorBifunctor.{u} false)
  have (Z : MarkedDiagSet.{u}) : PreservesColimits (F.flip.obj Z) :=
    (tensorRightAdjunction false Z).leftAdjoint_preservesColimits
  exact (Functor.PushoutObjObj.ι_iso_of_iso_left
    (f₂ := CategoryTheory.Arrow.mk (markedIntervalVertex true))
    (f₁' := CategoryTheory.Arrow.mk f)
    (Functor.PushoutObjObj.ofHasPushout F f (markedIntervalVertex true))
    (Functor.PushoutObjObj.ofIsInitialLeft F f (markedIntervalVertex true) h)
    (Iso.refl (CategoryTheory.Arrow.mk f))) ≪≫
    (CategoryTheory.Arrow.isoMk (markedTensorLeftUnitor false markedTensorUnit)
      (markedTensorLeftUnitor false markedInterval)
      (markedTensorLeftUnitor_naturality false (markedIntervalVertex true)).symm :
      CategoryTheory.Arrow.mk ((F.obj markedTensorUnit).map (markedIntervalVertex true)) ≅
        CategoryTheory.Arrow.mk (markedIntervalVertex true))

noncomputable def pushoutProductFlatSphereAtomPointArrowIso :
    CategoryTheory.Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      ((MarkedPresheaf.flat atomMarking).map (sphereInclusion atomPoint))
      (markedIntervalVertex true)).ι ≅ CategoryTheory.Arrow.mk (markedIntervalVertex.{u} true) := by
  have := (MarkedPresheaf.flatForgetAdjunction atomMarking).leftAdjoint_preservesColimits
  exact pushoutProductIntervalVertexArrowIsoOfIsInitial _
    (IsInitial.isInitialObj _ _
      (DiagSet.isInitialSphereOfDimensionEqZero atomPoint dimension_atomPoint))

theorem hasLiftingProperty_pushoutProduct_flat_sphere_atomPoint {Y S : MarkedDiagSet.{u}}
    (y : Y ⟶ S) [HasLiftingProperty (markedIntervalVertex.{u} true) y] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      ((MarkedPresheaf.flat atomMarking).map (sphereInclusion atomPoint))
      (markedIntervalVertex true)).ι y := by
  exact HasLiftingProperty.of_arrow_iso_left pushoutProductFlatSphereAtomPointArrowIso.symm y

theorem hasLiftingProperty_markedIntervalVertex_of_rlp_rightCylinderMaps {Y S : MarkedDiagSet.{u}}
    (y : Y ⟶ S) (hy : rightCylinderMaps.rlp y) :
    HasLiftingProperty (markedIntervalVertex.{u} true) y := by
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) (initial.to markedTensorUnit.{u})
    (markedIntervalVertex true)
  have : HasLiftingProperty sq.ι y := hy _ (rightCylinderMaps.mk (initial.to markedTensorUnit.{u}))
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (pushoutProductIntervalVertexArrowIsoOfIsInitial (initial.to markedTensorUnit)
      initialIsInitial) y).1 inferInstance

end MarkedDiagSet

variable {E S : DiagSet.{u}}

theorem DiagSet.hasLiftingProperty_flat_map_cartesianMarkedHom (p : E ⟶ S)
    [hp : Fibration ((DiagSet.toInfty 1).map p)] {K L : DiagSet.{u}} (j : K ⟶ L)
    (hj : trivialCofibrations (DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map j)) :
    HasLiftingProperty ((MarkedPresheaf.flat atomMarking).map j)
      (DiagSet.cartesianMarkedHom p) :=
  ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff j
    (DiagSet.cartesianMarkedHom p)).2
    ((hp.mem : reversibleCylinder.{u}.fibrations (inftyGenerators 1) p) _ hj)

theorem DiagSet.hasLiftingProperty_markingGeneratorsAbove_cartesianMarkedHom (p : E ⟶ S)
    {A B : MarkedDiagSet.{u}} (a : A ⟶ B) (ha : markingGeneratorsAbove 1 a) :
    HasLiftingProperty a (DiagSet.cartesianMarkedHom p) := by
  have h : HasMarkedRLP (markingGeneratorsAbove 1) (DiagSet.cartesianMarked p) :=
    (hasMarkedRLP_markingGeneratorsAbove_iff 1 _).2 fun U x hU ↦
      (DiagSet.mem_marked_cartesianMarked p U x).2 (Or.inr (Or.inl (by exact_mod_cast hU)))
  have h' := h a ha
  obtain ⟨⟨U, hU⟩⟩ := ha
  exact hasLiftingProperty_of_isIso_forget _ _ h'

theorem DiagSet.hasLiftingProperty_pushoutProduct_markingInclusion_above_one
    (p : E ⟶ S) (U : Atom) (hU : 1 < U.dimension) :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (MarkedDiagSet.markingInclusion U (by omega)) (markedIntervalVertex true)).ι
      (DiagSet.cartesianMarkedHom p) := by
  have hm : markingGeneratorsAbove 1
      (MarkedDiagSet.markingInclusion.{u} U (by omega)) :=
    MorphismProperty.ofHoms.mk
      (⟨U, by exact_mod_cast hU⟩ : {U : Atom // (1 : ℕ∞) < U.dimension})
  have := DiagSet.hasLiftingProperty_markingGeneratorsAbove_cartesianMarkedHom p _ hm
  exact hasLiftingProperty_pushoutProduct_of_isIso_forget_left _ _ _
    (fun _ _ a ha => DiagSet.hasLiftingProperty_markingGeneratorsAbove_cartesianMarkedHom p a ha)

theorem DiagSet.hasLiftingProperty_localizationGenerators_cartesianMarkedHom (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {A B : MarkedDiagSet.{u}} (a : A ⟶ B) (ha : localizationGenerators a) :
    HasLiftingProperty a (DiagSet.cartesianMarkedHom p) := by
  obtain ⟨⟨U, hU⟩⟩ := ha
  refine hasLiftingProperty_of_isIso_forget _ _ ⟨fun {q _} _ ↦ ?_⟩
  refine ⟨⟨⟨MarkedPresheaf.homMk (MarkedPresheaf.forget.map q) fun V y hy ↦ ?_,
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)),
    terminal.hom_ext _ _⟩⟩⟩
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨g, hg, rfl⟩
  · exact MarkedPresheaf.map_mem_marked q
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).2 hy)
  · refine DiagSet.mem_marked_cartesianMarked_of_isEquivalence p ?_
    have h₁ : IsEquivalence (walkingEquivalence U hU)
        ((toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩) :=
      (topInversionData U hU).isEquivalence_toLocalization ⟨⟩
    have h₂ : (toWalkingEquivalence U hU).app (op V) ⟨g⟩ =
        (walkingEquivalence U hU).map g.op ((toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩) :=
      (congrArg ((toWalkingEquivalence U hU).app (op V))
        (congrArg ULift.up (Category.comp_id g).symm)).trans
        (NatTrans.naturality_apply (toWalkingEquivalence U hU) g.op ⟨𝟙 U⟩)
    rw [h₂]
    refine (congrArg (IsEquivalence _)
      (NatTrans.naturality_apply (MarkedPresheaf.forget.map q) g.op _)).mpr ?_
    exact (isEquivalence_map_iso_iff (asIso g) _).2 (h₁.map _)

theorem DiagSet.markedRightFibrations_cartesianMarkedHom (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    MarkedDiagSet.markedRightFibrations (DiagSet.cartesianMarkedHom p) := by
  intro A B a ha
  cases ha with
  | flat j hj => exact DiagSet.hasLiftingProperty_flat_map_cartesianMarkedHom p j hj
  | localization a ha =>
    exact DiagSet.hasLiftingProperty_localizationGenerators_cartesianMarkedHom p a ha
  | marking a ha =>
    exact DiagSet.hasLiftingProperty_markingGeneratorsAbove_cartesianMarkedHom p a ha
  | cylinder a ha => exact hp a ha

theorem DiagSet.hasLiftingProperty_markedIntervalVertex_cartesianMarkedHom (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] :
    HasLiftingProperty (markedIntervalVertex.{u} true) (DiagSet.cartesianMarkedHom p) := by
  refine ⟨fun {u v} csq ↦ ?_⟩
  let i := ballIsoForgetYoneda.{u} (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)
  let y : E.Vertex := (forget.map u).app (op atomPoint) ⟨𝟙 _⟩
  let fc : diagram S (atomGlobe 1) := (forget.map v).app (op (atomGlobe 1)) (i.hom.app _ ⟨𝟙 _⟩)
  have hf : S.map (atomGlobeVertex true).op fc = y.map p := by
    have h := ConcreteCategory.congr_hom (congr_app (congrArg forget.map csq.w) (op atomPoint))
      ⟨𝟙 _⟩
    refine Eq.trans ?_ h.symm
    exact (NatTrans.naturality_apply (forget.map v) (atomGlobeVertex true).op _).symm
  obtain ⟨x, e, hecell, he⟩ := DiagSet.IsCartesianFibration.exists_isCartesianEdge (p := p) y
    (⟨fc, rfl, hf⟩ : S.Edge _ _)
  have hmem : e.cell ∈ (DiagSet.cartesianMarked p).marked (atomGlobe 1) :=
    (DiagSet.mem_marked_cartesianMarked p _ _).2
      (Or.inr (Or.inr ((DiagSet.isCartesianCell_iff_isCartesianEdge p e).2 he)))
  refine ⟨⟨⟨MarkedPresheaf.homMk (X := markedInterval.{u})
    (i.inv ≫ uliftYonedaEquiv.symm e.cell) fun V g hg ↦ ?_, ?_, ?_⟩⟩⟩
  · obtain ⟨-, ⟨-, hiso⟩ | hdeg⟩ := (mem_marked_yoneda_obj_iff _ _ _).1 hg
    · exact ((DiagSet.cartesianMarked p).transport (asIso g.down.1) e.cell).1 hmem
    · obtain ⟨W, (q : V ⟶ W), (r : W ⟶ atomGlobe 1), hq, hqr⟩ := hdeg
      exact MarkedDiagSet.mem_marked_of_isDegenerate _ ⟨W, q, E.map r.op e.cell, hq.1, hq.2,
        (E.map_comp_apply r.op q.op e.cell).symm.trans
          (congrArg (fun k : V ⟶ atomGlobe 1 ↦ E.map k.op e.cell) hqr)⟩
  · refine MarkedPresheaf.hom_ext ?_
    ext V ⟨k⟩
    change E.map (k ≫ atomGlobeVertex true).op e.cell = (forget.map u).app V ⟨k⟩
    rw [op_comp, E.map_comp_apply, e.tgt_eq]
    refine (NatTrans.naturality_apply (forget.map u) k.op ⟨𝟙 _⟩).symm.trans ?_
    exact congrArg (fun k' ↦ (forget.map u).app V ⟨k'⟩) (Category.comp_id k)
  · refine MarkedPresheaf.hom_ext ((cancel_epi i.hom).1 ?_)
    ext V ⟨k⟩
    change p.app V (E.map k.op e.cell) = (forget.map v).app V (i.hom.app V ⟨k⟩)
    have h := NatTrans.naturality_apply (i.hom ≫ forget.map v) k.op ⟨𝟙 _⟩
    refine (NatTrans.naturality_apply p k.op e.cell).trans ((congrArg (S.map k.op) hecell).trans
      (h.symm.trans ?_))
    exact congrArg (fun k' ↦ (forget.map v).app V (i.hom.app V ⟨k'⟩)) (Category.comp_id k)

theorem DiagSet.isCartesianFibration_iff_hasLiftingProperty_markedIntervalVertex (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsCartesianFibration p ↔
      HasLiftingProperty (markedIntervalVertex.{u} true) (DiagSet.cartesianMarkedHom p) := by
  refine ⟨fun _ ↦ DiagSet.hasLiftingProperty_markedIntervalVertex_cartesianMarkedHom p,
    fun _ ↦ ⟨inferInstance, fun y b f ↦ ?_⟩⟩
  let i := ballIsoForgetYoneda.{u} (MarkedSite.marked (atomGlobe 1) markable_atomGlobe_one)
  let u : markedTensorUnit.{u} ⟶ DiagSet.cartesianMarked p :=
    MarkedPresheaf.homMk (X := markedTensorUnit.{u}) (uliftYonedaEquiv.symm y) fun V x hx ↦
      MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _
        ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).1 hx))
  let v : markedInterval.{u} ⟶ (MarkedPresheaf.sharp atomMarking).obj S :=
    MarkedPresheaf.homMk (X := markedInterval.{u}) (i.inv ≫ uliftYonedaEquiv.symm f.cell)
      fun V x hx ↦ (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 (markedInterval.markable V x hx)
  have csq : CommSq u (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p) v := by
    refine ⟨MarkedPresheaf.hom_ext ?_⟩
    ext V ⟨k⟩
    change p.app V (E.map k.op y) = S.map (k ≫ atomGlobeVertex true).op f.cell
    rw [op_comp, S.map_comp_apply, f.tgt_eq]
    exact NatTrans.naturality_apply p k.op y
  let c : diagram E (atomGlobe 1) :=
    (forget.map csq.lift).app (op (atomGlobe 1)) (i.hom.app _ ⟨𝟙 _⟩)
  have hc : c ∈ (DiagSet.cartesianMarked p).marked (atomGlobe 1) :=
    MarkedPresheaf.map_mem_marked csq.lift ((mem_marked_yoneda_obj_iff _ _ _).2
      ⟨markable_atomGlobe_one, Or.inl ⟨rfl, inferInstanceAs (IsIso (𝟙 (atomGlobe 1)))⟩⟩)
  have hpc : p.app _ c = f.cell := by
    have h := ConcreteCategory.congr_hom (congr_app (congrArg forget.map csq.fac_right)
      (op (atomGlobe 1))) (i.hom.app _ ⟨𝟙 _⟩)
    refine h.trans ?_
    exact S.map_id_apply _ f.cell
  have hty : E.map (atomGlobeVertex true).op c = y := by
    have h := ConcreteCategory.congr_hom (congr_app (congrArg forget.map csq.fac_left)
      (op atomPoint)) ⟨𝟙 _⟩
    refine Eq.trans ?_ (h.trans ?_)
    · exact (NatTrans.naturality_apply (forget.map csq.lift) (atomGlobeVertex true).op _).symm
    · exact E.map_id_apply _ y
  let e : E.Edge (E.map (atomGlobeVertex false).op c) y := ⟨c, rfl, hty⟩
  refine ⟨_, e, hpc, ?_⟩
  rcases (DiagSet.mem_marked_cartesianMarked p _ c).1 hc with hd | hd | hd
  · obtain ⟨x, hx⟩ := DiagSet.exists_id_cell_eq_of_isDegenerate hd
    exact (DiagSet.isCartesianEdge_congr p hx).1 (DiagSet.isCartesianEdge_id x)
  · rw [dimension_atomGlobe] at hd
    exact absurd hd (lt_irrefl 1)
  · exact (DiagSet.isCartesianCell_iff_isCartesianEdge p e).1 hd

theorem DiagSet.isCartesianFibration_of_rlp_rightCylinderMaps (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    DiagSet.IsCartesianFibration p :=
  (DiagSet.isCartesianFibration_iff_hasLiftingProperty_markedIntervalVertex p).2
    (MarkedDiagSet.hasLiftingProperty_markedIntervalVertex_of_rlp_rightCylinderMaps _ hp)

theorem DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_cellularMarkedRightAnodyne (p : E ⟶ S)
    (b : S.Vertex)
    (hb : MarkedDiagSet.cellularMarkedRightAnodyne (S.sharpSliceAtId b))
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    (monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b) :=
  DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_hasLiftingProperty p b fun _ _ m _ ↦
    MarkedDiagSet.hasLiftingProperty_pushoutProduct_flat_map_of_cellularMarkedRightAnodyne _ hb _ hp
      m

theorem DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_markedRightAnodyne (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (b : S.Vertex) (hb : MarkedDiagSet.markedRightAnodyne (S.sharpSliceAtId b))
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    (monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b) :=
  DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_hasLiftingProperty p b fun _ _ m _ ↦
    MarkedDiagSet.hasLiftingProperty_pushoutProduct_flat_map_of_markedRightAnodyne _ hb _
      (DiagSet.markedRightFibrations_cartesianMarkedHom p hp) m

end Atoms.Diagrammatic
