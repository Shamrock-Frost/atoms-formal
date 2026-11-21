import Atoms.Diagrammatic.Joyal.GrayTensor
import Atoms.Diagrammatic.MappingSpace
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Atoms.Homotopical.Simplicial.CartesianMonoidal

open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open Atoms.Homotopical Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

private noncomputable def prodIsoTensor (A B : MarkedSSet.{u}) : A ⨯ B ≅ A ⊗ B where
  hom := lift prod.fst prod.snd
  inv := prod.lift (fst A B) (snd A B)
  hom_inv_id := prod.hom_ext
    (by simp only [Category.assoc, prod.lift_fst, lift_fst, Category.id_comp])
    (by simp only [Category.assoc, prod.lift_snd, lift_snd, Category.id_comp])
  inv_hom_id := CartesianMonoidalCategory.hom_ext _ _
    (by simp only [Category.assoc, prod.lift_fst, lift_fst, Category.id_comp])
    (by simp only [Category.assoc, prod.lift_snd, lift_snd, Category.id_comp])

private theorem prodIsoTensor_hom_naturality {A B A' B' : MarkedSSet.{u}} (f : A ⟶ A')
    (g : B ⟶ B') : prod.map f g ≫ (prodIsoTensor A' B').hom = (prodIsoTensor A B).hom ≫ (f ⊗ₘ g) :=
  CartesianMonoidalCategory.hom_ext _ _
    (by simp only [prodIsoTensor, Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc,
      prod.map_fst])
    (by simp only [prodIsoTensor, Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc,
      prod.map_snd])

private noncomputable def markedProdCurryIso :
    Functor.curry.obj markedProd.{u} ≅ curriedTensor MarkedSSet.{u} :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun B => prodIsoTensor A B)
    fun g => (prodIsoTensor_hom_naturality (𝟙 A) g).trans
      (congrArg _ (id_tensorHom A g)))
    fun f => NatTrans.ext (funext fun B => (prodIsoTensor_hom_naturality f (𝟙 B)).trans
      (congrArg _ (tensorHom_id f B)))

private noncomputable def faceNerveCurriedTensorIso :
    Functor.curry.obj grayTensorBifunctor.{u} ⋙ (Functor.whiskeringRight _ _ _).obj faceNerve ≅
      faceNerve ⋙ curriedTensor MarkedSSet.{u} ⋙ (Functor.whiskeringLeft _ _ _).obj faceNerve :=
  (Iso.refl _ : _ ≅ faceNerveGrayTensorCurry) ≪≫ faceNerveGrayTensorCurryIso ≪≫
    Functor.curryObjProdComp faceNerve faceNerve markedProd ≪≫
      Functor.isoWhiskerLeft faceNerve
        (Functor.isoWhiskerRight markedProdCurryIso ((Functor.whiskeringLeft _ _ _).obj faceNerve))

open MonoidalCategory.Arrow in
noncomputable def faceNervePushoutProductIso {X₁ Y₁ X₂ Y₂ : DiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) :
    faceNerve.mapArrow.obj
        (Arrow.mk (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
          f₁ f₂).ι) ≅
      (Arrow.mk (faceNerve.map f₁) □ Arrow.mk (faceNerve.map f₂)) :=
  Functor.PushoutObjObj.mapArrowIso _ _ faceNerveCurriedTensorIso

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
private theorem weakEquivalence_faceNerve_map {A B : DiagSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) : WeakEquivalence (faceNerve.map f) :=
  (weakEquivalence_iff _).2 (isQuillen_faceNerveAdjunction.trivialCofibrations_le
    ((DiagSet.toInfty 1).map f)
    ⟨MorphismProperty.monomorphisms.infer_property f, (weakEquivalence_iff _).1 hf⟩).2

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
theorem DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct {X₁ Y₁ X₂ Y₂ : DiagSet.{u}}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : WeakEquivalence ((DiagSet.toInfty 1).map f₁) ∨
      WeakEquivalence ((DiagSet.toInfty 1).map f₂)) :
    WeakEquivalence ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) f₁ f₂).ι) := by
  have : Mono (Arrow.mk (faceNerve.map f₁)).hom := faceNerve.map_mono f₁
  have : Mono (Arrow.mk (faceNerve.map f₂)).hom := faceNerve.map_mono f₂
  have hbox := MarkedSSet.weakEquivalence_pushoutProduct (Arrow.mk (faceNerve.map f₁))
    (Arrow.mk (faceNerve.map f₂))
    (h.imp (weakEquivalence_faceNerve_map f₁) (weakEquivalence_faceNerve_map f₂))
  rw [weakEquivalence_iff] at hbox
  have hι : WeakEquivalence (faceNerve.map
      (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) f₁ f₂).ι) :=
    (weakEquivalence_iff _).2
      (((weakEquivalences _).arrow_mk_iso_iff (faceNervePushoutProductIso f₁ f₂)).2 hbox)
  exact ((isQuillen_faceNerveAdjunction.isQuillenEquivalence_iff_of_isCofibrant).1
    isQuillenEquivalence_faceNerveAdjunction).1 _ hι

private theorem weakEquivalence_toInfty_one_isIso_comp {A B C : DiagSet.{u}} (e : A ⟶ B)
    [IsIso e] (g : B ⟶ C) (hg : WeakEquivalence ((DiagSet.toInfty 1).map g)) :
    WeakEquivalence ((DiagSet.toInfty 1).map (e ≫ g)) := by
  rw [Functor.map_comp, weakEquivalence_iff]
  exact (weakEquivalences _).comp_mem _ _ ((weakEquivalences _).of_isIso _)
    ((weakEquivalence_iff _).1 hg)

private theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map_of_mono
    (Z : DiagSet.{u}) {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') [Mono f]
    (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayTensorLeft Z).map f)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
    (initial.to Z) f
  have : IsIso ((grayTensorLeft (⊥_ DiagSet.{u})).map f) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (grayTensorRight Y) _)
      (initialIsInitial.isInitialObj (grayTensorRight Y') _) _
  have : IsIso sq.inl := sq.isPushout.isIso_inl_of_isIso this
  have h : (grayTensorLeft Z).map f = sq.inl ≫ sq.ι := sq.inl_ι.symm
  rw [h]
  exact weakEquivalence_toInfty_one_isIso_comp _ _
    (DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct (initial.to Z) f (Or.inr hf))

private theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map_of_mono
    (Z : DiagSet.{u}) {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') [Mono f]
    (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayTensorRight Z).map f)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
    f (initial.to Z)
  have : IsIso ((grayTensorRight (⊥_ DiagSet.{u})).map f) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (grayTensorLeft Y) _)
      (initialIsInitial.isInitialObj (grayTensorLeft Y') _) _
  have : IsIso sq.inr := sq.isPushout.isIso_inr_of_isIso this
  have h : (grayTensorRight Z).map f = sq.inr ≫ sq.ι := sq.inr_ι.symm
  rw [h]
  exact weakEquivalence_toInfty_one_isIso_comp _ _
    (DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct f (initial.to Z) (Or.inl hf))

private theorem weakEquivalence_toInfty_one_map_of_mono (F : DiagSet.{u} ⥤ DiagSet.{u})
    (hF : ∀ {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') [Mono f],
      WeakEquivalence ((DiagSet.toInfty 1).map f) →
        WeakEquivalence ((DiagSet.toInfty 1).map (F.map f)))
    {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) :
    WeakEquivalence ((DiagSet.toInfty 1).map (F.map f)) := by
  let F' : DiagSet.Infty.{u} 1 ⥤ DiagSet.Infty.{u} 1 := F
  rw [weakEquivalence_iff]
  exact F'.map_mem_of_cofibrant (weakEquivalences _) (fun A B i _ _ hi hw => by
      have : @Mono DiagSet.{u} _ A B i := (cofibration_iff i).1 hi
      exact (weakEquivalence_iff _).1 (hF i hw)) ((DiagSet.toInfty 1).map f)

theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map (Z : DiagSet.{u})
    {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayTensorLeft Z).map f)) :=
  weakEquivalence_toInfty_one_map_of_mono _
    (DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorLeft_map_of_mono Z) f hf

theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map (Z : DiagSet.{u})
    {Y Y' : DiagSet.{u}} (f : Y ⟶ Y') (hf : WeakEquivalence ((DiagSet.toInfty 1).map f)) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayTensorRight Z).map f)) :=
  weakEquivalence_toInfty_one_map_of_mono _
    (DiagSet.Infty.weakEquivalence_toInfty_one_grayTensorRight_map_of_mono Z) f hf

noncomputable def grayTensorRightParametrizedAdjunction :
    (Functor.curry.obj grayTensorBifunctor.{u}).flip ⊣₂ grayHomRightBifunctor :=
  ParametrizedAdjunction.mk' grayTensorRightAdjunction fun {B B'} f {T Z} g =>
    NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun t =>
      (grayHomRightCellEquiv B Z U.unop).injective <| by
        refine (grayHomRightCellEquiv_homEquiv_app B T Z _ U.unop t).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ g) (grayTensorLeft_map_comp_grayTensorRight_map
          (uliftYonedaEquiv.symm t) f).symm).trans ((Category.assoc _ _ _).trans ?_)
        exact ((grayHomRightCellEquiv_grayHomRestrict f Z U.unop _).trans
          (congrArg _ (grayHomRightCellEquiv_homEquiv_app B' T Z g U.unop t))).symm)

private theorem hasLiftingProperty_grayHomRight_pullbackObjObj {K L A B X Y : DiagSet.{u}}
    (j : K ⟶ L) (i : A ⟶ B) (p : X ⟶ Y)
    (h : HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) j i).ι p) :
    HasLiftingProperty j (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p).π :=
  (grayTensorRightParametrizedAdjunction.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout _ j i).flip _).1 h

theorem rlp_monomorphisms_grayHomRight_pullbackObjObj {A B Z W : DiagSet.{u}} (i : A ⟶ B)
    [Mono i] {p : Z ⟶ W} (hp : (MorphismProperty.monomorphisms DiagSet.{u}).rlp p) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p).π := by
  intro T' T j hj
  have : Mono j := hj
  exact hasLiftingProperty_grayHomRight_pullbackObjObj j i p (hp _ (mono_pushoutProduct j i))

theorem fibration_toInfty_one_grayHomRight_pullbackObjObj {A B X Y : DiagSet.{u}} (i : A ⟶ B)
    [Mono i] (p : X ⟶ Y) [Fibration ((DiagSet.toInfty 1).map p)] :
    Fibration ((DiagSet.toInfty 1).map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p).π) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L j hj
  have : @Mono DiagSet.{u} _ K L j := hj.1
  have hp := (fibration_iff ((DiagSet.toInfty 1).map p)).1 inferInstance
  rw [← trivialCofibrations_rlp] at hp
  exact hasLiftingProperty_grayHomRight_pullbackObjObj j i p (hp _ ⟨mono_pushoutProduct j i,
    (weakEquivalence_iff _).1 (DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct j i
      (Or.inl ((weakEquivalence_iff _).2 hj.2)))⟩)

theorem weakEquivalence_toInfty_one_grayHomRight_pullbackObjObj {A B X Y : DiagSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) [Fibration ((DiagSet.toInfty 1).map p)]
    (h : WeakEquivalence ((DiagSet.toInfty 1).map i) ∨
      WeakEquivalence ((DiagSet.toInfty 1).map p)) :
    WeakEquivalence ((DiagSet.toInfty 1).map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p).π) := by
  have hπ : trivialFibrations _ ((DiagSet.toInfty 1).map
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i p).π) := by
    rw [← cofibrations_rlp]
    intro K L j hj
    have : @Mono DiagSet.{u} _ K L j := hj
    refine hasLiftingProperty_grayHomRight_pullbackObjObj j i p ?_
    rcases h with hi | hp
    · have hp := (fibration_iff ((DiagSet.toInfty 1).map p)).1 inferInstance
      rw [← trivialCofibrations_rlp] at hp
      exact hp _ ⟨mono_pushoutProduct j i, (weakEquivalence_iff _).1
        (DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct j i (Or.inr hi))⟩
    · have hp : trivialFibrations _ ((DiagSet.toInfty 1).map p) :=
        ⟨(fibration_iff _).1 inferInstance, (weakEquivalence_iff _).1 hp⟩
      rw [← cofibrations_rlp] at hp
      exact hp _ (mono_pushoutProduct j i)
  exact (weakEquivalence_iff _).2 hπ.2

private noncomputable def isTerminalGrayHomRight (K : DiagSet.{u}) :
    IsTerminal ((grayHomRight K).obj (⊤_ DiagSet.{u})) :=
  have := (grayTensorRightAdjunction K).rightAdjoint_preservesLimits
  terminalIsTerminal.isTerminalObj (grayHomRight K) _

noncomputable def isTerminalGrayHomRightInitial (X : DiagSet.{u}) :
    IsTerminal ((grayHomRight (⊥_ DiagSet.{u})).obj X) :=
  IsTerminal.ofUniqueHom
    (fun T => (grayTensorRightAdjunction _).homEquiv T X
      ((initialIsInitial.isInitialObj (grayTensorLeft T) _).to X))
    fun T _ => ((grayTensorRightAdjunction _).homEquiv T X).symm_apply_eq.1
      ((initialIsInitial.isInitialObj (grayTensorLeft T) _).hom_ext _ _)

theorem fibration_toInfty_one_grayHomRestrict {A B : DiagSet.{u}} (i : A ⟶ B) [Mono i]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) :
    Fibration ((DiagSet.toInfty 1).map ((grayHomRestrict i).app X)) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 ((isFibrant_infty_iff 1 _).2 hX)
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u} i (terminal.from X)
  have : IsIso sq.fst := sq.isPullback.isIso_fst_of_isIso
    (isIso_of_isTerminal (isTerminalGrayHomRight B) (isTerminalGrayHomRight A) _)
  have : Fibration ((DiagSet.toInfty 1).map sq.π) :=
    fibration_toInfty_one_grayHomRight_pullbackObjObj i (terminal.from X)
  have h : (grayHomRestrict i).app X = sq.π ≫ sq.fst := sq.π_fst.symm
  have h' : (DiagSet.toInfty 1).map ((grayHomRestrict i).app X) =
      (DiagSet.toInfty 1).map sq.π ≫ (DiagSet.toInfty 1).map sq.fst := by
    rw [← Functor.map_comp]
    exact congrArg _ h
  have : Fibration ((DiagSet.toInfty 1).map sq.fst) := inferInstance
  rw [h']
  exact (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).comp_mem _ _
    ((fibration_iff _).1 ‹_›) ((fibration_iff _).1 this))

theorem isInftyCategory_grayHomRight (K : DiagSet.{u}) {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) : IsInftyCategory 1 ((grayHomRight K).obj X) :=
  have := fibration_toInfty_one_grayHomRestrict (initial.to K) hX
  (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj ((grayHomRight K).obj X))).1
    ((isFibrant_iff_of_isTerminal ((DiagSet.toInfty 1).map ((grayHomRestrict (initial.to K)).app X))
      (isTerminalGrayHomRightInitial X)).2 this)

theorem isInftyCategory_functorCategory (pseudo : Bool) (K : DiagSet.{u}) {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) : IsInftyCategory 1 (functorCategory pseudo K X) := by
  have hgray := isInftyCategory_of_iso (functorCategoryGrayIso K X)
    (isInftyCategory_grayHomRight K hX)
  cases pseudo
  · exact hgray
  · have := isIso_functorCategoryPseudoToGray K hX
    exact isInftyCategory_of_iso (asIso (functorCategoryPseudoToGray K X)) hgray

noncomputable def grayTensorLeftParametrizedAdjunction :
    Functor.curry.obj grayTensorBifunctor.{u} ⊣₂ grayHomLeftBifunctor :=
  ParametrizedAdjunction.mk' grayTensorLeftAdjunction fun {A A'} f {T Z} g =>
    NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun t =>
      (grayHomLeftCellEquiv A Z V.unop).injective <| by
        refine (grayHomLeftCellEquiv_homEquiv_app A T Z _ V.unop t).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ g) (grayTensorLeft_map_comp_grayTensorRight_map f
          (uliftYonedaEquiv.symm t))).trans ((Category.assoc _ _ _).trans ?_)
        exact ((grayHomLeftCellEquiv_grayHomLeftRestrict f Z V.unop _).trans
          (congrArg _ (grayHomLeftCellEquiv_homEquiv_app A' T Z g V.unop t))).symm)

private theorem hasLiftingProperty_grayHomLeft_pullbackObjObj {K L A B X Y : DiagSet.{u}}
    (j : K ⟶ L) (i : A ⟶ B) (p : X ⟶ Y)
    (h : HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) i j).ι p) :
    HasLiftingProperty j (Functor.PullbackObjObj.ofHasPullback grayHomLeftBifunctor.{u} i p).π :=
  (grayTensorLeftParametrizedAdjunction.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout _ i j) _).1 h

theorem fibration_toInfty_one_grayHomLeft_pullbackObjObj {A B X Y : DiagSet.{u}} (i : A ⟶ B)
    [Mono i] (p : X ⟶ Y) [Fibration ((DiagSet.toInfty 1).map p)] :
    Fibration ((DiagSet.toInfty 1).map
      (Functor.PullbackObjObj.ofHasPullback grayHomLeftBifunctor.{u} i p).π) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L j hj
  have : @Mono DiagSet.{u} _ K L j := hj.1
  have hp := (fibration_iff ((DiagSet.toInfty 1).map p)).1 inferInstance
  rw [← trivialCofibrations_rlp] at hp
  exact hasLiftingProperty_grayHomLeft_pullbackObjObj j i p (hp _ ⟨mono_pushoutProduct i j,
    (weakEquivalence_iff _).1 (DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct i j
      (Or.inr ((weakEquivalence_iff _).2 hj.2)))⟩)

private noncomputable def isTerminalGrayHomLeft (A : DiagSet.{u}) :
    IsTerminal ((grayHomLeft A).obj (⊤_ DiagSet.{u})) :=
  have := (grayTensorLeftAdjunction A).rightAdjoint_preservesLimits
  terminalIsTerminal.isTerminalObj (grayHomLeft A) _

private noncomputable def isTerminalGrayHomLeftInitial (X : DiagSet.{u}) :
    IsTerminal ((grayHomLeft (⊥_ DiagSet.{u})).obj X) :=
  IsTerminal.ofUniqueHom
    (fun T => (grayTensorLeftAdjunction _).homEquiv T X
      ((initialIsInitial.isInitialObj (grayTensorRight T) _).to X))
    fun T _ => ((grayTensorLeftAdjunction _).homEquiv T X).symm_apply_eq.1
      ((initialIsInitial.isInitialObj (grayTensorRight T) _).hom_ext _ _)

theorem fibration_toInfty_one_grayHomLeftRestrict {A B : DiagSet.{u}} (i : A ⟶ B) [Mono i]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) :
    Fibration ((DiagSet.toInfty 1).map ((grayHomLeftRestrict i).app X)) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 ((isFibrant_infty_iff 1 _).2 hX)
  let sq := Functor.PullbackObjObj.ofHasPullback grayHomLeftBifunctor.{u} i (terminal.from X)
  have : IsIso sq.fst := sq.isPullback.isIso_fst_of_isIso
    (isIso_of_isTerminal (isTerminalGrayHomLeft B) (isTerminalGrayHomLeft A) _)
  have : Fibration ((DiagSet.toInfty 1).map sq.π) :=
    fibration_toInfty_one_grayHomLeft_pullbackObjObj i (terminal.from X)
  have h : (DiagSet.toInfty 1).map ((grayHomLeftRestrict i).app X) =
      (DiagSet.toInfty 1).map sq.π ≫ (DiagSet.toInfty 1).map sq.fst := by
    rw [← Functor.map_comp]
    exact congrArg _ sq.π_fst.symm
  have hfst : Fibration ((DiagSet.toInfty 1).map sq.fst) := inferInstance
  rw [h]
  exact (fibration_iff _).2 ((fibrations (DiagSet.Infty.{u} 1)).comp_mem _ _
    ((fibration_iff _).1 ‹_›) ((fibration_iff _).1 hfst))

theorem isInftyCategory_grayHomLeft (K : DiagSet.{u}) {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) : IsInftyCategory 1 ((grayHomLeft K).obj X) :=
  have := fibration_toInfty_one_grayHomLeftRestrict (initial.to K) hX
  (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj ((grayHomLeft K).obj X))).1
    ((isFibrant_iff_of_isTerminal
      ((DiagSet.toInfty 1).map ((grayHomLeftRestrict (initial.to K)).app X))
      (isTerminalGrayHomLeftInitial X)).2 this)

theorem DiagSet.isFibrant_mappingSpace {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : (DiagSet.toSSet.obj X) _⦋0⦌) :
    IsFibrant ((DiagSet.toInfty 1).obj (X.mappingSpace x y).toFunctor) :=
  have := fibration_toInfty_one_grayHomRestrict intervalBoundaryι hX
  X.isFibrant_mappingSpace_of_fibration x y

theorem DiagSet.isInftyCategory_mappingSpace {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x y : (DiagSet.toSSet.obj X) _⦋0⦌) : IsInftyCategory 1 (X.mappingSpace x y).toFunctor :=
  (isFibrant_infty_iff 1 _).1 (DiagSet.isFibrant_mappingSpace hX x y)

end Atoms.Diagrammatic
