import Atoms.Diagrammatic.Joyal.GrayHomFaceNerve
import Atoms.Diagrammatic.Limits.ProductPullback
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FibrewisePath
import Atoms.ForMathlib.CategoryTheory.Localization.Predicate

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory Simplicial
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

noncomputable def grayHomFaceNerveAdjunction (S : SSet.{u}) :=
  DiagSet.Infty.sSetDiagSetAdj.{u}.comp
    ((DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)).comp faceNerveAdjunction)

noncomputable def flatTensorLeftAdjunction (S : SSet.{u}) :=
  (ihom.adjunction S).comp (MarkedPresheaf.flatForgetAdjunction edgeMarking)

noncomputable def faceNerveSSetAdjunction :=
  DiagSet.Infty.sSetDiagSetAdj.{u}.comp faceNerveAdjunction

theorem isQuillen_grayHomFaceNerveAdjunction (S : SSet.{u}) :
    (grayHomFaceNerveAdjunction S).IsQuillen :=
  isQuillen_sSetDiagSetAdj.comp
    ((DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one _).comp isQuillen_faceNerveAdjunction)

theorem isQuillen_flatTensorLeftAdjunction (S : SSet.{u}) :
    (flatTensorLeftAdjunction S).IsQuillen :=
  (isQuillen_ihomAdjunction S).comp
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen

theorem isQuillen_faceNerveSSetAdjunction : faceNerveSSetAdjunction.{u}.IsQuillen :=
  isQuillen_sSetDiagSetAdj.comp isQuillen_faceNerveAdjunction

private theorem flat_map_whiskerLeft_comp_flatTensorIso_hom (S : SSet.{u}) {K K' : SSet.{u}}
    (k : K ⟶ K') :
    (MarkedPresheaf.flat edgeMarking).map (S ◁ k) ≫ (SSet.flatTensorIso S K').hom =
      (SSet.flatTensorIso S K).hom ≫
        ((MarkedPresheaf.flat edgeMarking).obj S ◁ (MarkedPresheaf.flat edgeMarking).map k) :=
  MarkedPresheaf.hom_ext rfl

noncomputable def faceNerveGrayTensorFlat (S : SSet.{u}) :
    SSet.toDiagSet ⋙ grayTensorRight (SSet.toDiagSet.obj S) ⋙ faceNerve ⟶
      MonoidalCategory.tensorLeft S ⋙ MarkedPresheaf.flat edgeMarking where
  app K := lift (faceNerve.map (grayTensorSnd _ _) ≫ faceNerveToDiagSetFlat.app S)
      (faceNerve.map (grayTensorFst _ _) ≫ faceNerveToDiagSetFlat.app K) ≫
    (SSet.flatTensorIso S K).inv
  naturality K K' k := by
    have hk : (MonoidalCategory.tensorLeft S).map k = S ◁ k := rfl
    rw [← cancel_mono (SSet.flatTensorIso S K').hom]
    simp only [Functor.comp_map, Category.assoc, Iso.inv_hom_id, Category.comp_id, hk,
      flat_map_whiskerLeft_comp_flatTensorIso_hom, Iso.inv_hom_id_assoc]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst, grayTensorRight_map_eq,
        ← Functor.map_comp_assoc]
      rw [grayTensorBifunctor_map_grayTensorSnd, Category.comp_id]
    · simp only [Category.assoc, lift_snd, whiskerLeft_snd, lift_snd_assoc,
        grayTensorRight_map_eq]
      rw [← Functor.map_comp_assoc, grayTensorBifunctor_map_grayTensorFst,
        Functor.map_comp_assoc]
      exact congrArg (_ ≫ ·) (faceNerveToDiagSetFlat.naturality k)

private theorem isIso_lift_faceNerve_map_grayTensorSnd (A B : DiagSet.{u}) :
    IsIso (lift (faceNerve.map (grayTensorSnd A B)) (faceNerve.map (grayTensorFst A B))) := by
  have e : lift (faceNerve.map (grayTensorSnd A B)) (faceNerve.map (grayTensorFst A B)) =
      prod.lift (faceNerve.map (grayTensorFst A B)) (faceNerve.map (grayTensorSnd A B)) ≫
        lift (prod.snd : faceNerve.obj A ⨯ faceNerve.obj B ⟶ _) prod.fst := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, Category.assoc, lift_fst, prod.lift_snd]
    · rw [lift_snd, Category.assoc, lift_snd, prod.lift_fst]
  have : IsIso (prod.lift (faceNerve.map (grayTensorFst A B))
      (faceNerve.map (grayTensorSnd A B))) := by
    have h : IsIso (faceNerveGrayTensorIso.hom.app (A, B)) := inferInstance
    rw [faceNerveGrayTensorIso_hom_app] at h
    exact h
  have : IsIso (lift (prod.snd : faceNerve.obj A ⨯ faceNerve.obj B ⟶ _) prod.fst) :=
    ⟨⟨prod.lift (snd _ _) (fst _ _), by ext <;> simp,
      CartesianMonoidalCategory.hom_ext _ _ (by rw [Category.assoc, lift_fst, prod.lift_snd,
        Category.id_comp]) (by rw [Category.assoc, lift_snd, prod.lift_fst, Category.id_comp])⟩⟩
  rw [e]
  exact IsIso.comp_isIso

theorem weakEquivalence_faceNerveGrayTensorFlat_app (S K : SSet.{u}) :
    WeakEquivalence ((faceNerveGrayTensorFlat S).app K) := by
  have := isIso_lift_faceNerve_map_grayTensorSnd (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj S)
  have := weakEquivalence_faceNerveToDiagSetFlat_app S
  have := weakEquivalence_faceNerveToDiagSetFlat_app K
  have := MarkedSSet.weakEquivalence_tensorHom (faceNerveToDiagSetFlat.app S)
    (faceNerveToDiagSetFlat.app K)
  have e : (faceNerveGrayTensorFlat S).app K =
      lift (faceNerve.map (grayTensorSnd (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj S)))
        (faceNerve.map (grayTensorFst (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj S))) ≫
        (faceNerveToDiagSetFlat.app S ⊗ₘ faceNerveToDiagSetFlat.app K) ≫
          (SSet.flatTensorIso S K).inv := by
    rw [lift_map_assoc]
    rfl
  rw [e]
  infer_instance

noncomputable def grayHomSimplicialComparison (S : SSet.{u}) :
    MarkedPresheaf.forget (D := edgeMarking) ⋙ ihom S ⟶
      faceNerveRight ⋙ grayHomRight (SSet.toDiagSet.obj S) ⋙ DiagSet.toSSet :=
  conjugateEquiv (flatTensorLeftAdjunction S) (grayHomFaceNerveAdjunction S)
    (faceNerveGrayTensorFlat S)

noncomputable def faceNerveRightComparison :
    MarkedPresheaf.forget (D := edgeMarking) ⟶ faceNerveRight.{u} ⋙ DiagSet.toSSet :=
  conjugateEquiv (MarkedPresheaf.flatForgetAdjunction edgeMarking) faceNerveSSetAdjunction
    faceNerveToDiagSetFlat

theorem weakEquivalence_grayHomSimplicialComparison_app (S : SSet.{u}) (C : MarkedSSet.{u})
    [IsFibrant C] : WeakEquivalence ((grayHomSimplicialComparison S).app C) :=
  (isQuillen_flatTensorLeftAdjunction S).weakEquivalence_conjugateEquiv_app
    (isQuillen_grayHomFaceNerveAdjunction S) (faceNerveGrayTensorFlat S)
    (fun K _ => weakEquivalence_faceNerveGrayTensorFlat_app S K) C

theorem weakEquivalence_faceNerveRightComparison_app (C : MarkedSSet.{u}) [IsFibrant C] :
    WeakEquivalence (faceNerveRightComparison.app C) :=
  Adjunction.IsQuillen.weakEquivalence_conjugateEquiv_app
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen
    isQuillen_faceNerveSSetAdjunction faceNerveToDiagSetFlat
    (fun K _ => weakEquivalence_faceNerveToDiagSetFlat_app K) C

theorem exists_weakEquivalence_faceNerveRight (Y : DiagSet.{u}) :
    ∃ (C : MarkedSSet.{u}) (_ : IsFibrant C) (η : Y ⟶ faceNerveRight.obj C),
      WeakEquivalence ((DiagSet.toInfty 1).map η) ∧
        ∀ (C' : MarkedSSet.{u}) [IsFibrant C'] (θ : Y ⟶ faceNerveRight.obj C'),
          ∃ c : C ⟶ C', η ≫ faceNerveRight.map c = θ := by
  let φ := factorizationData (trivialCofibrations MarkedSSet.{u}) (fibrations _)
    (terminal.from (faceNerve.obj Y))
  have : IsFibrant φ.Z := by
    rw [HomotopicalAlgebra.isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    exact (fibration_iff _).2 φ.hp
  have hi : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  have : Cofibration φ.i := (cofibration_iff _).2 φ.hi.1
  refine ⟨φ.Z, inferInstance, faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj Y) φ.Z φ.i,
    (isQuillenEquivalence_faceNerveAdjunction.weakEquivalence_iff
      (A := (DiagSet.toInfty 1).obj Y) φ.i).1 hi, fun C' _ θ => ?_⟩
  let sq : CommSq ((faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj Y) C').symm θ) φ.i
      (terminal.from C') (terminal.from φ.Z) := ⟨terminal.hom_ext _ _⟩
  obtain ⟨⟨l⟩⟩ := (ModelCategory.cm4a φ.i (terminal.from C')).sq_hasLift sq
  exact ⟨l.l, ((faceNerveAdjunction.homEquiv_naturality_right φ.i l.l).symm.trans
    (congrArg (faceNerveAdjunction.homEquiv ((DiagSet.toInfty 1).obj Y) C') l.fac_left)).trans
      (Equiv.apply_symm_apply _ _)⟩

private noncomputable def flatTensorLeftMap {S S' : SSet.{u}} (s : S ⟶ S') :
    MonoidalCategory.tensorLeft S ⋙ MarkedPresheaf.flat edgeMarking ⟶
      MonoidalCategory.tensorLeft S' ⋙ MarkedPresheaf.flat edgeMarking :=
  Functor.whiskerRight ((MonoidalCategory.tensoringLeft SSet.{u}).map s) _

private noncomputable def faceNerveGrayTensorMap {S S' : SSet.{u}} (s : S ⟶ S') :
    SSet.toDiagSet ⋙ grayTensorRight (SSet.toDiagSet.obj S) ⋙ faceNerve ⟶
      SSet.toDiagSet ⋙ grayTensorRight (SSet.toDiagSet.obj S') ⋙ faceNerve where
  app K := faceNerve.map ((grayTensorLeft (SSet.toDiagSet.obj K)).map (SSet.toDiagSet.map s))
  naturality K K' k := by
    simp only [Functor.comp_map, ← Functor.map_comp, grayTensorRight_map_eq, grayTensorLeft_map_eq,
      ← grayTensorBifunctor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

private theorem faceNerveGrayTensorMap_comp_faceNerveGrayTensorFlat {S S' : SSet.{u}}
    (s : S ⟶ S') :
    faceNerveGrayTensorMap s ≫ faceNerveGrayTensorFlat S' =
      faceNerveGrayTensorFlat S ≫ flatTensorLeftMap s := by
  refine NatTrans.ext (funext fun K => ?_)
  have hs : (flatTensorLeftMap s).app K = (MarkedPresheaf.flat edgeMarking).map (s ▷ K) := rfl
  have e : (MarkedPresheaf.flat edgeMarking).map (s ▷ K) ≫ (SSet.flatTensorIso S' K).hom =
      (SSet.flatTensorIso S K).hom ≫
        ((MarkedPresheaf.flat edgeMarking).map s ▷ (MarkedPresheaf.flat edgeMarking).obj K) :=
    MarkedPresheaf.hom_ext rfl
  simp only [NatTrans.comp_app, hs]
  rw [← cancel_mono (SSet.flatTensorIso S' K).hom]
  simp only [faceNerveGrayTensorFlat, faceNerveGrayTensorMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, e, Iso.inv_hom_id_assoc]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp only [Category.assoc, lift_fst, whiskerRight_fst, lift_fst_assoc, grayTensorLeft_map_eq]
    rw [← Functor.map_comp_assoc, grayTensorBifunctor_map_grayTensorSnd, Functor.map_comp_assoc]
    exact congrArg (_ ≫ ·) (faceNerveToDiagSetFlat.naturality s)
  · simp only [Category.assoc, lift_snd, whiskerRight_snd, grayTensorLeft_map_eq]
    rw [← Functor.map_comp_assoc, grayTensorBifunctor_map_grayTensorFst, Category.comp_id]

private theorem conjugateEquiv_flatTensorLeftMap {S S' : SSet.{u}} (s : S ⟶ S') :
    conjugateEquiv (flatTensorLeftAdjunction S') (flatTensorLeftAdjunction S)
        (flatTensorLeftMap s) =
      Functor.whiskerLeft (MarkedPresheaf.forget (D := edgeMarking)) (MonoidalClosed.pre s) := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ fun A C f => ?_
  have h := homEquiv_conjugateEquiv_app (ihom.adjunction S') (ihom.adjunction S)
    ((MonoidalCategory.tensoringLeft SSet.{u}).map s) (c := A)
    ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ C f)
  exact h

private theorem grayHomFaceNerveAdjunction_homEquiv (S A : SSet.{u}) (C : MarkedSSet.{u})
    (g : (SSet.toDiagSet ⋙ grayTensorRight (SSet.toDiagSet.obj S) ⋙ faceNerve).obj A ⟶ C) :
    (grayHomFaceNerveAdjunction S).homEquiv A C g =
      DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _
        ((DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)).homEquiv _ _
          (faceNerveAdjunction.homEquiv _ C g)) := by
  have h₁ := congrArg (fun e => e A C g) (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj
    ((DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)).comp faceNerveAdjunction))
  have h₂ := congrArg (fun e => e (SSet.toDiagSetInfty.obj A) C g) (Adjunction.comp_homEquiv
    (DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)) faceNerveAdjunction)
  exact h₁.trans (congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _) h₂)

private theorem conjugateEquiv_faceNerveGrayTensorMap {S S' : SSet.{u}} (s : S ⟶ S') :
    conjugateEquiv (grayHomFaceNerveAdjunction S') (grayHomFaceNerveAdjunction S)
        (faceNerveGrayTensorMap s) =
      Functor.whiskerLeft faceNerveRight
        (Functor.whiskerRight (grayHomRestrict (SSet.toDiagSet.map s)) DiagSet.toSSet) := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ fun A C f => ?_
  have e : faceNerveAdjunction.homEquiv _ C ((faceNerveGrayTensorMap s).app A ≫ f) =
      (grayTensorLeft (SSet.toDiagSet.obj A)).map (SSet.toDiagSet.map s) ≫
        faceNerveAdjunction.homEquiv _ C f :=
    faceNerveAdjunction.homEquiv_naturality_left _ f
  refine (grayHomFaceNerveAdjunction_homEquiv S A C _).trans (Eq.trans ?_
    (congrArg (· ≫ _) (grayHomFaceNerveAdjunction_homEquiv S' A C f).symm))
  exact (congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _) ((congrArg
    ((DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)).homEquiv _ _) e).trans
      (homEquiv_comp_grayHomRestrict (SSet.toDiagSet.map s) _).symm)).trans
    (DiagSet.Infty.sSetDiagSetAdj.homEquiv_naturality_right _ _)

@[reassoc]
theorem pre_app_comp_grayHomSimplicialComparison_app {S S' : SSet.{u}} (s : S ⟶ S')
    (C : MarkedSSet.{u}) :
    (MonoidalClosed.pre s).app ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        (grayHomSimplicialComparison S).app C =
      (grayHomSimplicialComparison S').app C ≫
        DiagSet.toSSet.map
          ((grayHomRestrict (SSet.toDiagSet.map s)).app (faceNerveRight.obj C)) := by
  have h₁ := conjugateEquiv_comp (flatTensorLeftAdjunction S') (flatTensorLeftAdjunction S)
    (grayHomFaceNerveAdjunction S) (flatTensorLeftMap s) (faceNerveGrayTensorFlat S)
  have h₂ := conjugateEquiv_comp (flatTensorLeftAdjunction S') (grayHomFaceNerveAdjunction S')
    (grayHomFaceNerveAdjunction S) (faceNerveGrayTensorFlat S') (faceNerveGrayTensorMap s)
  have h := congrArg (conjugateEquiv (flatTensorLeftAdjunction S') (grayHomFaceNerveAdjunction S))
    (faceNerveGrayTensorMap_comp_faceNerveGrayTensorFlat s)
  have k := congrArg (fun t => t.app C) (h₂.trans (h.trans h₁.symm))
  exact (congrArg (· ≫ (grayHomSimplicialComparison S).app C)
    (NatTrans.congr_app (conjugateEquiv_flatTensorLeftMap s) C).symm).trans
      (k.symm.trans (congrArg ((grayHomSimplicialComparison S').app C ≫ ·)
        (NatTrans.congr_app (conjugateEquiv_faceNerveGrayTensorMap s) C)))

private noncomputable def flatTensorLeftSnd (S : SSet.{u}) :
    MonoidalCategory.tensorLeft S ⋙ MarkedPresheaf.flat edgeMarking ⟶
      MarkedPresheaf.flat edgeMarking where
  app K := (MarkedPresheaf.flat edgeMarking).map (snd S K)
  naturality K K' k := by
    have hk : (MonoidalCategory.tensorLeft S).map k = S ◁ k := rfl
    simp only [Functor.comp_map, hk, ← Functor.map_comp, whiskerLeft_snd]

private noncomputable def faceNerveGrayTensorFst (S : SSet.{u}) :
    SSet.toDiagSet ⋙ grayTensorRight (SSet.toDiagSet.obj S) ⋙ faceNerve ⟶
      SSet.toDiagSet ⋙ faceNerve where
  app K := faceNerve.map (grayTensorFst (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj S))
  naturality K K' k := by
    simp only [Functor.comp_map, ← Functor.map_comp, grayTensorRight_map_grayTensorFst]

private theorem faceNerveGrayTensorFlat_comp_flatTensorLeftSnd (S : SSet.{u}) :
    faceNerveGrayTensorFlat S ≫ flatTensorLeftSnd S =
      faceNerveGrayTensorFst S ≫ faceNerveToDiagSetFlat := by
  refine NatTrans.ext (funext fun K => ?_)
  have e : (SSet.flatTensorIso S K).inv ≫ (MarkedPresheaf.flat edgeMarking).map (snd S K) =
      snd _ _ := MarkedPresheaf.hom_ext rfl
  simp only [NatTrans.comp_app, faceNerveGrayTensorFlat, flatTensorLeftSnd, faceNerveGrayTensorFst,
    Category.assoc, e, lift_snd]

private theorem flatTensorLeftAdjunction_homEquiv (S A : SSet.{u}) (C : MarkedSSet.{u})
    (g : (MarkedPresheaf.flat edgeMarking).obj (S ⊗ A) ⟶ C) :
    (flatTensorLeftAdjunction S).homEquiv A C g =
      MonoidalClosed.curry ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ C g) :=
  congrArg (fun e => e A C g) (Adjunction.comp_homEquiv (ihom.adjunction S)
    (MarkedPresheaf.flatForgetAdjunction edgeMarking))

private theorem faceNerveSSetAdjunction_homEquiv (A : SSet.{u}) (C : MarkedSSet.{u})
    (g : faceNerve.obj (SSet.toDiagSet.obj A) ⟶ C) :
    faceNerveSSetAdjunction.homEquiv A C g =
      DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _ (faceNerveAdjunction.homEquiv _ C g) :=
  congrArg (fun e => e A C g) (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj
    faceNerveAdjunction)

private noncomputable def constDiagramNatTrans (S : SSet.{u}) : 𝟭 SSet.{u} ⟶ ihom S where
  app K := SSet.constDiagram S K
  naturality _ _ f := (SSet.constDiagram_comp_ihom_map f S).symm

private noncomputable def grayConstDiagramNatTrans (K : DiagSet.{u}) :
    𝟭 DiagSet.{u} ⟶ grayHomRight K where
  app X := constDiagram K X
  naturality _ _ f := constDiagram_naturality K f

private theorem conjugateEquiv_flatTensorLeftSnd (S : SSet.{u}) :
    conjugateEquiv (MarkedPresheaf.flatForgetAdjunction edgeMarking) (flatTensorLeftAdjunction S)
        (flatTensorLeftSnd S) =
      Functor.whiskerLeft (MarkedPresheaf.forget (D := edgeMarking)) (constDiagramNatTrans S) := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ fun A C f => ?_
  refine (flatTensorLeftAdjunction_homEquiv S A C _).trans ?_
  have e := (MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv_naturality_left (snd S A) f
  refine (congrArg MonoidalClosed.curry e).trans ?_
  refine Eq.trans ?_ (MonoidalClosed.curry_natural_left _ _)
  exact congrArg MonoidalClosed.curry (whiskerLeft_snd _ _).symm

private theorem conjugateEquiv_faceNerveGrayTensorFst (S : SSet.{u}) :
    conjugateEquiv faceNerveSSetAdjunction (grayHomFaceNerveAdjunction S)
        (faceNerveGrayTensorFst S) =
      Functor.whiskerLeft faceNerveRight (Functor.whiskerRight
        (grayConstDiagramNatTrans (SSet.toDiagSet.obj S)) DiagSet.toSSet) := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ fun A C f => ?_
  have e : faceNerveAdjunction.homEquiv _ C ((faceNerveGrayTensorFst S).app A ≫ f) =
      grayTensorFst (SSet.toDiagSet.obj A) (SSet.toDiagSet.obj S) ≫
        faceNerveAdjunction.homEquiv _ C f :=
    faceNerveAdjunction.homEquiv_naturality_left _ f
  have e₂ : (grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv _ _
      (grayTensorFst (SSet.toDiagSet.obj A) (SSet.toDiagSet.obj S) ≫
        faceNerveAdjunction.homEquiv _ C f) =
      faceNerveAdjunction.homEquiv _ C f ≫
        constDiagram (SSet.toDiagSet.obj S) (faceNerveRight.obj C) :=
    (congrArg ((grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv _ _)
      (grayTensorRight_map_grayTensorFst (faceNerveAdjunction.homEquiv _ C f) _).symm).trans
      ((grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv_naturality_left _ _)
  refine (grayHomFaceNerveAdjunction_homEquiv S A C _).trans (Eq.trans ?_
    (congrArg (· ≫ _) (faceNerveSSetAdjunction_homEquiv A C f).symm))
  exact (congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _) ((congrArg
    ((DiagSet.Infty.grayTensorRightAdjunction 1 (SSet.toDiagSet.obj S)).homEquiv _ _) e).trans
      e₂)).trans (DiagSet.Infty.sSetDiagSetAdj.homEquiv_naturality_right _ _)

@[reassoc]
theorem constDiagram_comp_grayHomSimplicialComparison_app (S : SSet.{u}) (C : MarkedSSet.{u}) :
    SSet.constDiagram S ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        (grayHomSimplicialComparison S).app C =
      faceNerveRightComparison.app C ≫
        DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj S) (faceNerveRight.obj C)) := by
  have h₁ := conjugateEquiv_comp (MarkedPresheaf.flatForgetAdjunction edgeMarking)
    (flatTensorLeftAdjunction S) (grayHomFaceNerveAdjunction S) (flatTensorLeftSnd S)
    (faceNerveGrayTensorFlat S)
  have h₂ := conjugateEquiv_comp (MarkedPresheaf.flatForgetAdjunction edgeMarking)
    faceNerveSSetAdjunction (grayHomFaceNerveAdjunction S) faceNerveToDiagSetFlat
    (faceNerveGrayTensorFst S)
  have h := congrArg (conjugateEquiv (MarkedPresheaf.flatForgetAdjunction edgeMarking)
    (grayHomFaceNerveAdjunction S)) (faceNerveGrayTensorFlat_comp_flatTensorLeftSnd S)
  have k := congrArg (fun t => t.app C) (h₁.trans (h.trans h₂.symm))
  exact (congrArg (· ≫ (grayHomSimplicialComparison S).app C)
    (NatTrans.congr_app (conjugateEquiv_flatTensorLeftSnd S) C).symm).trans
      (k.trans (congrArg (faceNerveRightComparison.app C ≫ ·)
        (NatTrans.congr_app (conjugateEquiv_faceNerveGrayTensorFst S) C)))

section Zigzag

variable (S : SSet.{u}) {Y Y' : DiagSet.{u}} {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C']

private theorem isFibrant_faceNerveRight_obj (C : MarkedSSet.{u}) [IsFibrant C] :
    IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
  isQuillen_faceNerveAdjunction.isFibrant_obj C

theorem weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory (T : DiagSet.{u})
    {X Y : DiagSet.{u}} (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (f : X ⟶ Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map f)] :
    WeakEquivalence (DiagSet.toSSet.map ((grayHomRight T).map f)) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  (isQuillen_sSetDiagSetAdj.comp (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one
    T)).weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map f)

theorem weakEquivalence_toSSet_map_grayHomRight_map (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η)) :=
  weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory _ hY
    (isInftyCategory_faceNerveRight_obj C) η

theorem weakEquivalence_ihom_map_toSSet_map (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence ((ihom S).map (DiagSet.toSSet.map η)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  have : IsFibrant (DiagSet.toSSet.obj Y) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj Y)
  have : IsFibrant (DiagSet.toSSet.obj (faceNerveRight.obj C)) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))
  have : WeakEquivalence (DiagSet.toSSet.map η) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map η)
  exact weakEquivalence_ihom_map S (DiagSet.toSSet.map η)

theorem weakEquivalence_ihom_map_faceNerveRightComparison_app (C : MarkedSSet.{u})
    [IsFibrant C] : WeakEquivalence ((ihom S).map (faceNerveRightComparison.app C)) := by
  have := isFibrant_faceNerveRight_obj C
  have : IsFibrant ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))
  have : IsFibrant ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C
  have := weakEquivalence_faceNerveRightComparison_app C
  exact weakEquivalence_ihom_map S (faceNerveRightComparison.app C)

variable {H : Type*} [Category* H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

noncomputable def grayHomSimplicialIso (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.obj (DiagSet.toSSet.obj ((grayHomRight (SSet.toDiagSet.obj S)).obj Y)) ≅
      L.obj ((ihom S).obj (DiagSet.toSSet.obj Y)) :=
  Localization.isoOfHom L (weakEquivalences _)
      (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η))
      ((weakEquivalence_iff _).1 (weakEquivalence_toSSet_map_grayHomRight_map S hY η)) ≪≫
    (Localization.isoOfHom L (weakEquivalences _) ((grayHomSimplicialComparison S).app C)
      ((weakEquivalence_iff _).1 (weakEquivalence_grayHomSimplicialComparison_app S C))).symm ≪≫
    Localization.isoOfHom L (weakEquivalences _) ((ihom S).map (faceNerveRightComparison.app C))
      ((weakEquivalence_iff _).1 (weakEquivalence_ihom_map_faceNerveRightComparison_app S C)) ≪≫
    (Localization.isoOfHom L (weakEquivalences _) ((ihom S).map (DiagSet.toSSet.map η))
      ((weakEquivalence_iff _).1 (weakEquivalence_ihom_map_toSSet_map S hY η))).symm

theorem grayHomSimplicialIso_hom_naturality_of_comp_eq (hY : IsInftyCategory 1 Y)
    (hY' : IsInftyCategory 1 Y') (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y' ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] (g : Y ⟶ Y') (c : C ⟶ C')
    (h : η ≫ faceNerveRight.map c = g ≫ η') :
    L.map (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map g)) ≫
        (grayHomSimplicialIso S L hY' η').hom =
      (grayHomSimplicialIso S L hY η).hom ≫ L.map ((ihom S).map (DiagSet.toSSet.map g)) := by
  have h₁ : DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η) ≫
      DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRight.map c)) =
      DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map g) ≫
        DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η') := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DiagSet.toSSet.map (((grayHomRight _).map_comp _ _).symm.trans
      ((congrArg (grayHomRight _).map h).trans ((grayHomRight _).map_comp _ _)))
  have h₂ : (grayHomSimplicialComparison S).app C ≫
      DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRight.map c)) =
      (ihom S).map ((MarkedPresheaf.forget (D := edgeMarking)).map c) ≫
        (grayHomSimplicialComparison S).app C' :=
    ((grayHomSimplicialComparison S).naturality c).symm
  have h₃ : (ihom S).map (faceNerveRightComparison.app C) ≫
      (ihom S).map (DiagSet.toSSet.map (faceNerveRight.map c)) =
      (ihom S).map ((MarkedPresheaf.forget (D := edgeMarking)).map c) ≫
        (ihom S).map (faceNerveRightComparison.app C') := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (ihom S).map (faceNerveRightComparison.naturality c).symm
  have h₄ : (ihom S).map (DiagSet.toSSet.map η) ≫
      (ihom S).map (DiagSet.toSSet.map (faceNerveRight.map c)) =
      (ihom S).map (DiagSet.toSSet.map g) ≫ (ihom S).map (DiagSet.toSSet.map η') := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (ihom S).map ((DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map h).trans (DiagSet.toSSet.map_comp _ _)))
  dsimp only [grayHomSimplicialIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom, Category.assoc]
  rw [← L.map_comp_assoc, ← h₁, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv_assoc L _ _ _ _ _ _ _ h₂, ← L.map_comp_assoc, ← h₃,
    L.map_comp_assoc, Localization.map_comp_isoOfHom_inv L _ _ _ _ _ _ _ h₄]

theorem grayHomSimplicialIso_eq (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] :
    grayHomSimplicialIso S L hY η = grayHomSimplicialIso S L hY η' := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight Y
  have key (C₁ : MarkedSSet.{u}) [IsFibrant C₁] (η₁ : Y ⟶ faceNerveRight.obj C₁)
      [WeakEquivalence ((DiagSet.toInfty 1).map η₁)] :
      grayHomSimplicialIso S L hY η₀ = grayHomSimplicialIso S L hY η₁ := by
    obtain ⟨c, hc⟩ := hη₀ C₁ η₁
    refine Iso.ext ?_
    have h := grayHomSimplicialIso_hom_naturality_of_comp_eq S L hY hY η₀ η₁ (𝟙 Y) c
      (hc.trans (Category.id_comp η₁).symm)
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm
  exact (key C η).symm.trans (key C' η')

theorem grayHomSimplicialIso_hom_naturality (hY : IsInftyCategory 1 Y)
    (hY' : IsInftyCategory 1 Y') (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y' ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] (g : Y ⟶ Y') :
    L.map (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map g)) ≫
        (grayHomSimplicialIso S L hY' η').hom =
      (grayHomSimplicialIso S L hY η).hom ≫ L.map ((ihom S).map (DiagSet.toSSet.map g)) := by
  obtain ⟨C₀, _, η₀, _, hη₀⟩ := exists_weakEquivalence_faceNerveRight Y
  obtain ⟨c, hc⟩ := hη₀ C' (g ≫ η')
  rw [grayHomSimplicialIso_eq S L hY η η₀]
  exact grayHomSimplicialIso_hom_naturality_of_comp_eq S L hY hY' η₀ η' g c hc

theorem grayHomRestrict_comp_grayHomSimplicialIso_hom {S' : SSet.{u}} (s : S ⟶ S')
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map s)).app Y)) ≫
        (grayHomSimplicialIso S L hY η).hom =
      (grayHomSimplicialIso S' L hY η).hom ≫
        L.map ((MonoidalClosed.pre s).app (DiagSet.toSSet.obj Y)) := by
  have h₁ : DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S')).map η) ≫
      DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map s)).app (faceNerveRight.obj C)) =
      DiagSet.toSSet.map ((grayHomRestrict (SSet.toDiagSet.map s)).app Y) ≫
        DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η) := by
    rw [← Functor.map_comp, ← Functor.map_comp, (grayHomRestrict _).naturality]
  have h₂ := (pre_app_comp_grayHomSimplicialComparison_app s C).symm
  have h₃ : (ihom S').map (faceNerveRightComparison.app C) ≫
      (MonoidalClosed.pre s).app (DiagSet.toSSet.obj (faceNerveRight.obj C)) =
      (MonoidalClosed.pre s).app ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
        (ihom S).map (faceNerveRightComparison.app C) :=
    (MonoidalClosed.pre s).naturality _
  have h₄ := (MonoidalClosed.pre s).naturality (DiagSet.toSSet.map η)
  dsimp only [grayHomSimplicialIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom, Category.assoc]
  rw [← L.map_comp_assoc, ← h₁, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv_assoc L _ _ _ _ _ _ _ h₂, ← L.map_comp_assoc, ← h₃,
    L.map_comp_assoc, Localization.map_comp_isoOfHom_inv L _ _ _ _ _ _ _ h₄]

theorem constDiagram_comp_grayHomSimplicialIso_hom (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj S) Y)) ≫
        (grayHomSimplicialIso S L hY η).hom =
      L.map (SSet.constDiagram S (DiagSet.toSSet.obj Y)) := by
  have h₁ : DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj S) Y) ≫
      DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map η) =
      DiagSet.toSSet.map η ≫
        DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj S) (faceNerveRight.obj C)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, constDiagram_naturality]
  have h₂ := (constDiagram_comp_grayHomSimplicialComparison_app S C).symm
  have h₃ : SSet.constDiagram S ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ≫
      (ihom S).map (faceNerveRightComparison.app C) = faceNerveRightComparison.app C ≫
        SSet.constDiagram S (DiagSet.toSSet.obj (faceNerveRight.obj C)) :=
    SSet.constDiagram_comp_ihom_map _ S
  have h₄ := SSet.constDiagram_comp_ihom_map (DiagSet.toSSet.map η) S
  dsimp only [grayHomSimplicialIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom]
  rw [← L.map_comp_assoc, h₁, L.map_comp_assoc,
    Localization.map_comp_isoOfHom_inv_assoc L _ _ ((weakEquivalence_iff _).1
      (weakEquivalence_faceNerveRightComparison_app C)) _ _ _ _ h₂,
    ← L.map_comp_assoc, h₃, L.map_comp_assoc, Localization.isoOfHom_inv_hom_id_assoc,
    ← L.map_comp_assoc, ← h₄, L.map_comp_assoc, Localization.isoOfHom_hom_inv_id,
    Category.comp_id]

end Zigzag

noncomputable def pointIsoToDiagSetStdSimplex : ball.{u} atomPoint ≅ SSet.toDiagSet.obj Δ[0] :=
  uliftYoneda.mapIso atomSimplexZeroIsoPoint.symm ≪≫ (toDiagSetObjStdSimplexIso 0).symm

noncomputable def grayHomEvalVertex {S : SSet.{u}} (a : S _⦋0⦌) (Y : DiagSet.{u}) :
    (grayHomRight (SSet.toDiagSet.obj S)).obj Y ⟶ Y :=
  (grayHomRestrict (pointIsoToDiagSetStdSimplex.hom ≫
    SSet.toDiagSet.map (SSet.yonedaEquiv.symm a))).app Y ≫ grayHomRightPointIso.hom.app Y

private theorem constDiagram_comp_grayHomRestrict_pointIso (Y : DiagSet.{u}) :
    constDiagram (SSet.toDiagSet.obj Δ[0]) Y ≫
        ((grayHomRestrict pointIsoToDiagSetStdSimplex.{u}.hom).app Y ≫
          grayHomRightPointIso.hom.app Y) = 𝟙 Y := by
  rw [← Category.assoc, constDiagram_comp_grayHomRestrict,
    constDiagram_comp_grayHomRightPointIso_hom_app]

instance isIso_grayHomRestrict_app {A B : DiagSet.{u}} (i : A ⟶ B) [IsIso i] (Y : DiagSet.{u}) :
    IsIso ((grayHomRestrict i).app Y) :=
  ⟨⟨(grayHomRestrict (inv i)).app Y,
    by rw [← NatTrans.comp_app, ← grayHomRestrict_comp, IsIso.inv_hom_id, grayHomRestrict_id,
      NatTrans.id_app],
    by rw [← NatTrans.comp_app, ← grayHomRestrict_comp, IsIso.hom_inv_id, grayHomRestrict_id,
      NatTrans.id_app]⟩⟩

section Evaluation

variable {S : SSet.{u}} {Y : DiagSet.{u}} {C : MarkedSSet.{u}} [IsFibrant C]
  {H : Type*} [Category* H] (L : SSet.{u} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{u})]

theorem grayHomSimplicialIso_hom_evalVertex (a : S _⦋0⦌) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (grayHomSimplicialIso S L hY η).hom ≫ L.map (SSet.evalVertex a (DiagSet.toSSet.obj Y)) =
      L.map (DiagSet.toSSet.map (grayHomEvalVertex a Y)) := by
  have ha : SSet.evalVertex a (DiagSet.toSSet.obj Y) =
      (MonoidalClosed.pre (SSet.yonedaEquiv.symm a)).app _ ≫
        SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) _ := by
    rw [SSet.pre_app_comp_evalVertex, SSet.yonedaEquiv_symm_app_id]
  let u := DiagSet.toSSet.map ((grayHomRestrict pointIsoToDiagSetStdSimplex.{u}.hom).app Y ≫
    grayHomRightPointIso.hom.app Y)
  have hcu : L.map (DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj Δ[0]) Y)) ≫ L.map u =
      𝟙 _ := by
    rw [← L.map_comp, ← Functor.map_comp, constDiagram_comp_grayHomRestrict_pointIso,
      CategoryTheory.Functor.map_id, L.map_id]
  have : IsIso (L.map (DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj Δ[0]) Y))) := by
    have : IsIso (L.map (DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj Δ[0]) Y)) ≫
        L.map u) := by
      rw [hcu]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (L.map u)
  have key : (grayHomSimplicialIso Δ[0] L hY η).hom ≫
      L.map (SSet.evalVertex (SSet.yonedaEquiv (𝟙 Δ[0])) (DiagSet.toSSet.obj Y)) = L.map u := by
    rw [← cancel_epi (L.map (DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj Δ[0]) Y))),
      ← Category.assoc, constDiagram_comp_grayHomSimplicialIso_hom Δ[0] L hY η, ← L.map_comp,
      SSet.constDiagram_comp_evalVertex, L.map_id, hcu]
  rw [ha, L.map_comp, ← Category.assoc,
    ← grayHomRestrict_comp_grayHomSimplicialIso_hom Δ[0] L (SSet.yonedaEquiv.symm a) hY η,
    Category.assoc, key, ← L.map_comp, ← Functor.map_comp, grayHomEvalVertex, ← Category.assoc,
    ← NatTrans.comp_app, ← grayHomRestrict_comp]

end Evaluation

section Span

variable (S : SSet.{u}) {Y : DiagSet.{u}} {C : MarkedSSet.{u}} [IsFibrant C]

noncomputable def faceNerveRightHomotopyInv (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    faceNerveRight.obj C ⟶ Y :=
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  (RightHomotopyClass.whitehead ((DiagSet.toInfty 1).map η)).choose

private theorem faceNerveRightHomotopyInv_spec (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    RightHomotopyRel ((DiagSet.toInfty 1).map (η ≫ faceNerveRightHomotopyInv hY η))
        (𝟙 ((DiagSet.toInfty 1).obj Y)) ∧
      RightHomotopyRel ((DiagSet.toInfty 1).map (faceNerveRightHomotopyInv hY η ≫ η))
        (𝟙 ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))) :=
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  (RightHomotopyClass.whitehead ((DiagSet.toInfty 1).map η)).choose_spec

private theorem weakEquivalence_faceNerveRightHomotopyInv (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence ((DiagSet.toInfty 1).map (faceNerveRightHomotopyInv hY η)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  obtain ⟨h₁, h₂⟩ := faceNerveRightHomotopyInv_spec hY η
  exact weakEquivalence_of_rightHomotopyRel _ ((DiagSet.toInfty 1).map η) h₂ h₁

noncomputable def grayHomSimplicialSpanLeft (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (ihom S).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj ((grayHomRight (SSet.toDiagSet.obj S)).obj Y) :=
  (grayHomSimplicialComparison S).app C ≫
    DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRightHomotopyInv hY η))

noncomputable def grayHomSimplicialSpanRight (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (ihom S).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      (ihom S).obj (DiagSet.toSSet.obj Y) :=
  (ihom S).map
    (faceNerveRightComparison.app C ≫ DiagSet.toSSet.map (faceNerveRightHomotopyInv hY η))

theorem weakEquivalence_grayHomSimplicialSpanLeft (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (grayHomSimplicialSpanLeft S hY η) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  have := weakEquivalence_faceNerveRightHomotopyInv hY η
  have := weakEquivalence_grayHomSimplicialComparison_app S C
  have : WeakEquivalence (DiagSet.toSSet.map
      ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRightHomotopyInv hY η))) :=
    (isQuillen_sSetDiagSetAdj.comp (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one
      (SSet.toDiagSet.obj S))).weakEquivalence_map_of_isFibrant
        ((DiagSet.toInfty 1).map (faceNerveRightHomotopyInv hY η))
  dsimp only [grayHomSimplicialSpanLeft]
  infer_instance

theorem weakEquivalence_grayHomSimplicialSpanRight (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (grayHomSimplicialSpanRight S hY η) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have := isFibrant_faceNerveRight_obj C
  have := weakEquivalence_faceNerveRightHomotopyInv hY η
  have := weakEquivalence_faceNerveRightComparison_app C
  have : IsFibrant (DiagSet.toSSet.obj Y) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj Y)
  have : IsFibrant (DiagSet.toSSet.obj (faceNerveRight.obj C)) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))
  have : IsFibrant ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C
  have : WeakEquivalence (DiagSet.toSSet.map (faceNerveRightHomotopyInv hY η)) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map (faceNerveRightHomotopyInv hY η))
  have : WeakEquivalence (faceNerveRightComparison.app C ≫
      DiagSet.toSSet.map (faceNerveRightHomotopyInv hY η)) := inferInstance
  exact weakEquivalence_ihom_map S _

variable {H : Type*} [Category* H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

theorem grayHomSimplicialSpanLeft_comp_grayHomSimplicialIso_hom (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (grayHomSimplicialSpanLeft S hY η) ≫ (grayHomSimplicialIso S L hY η).hom =
      L.map (grayHomSimplicialSpanRight S hY η) := by
  have := isFibrant_faceNerveRight_obj C
  have h₂ := (faceNerveRightHomotopyInv_spec hY η).2
  have hP : L.map (DiagSet.toSSet.map ((grayHomRight (SSet.toDiagSet.obj S)).map
      (faceNerveRightHomotopyInv hY η ≫ η))) = 𝟙 _ := by
    have hh := (isQuillen_sSetDiagSetAdj.comp (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one
      (SSet.toDiagSet.obj S))).rightHomotopyRel_map h₂
    have e := (areEqualizedByLocalization_iff L (weakEquivalences _) _ _).1
      (RightHomotopyRel.factorsThroughLocalization _ hh)
    simp only [CategoryTheory.Functor.map_id] at e
    exact e
  have hR : L.map ((ihom S).map (DiagSet.toSSet.map (faceNerveRightHomotopyInv hY η ≫ η))) =
      𝟙 _ := by
    have : IsFibrant (DiagSet.Infty.toSSet.obj ((DiagSet.toInfty 1).obj (faceNerveRight.obj C))) :=
      isQuillen_sSetDiagSetAdj.isFibrant_obj _
    have hh := (isQuillen_ihomAdjunction S).rightHomotopyRel_map
      (isQuillen_sSetDiagSetAdj.rightHomotopyRel_map h₂)
    have e := (areEqualizedByLocalization_iff L (weakEquivalences _) _ _).1
      (RightHomotopyRel.factorsThroughLocalization _ hh)
    simp only [CategoryTheory.Functor.map_id] at e
    exact e
  have k : L.map ((ihom S).map (DiagSet.toSSet.map (faceNerveRightHomotopyInv hY η))) =
      (Localization.isoOfHom L (weakEquivalences _) ((ihom S).map (DiagSet.toSSet.map η))
        ((weakEquivalence_iff _).1 (weakEquivalence_ihom_map_toSSet_map S hY η))).inv := by
    refine (cancel_mono (Localization.isoOfHom L (weakEquivalences _)
      ((ihom S).map (DiagSet.toSSet.map η))
        ((weakEquivalence_iff _).1 (weakEquivalence_ihom_map_toSSet_map S hY η))).hom).1 ?_
    rw [Iso.inv_hom_id, Localization.isoOfHom_hom, ← L.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, hR]
  dsimp only [grayHomSimplicialSpanLeft, grayHomSimplicialSpanRight, grayHomSimplicialIso,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Localization.isoOfHom_hom]
  rw [L.map_comp, Category.assoc, ← L.map_comp_assoc (DiagSet.toSSet.map
      ((grayHomRight (SSet.toDiagSet.obj S)).map (faceNerveRightHomotopyInv hY η))),
    ← Functor.map_comp, ← Functor.map_comp, hP, Category.id_comp,
    Localization.isoOfHom_hom_inv_id_assoc, ← k,
    ← L.map_comp, ← Functor.map_comp]

end Span

open SSet.modelCategoryJoyal in
theorem grayHomLComparison_exists (S : SSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj
      ((grayHomRight (SSet.toDiagSet.obj S)).obj Y))
      (r : Z ⟶ (ihom S).obj (DiagSet.toSSet.obj Y)),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨C, _, η, _, -⟩ := exists_weakEquivalence_faceNerveRight Y
  exact ⟨_, _, _, weakEquivalence_grayHomSimplicialSpanLeft S hY η,
    weakEquivalence_grayHomSimplicialSpanRight S hY η⟩

private theorem conjugateEquiv_grayTensorRight_map {A B : DiagSet.{u}} (i : A ⟶ B) :
    conjugateEquiv (grayTensorRightAdjunction B) (grayTensorRightAdjunction A)
      ((Functor.curry.obj grayTensorBifunctor).flip.map i) = grayHomRestrict i :=
  conjugateEquiv_eq_of_homEquiv _ _ _ _ fun _ _ f => (homEquiv_comp_grayHomRestrict i f).symm

theorem weakEquivalence_grayHomRestrict_app {A B : DiagSet.{u}} (i : A ⟶ B)
    [WeakEquivalence ((DiagSet.toInfty 1).map i)] {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRestrict i).app Y)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have h := Adjunction.IsQuillen.weakEquivalence_conjugateEquiv_app
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one B)
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one A)
    ((Functor.curry.obj grayTensorBifunctor).flip.map i)
    (fun T _ => (DiagSet.Infty.isQuillen_grayTensorLeftAdjunction_one T).weakEquivalence_map
      ((DiagSet.toInfty 1).map i)) ((DiagSet.toInfty 1).obj Y)
  have e : (conjugateEquiv (DiagSet.Infty.grayTensorRightAdjunction 1 B)
      (DiagSet.Infty.grayTensorRightAdjunction 1 A)
        ((Functor.curry.obj grayTensorBifunctor).flip.map i)).app ((DiagSet.toInfty 1).obj Y) =
      (DiagSet.toInfty 1).map ((grayHomRestrict i).app Y) :=
    NatTrans.congr_app (conjugateEquiv_grayTensorRight_map i) Y
  rw [e] at h
  exact h

noncomputable def isTerminalToSSetBallAtomPoint :
    IsTerminal (DiagSet.toSSet.obj (ball.{u} atomPoint)) :=
  isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _

private theorem ihomPointEquiv_comp_constDiagram {Q : SSet.{u}} (g : Δ[0] ⟶ Q) :
    SSet.ihomPointEquiv Δ[0] Q (g ≫ SSet.constDiagram Δ[0] Q) = g := by
  have h := SSet.comp_evalVertex_eq (g ≫ SSet.constDiagram Δ[0] Q) (SSet.yonedaEquiv (𝟙 _))
  rw [Category.assoc, SSet.constDiagram_comp_evalVertex, Category.comp_id, Equiv.symm_apply_apply,
    Category.id_comp] at h
  exact h.symm

@[reassoc]
theorem comp_grayHomSimplicialComparison_app_grayHomEvalVertex (C : MarkedSSet.{u})
    {S : SSet.{u}}
    (b : Δ[0] ⟶ (ihom S).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) (a : S _⦋0⦌) :
    b ≫ (grayHomSimplicialComparison S).app C ≫
        DiagSet.toSSet.map (grayHomEvalVertex a (faceNerveRight.obj C)) =
      (SSet.yonedaEquiv.symm a ≫ SSet.ihomPointEquiv S _ b) ≫ faceNerveRightComparison.app C := by
  have hb : b ≫ (MonoidalClosed.pre (SSet.yonedaEquiv.symm a)).app _ =
      (SSet.yonedaEquiv.symm a ≫ SSet.ihomPointEquiv S _ b) ≫ SSet.constDiagram Δ[0] _ :=
    (SSet.ihomPointEquiv Δ[0] _).injective ((SSet.ihomPointEquiv_comp_pre_app _ _).trans
      (ihomPointEquiv_comp_constDiagram _).symm)
  have hc : constDiagram (SSet.toDiagSet.obj Δ[0]) (faceNerveRight.obj C) ≫
      ((grayHomRestrict pointIsoToDiagSetStdSimplex.{u}.hom).app _ ≫
        grayHomRightPointIso.hom.app _) = 𝟙 _ := by
    rw [← Category.assoc, constDiagram_comp_grayHomRestrict,
      constDiagram_comp_grayHomRightPointIso_hom_app]
  rw [grayHomEvalVertex, grayHomRestrict_comp, NatTrans.comp_app, Category.assoc,
    Functor.map_comp, ← pre_app_comp_grayHomSimplicialComparison_app_assoc, reassoc_of% hb,
    constDiagram_comp_grayHomSimplicialComparison_app_assoc, ← Functor.map_comp, hc,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]

private theorem faceNerveGrayTensorFlat_app_comp_flat_map_fst (S K : SSet.{u}) :
    (faceNerveGrayTensorFlat S).app K ≫
        (MarkedPresheaf.flat edgeMarking).map (fst S K) =
      faceNerve.map (grayTensorSnd (SSet.toDiagSet.obj K) (SSet.toDiagSet.obj S)) ≫
        faceNerveToDiagSetFlat.app S := by
  have e : (SSet.flatTensorIso S K).inv ≫
      (MarkedPresheaf.flat edgeMarking).map (fst S K) = fst _ _ :=
    MarkedPresheaf.hom_ext rfl
  rw [faceNerveGrayTensorFlat, Category.assoc, e, lift_fst]

theorem grayHomSimplicialComparison_app_point (S : SSet.{u}) (C : MarkedSSet.{u})
    (b : Δ[0] ⟶ (ihom S).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _
        ((grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv _ _
          (grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj S) ≫
            (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
              (SSet.ihomPointEquiv S _ b ≫ faceNerveRightComparison.app C))) =
      b ≫ (grayHomSimplicialComparison S).app C := by
  let q := SSet.ihomPointEquiv S _ b
  let g := ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv S C).symm q
  have hq := homEquiv_conjugateEquiv_app
    (MarkedPresheaf.flatForgetAdjunction edgeMarking) faceNerveSSetAdjunction
    faceNerveToDiagSetFlat g
  rw [Equiv.apply_symm_apply] at hq
  have hb : (flatTensorLeftAdjunction S).homEquiv Δ[0] C
      ((MarkedPresheaf.flat edgeMarking).map (fst S Δ[0]) ≫ g) = b := by
    rw [flatTensorLeftAdjunction_homEquiv,
      (MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv_naturality_left,
      Equiv.apply_symm_apply]
    exact (SSet.ihomPointEquiv S _).symm_apply_apply b
  have h := homEquiv_conjugateEquiv_app (flatTensorLeftAdjunction S)
    (grayHomFaceNerveAdjunction S) (faceNerveGrayTensorFlat S)
    ((MarkedPresheaf.flat edgeMarking).map (fst S Δ[0]) ≫ g)
  rw [hb] at h
  have ht := congrArg (· ≫ g) (faceNerveGrayTensorFlat_app_comp_flat_map_fst S Δ[0])
  have hh := congrArg ((grayHomFaceNerveAdjunction S).homEquiv Δ[0] C) ht
  have h' := hh.symm.trans ((congrArg ((grayHomFaceNerveAdjunction S).homEquiv Δ[0] C)
    (Category.assoc _ _ _).symm).trans h)
  rw [Category.assoc] at h'
  have e : faceNerveAdjunction.homEquiv _ C (faceNerveToDiagSetFlat.app S ≫ g) =
      (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
        (q ≫ faceNerveRightComparison.app C) := by
    apply (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).injective
    exact ((faceNerveSSetAdjunction_homEquiv S C _).symm.trans hq).trans
      ((DiagSet.Infty.sSetDiagSetAdj.homEquiv S (faceNerveRight.obj C)).apply_symm_apply _).symm
  have hn : faceNerveAdjunction.homEquiv _ C
      (faceNerve.map (grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj S)) ≫
        faceNerveToDiagSetFlat.app S ≫ g) =
      grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj S) ≫
        faceNerveAdjunction.homEquiv _ C (faceNerveToDiagSetFlat.app S ≫ g) :=
    faceNerveAdjunction.homEquiv_naturality_left _ _
  have hn' := hn.trans (congrArg
    (grayTensorSnd (SSet.toDiagSet.obj Δ[0]) (SSet.toDiagSet.obj S) ≫ ·) e)
  exact (congrArg (fun t => DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _
    ((grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv _ _ t)) hn').symm.trans
      ((grayHomFaceNerveAdjunction_homEquiv S Δ[0] C _).symm.trans h')

theorem grayHomSimplicialComparison_app_vertex (S : SSet.{u}) (C : MarkedSSet.{u})
    (b : ((ihom S).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) _⦋0⦌) :
    grayHomRightCellEquiv (SSet.toDiagSet.obj S) (faceNerveRight.obj C) (atomSimplex 0)
        (((grayHomSimplicialComparison S).app C).app (Opposite.op ⦋0⦌) b) =
      grayTensorSnd (ball (atomSimplex 0)) (SSet.toDiagSet.obj S) ≫
        (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
          (SSet.ihomPointEquiv S _ (SSet.yonedaEquiv.symm b) ≫
            faceNerveRightComparison.app C) := by
  have h := congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
    (grayHomSimplicialComparison_app_point S C (SSet.yonedaEquiv.symm b))
  have h' := ((DiagSet.Infty.sSetDiagSetAdj.homEquiv Δ[0]
    ((grayHomRight (SSet.toDiagSet.obj S)).obj
      (faceNerveRight.obj C))).symm_apply_apply _).symm.trans h
  rw [SSet.yonedaEquiv_symm_comp] at h'
  have h'' := h'.trans (homEquiv_symm_yonedaEquiv_symm
    (((grayHomSimplicialComparison S).app C).app _ b))
  have hp := congrArg (uliftYonedaEquiv ∘ ((toDiagSetObjStdSimplexIso 0).inv ≫ ·)) h''
  dsimp only [Function.comp_apply] at hp
  rw [Iso.inv_hom_id_assoc] at hp
  have hp' := hp.trans (uliftYonedaEquiv.apply_symm_apply _)
  refine (congrArg (grayHomRightCellEquiv (SSet.toDiagSet.obj S)
    (faceNerveRight.obj C) (atomSimplex 0)) hp'.symm).trans ?_
  let B := SSet.toDiagSet.obj S
  let T := SSet.toDiagSet.obj Δ[0]
  let g : SSet.toDiagSet.obj S ⟶ faceNerveRight.obj C :=
    (DiagSet.Infty.sSetDiagSetAdj.homEquiv _ _).symm
      (SSet.ihomPointEquiv S _ (SSet.yonedaEquiv.symm b) ≫ faceNerveRightComparison.app C)
  let F : grayTensor T B ⟶ faceNerveRight.obj C := grayTensorSnd T B ≫ g
  let t := (grayTensorRightAdjunction B).homEquiv T (faceNerveRight.obj C) F
  let a : diagram T (atomSimplex 0) := uliftYonedaEquiv (toDiagSetObjStdSimplexIso 0).inv
  refine (congrArg (grayHomRightCellEquiv B (faceNerveRight.obj C) (atomSimplex 0))
    (uliftYonedaEquiv_comp (toDiagSetObjStdSimplexIso 0).inv t)).trans ?_
  refine (grayHomRightCellEquiv_homEquiv_app B T (faceNerveRight.obj C) F
    (atomSimplex 0) a).trans ?_
  have e := congrArg (fun f => (grayTensorRight B).map f ≫ F)
    (uliftYonedaEquiv.symm_apply_apply (toDiagSetObjStdSimplexIso 0).inv)
  exact e.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ g) (grayTensorRight_map_grayTensorSnd
      (toDiagSetObjStdSimplexIso 0).inv B)))

end Atoms.Diagrammatic
