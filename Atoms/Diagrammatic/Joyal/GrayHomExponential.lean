import Atoms.Diagrammatic.Adjunction.Transformation
import Atoms.Diagrammatic.Joyal.GrayHomComparison

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory Simplicial
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

noncomputable abbrev sSetDiagSetCounit (X : DiagSet.{u}) :
    SSet.toDiagSet.obj (DiagSet.toSSet.obj X) ⟶ X :=
  sSetDiagSetAdj.counit.app X

section Infty

variable {X X' Y Y' : DiagSet.{u}} {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C']

private theorem isFibrant_toSSet_grayHomRight_counit (hY : IsInftyCategory 1 Y) :
    IsFibrant (DiagSet.toSSet.obj ((grayHomRight X).obj Y)) ∧
      IsFibrant (DiagSet.toSSet.obj
        ((grayHomRight (SSet.toDiagSet.obj (DiagSet.toSSet.obj X))).obj Y)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight X).obj Y)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one X).isFibrant_obj
      ((DiagSet.toInfty 1).obj Y)
  have : IsFibrant ((DiagSet.toInfty 1).obj
      ((grayHomRight (SSet.toDiagSet.obj (DiagSet.toSSet.obj X))).obj Y)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one _).isFibrant_obj
      ((DiagSet.toInfty 1).obj Y)
  exact ⟨isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj ((grayHomRight X).obj Y)),
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj
      ((grayHomRight (SSet.toDiagSet.obj (DiagSet.toSSet.obj X))).obj Y))⟩

theorem weakEquivalence_toSSet_map_grayHomRestrict_counit_app (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) :
    WeakEquivalence
      (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y)) := by
  have : WeakEquivalence ((DiagSet.toInfty 1).map (sSetDiagSetCounit X)) :=
    weakEquivalence_sSetDiagSetAdj_counit_app ((DiagSet.toInfty 1).obj X)
      ((isFibrant_infty_iff 1 _).2 hX)
  have := weakEquivalence_grayHomRestrict_app (sSetDiagSetCounit X) hY
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight X).obj Y)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one X).isFibrant_obj
      ((DiagSet.toInfty 1).obj Y)
  have : IsFibrant ((DiagSet.toInfty 1).obj
      ((grayHomRight (SSet.toDiagSet.obj (DiagSet.toSSet.obj X))).obj Y)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one _).isFibrant_obj
      ((DiagSet.toInfty 1).obj Y)
  exact isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant
    ((DiagSet.toInfty 1).map ((grayHomRestrict (sSetDiagSetCounit X)).app Y))

theorem grayHomRestrict_counit_app_comp_grayHomEvalVertex (x : (DiagSet.toSSet.obj X) _⦋0⦌)
    (Y : DiagSet.{u}) :
    (grayHomRestrict (sSetDiagSetCounit X)).app Y ≫ grayHomEvalVertex x Y =
      grayHomEval x Y := by
  have h₁ : SSet.toDiagSet.map (SSet.yonedaEquiv.symm x) ≫ sSetDiagSetCounit X =
      (toDiagSetObjStdSimplexIso 0).hom ≫ uliftYonedaEquiv.symm x :=
    (sSetDiagSetAdj.homEquiv_counit _ _ _).symm.trans (homEquiv_symm_yonedaEquiv_symm x)
  have h : pointIsoToDiagSetStdSimplex.hom ≫ SSet.toDiagSet.map (SSet.yonedaEquiv.symm x) ≫
      sSetDiagSetCounit X = vertexHom x := by
    rw [h₁, pointIsoToDiagSetStdSimplex, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, Functor.mapIso_hom, Iso.symm_hom, atomSimplexZeroIsoPoint, Iso.refl_inv]
    have e : (uliftYoneda.{u} (C := Atom)).map (𝟙 (atomSimplex 0)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    exact (congrArg (· ≫ _) e).trans (Category.id_comp _)
  dsimp only [grayHomEval]
  rw [grayHomEvalVertex, ← Category.assoc, ← NatTrans.comp_app, ← grayHomRestrict_comp,
    Category.assoc, h]

variable {H : Type*} [Category* H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

noncomputable def grayHomComparisonIso (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.obj (DiagSet.toSSet.obj ((grayHomRight X).obj Y)) ≅
      L.obj ((ihom (DiagSet.toSSet.obj X)).obj (DiagSet.toSSet.obj Y)) :=
  Localization.isoOfHom L (weakEquivalences _)
      (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y))
      ((weakEquivalence_iff _).1 (weakEquivalence_toSSet_map_grayHomRestrict_counit_app hX hY)) ≪≫
    grayHomSimplicialIso (DiagSet.toSSet.obj X) L hY η

theorem grayHomComparisonIso_hom (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (grayHomComparisonIso L hX hY η).hom =
      L.map (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y)) ≫
        (grayHomSimplicialIso (DiagSet.toSSet.obj X) L hY η).hom :=
  rfl

theorem grayHomComparisonIso_eq (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (η' : Y ⟶ faceNerveRight.obj C') [WeakEquivalence ((DiagSet.toInfty 1).map η')] :
    grayHomComparisonIso L hX hY η = grayHomComparisonIso L hX hY η' :=
  Iso.ext (by
    rw [grayHomComparisonIso_hom, grayHomComparisonIso_hom, grayHomSimplicialIso_eq _ L hY η η'])

theorem grayHomComparisonIso_hom_naturality (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (hY' : IsInftyCategory 1 Y') (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y' ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] (g : Y ⟶ Y') :
    L.map (DiagSet.toSSet.map ((grayHomRight X).map g)) ≫ (grayHomComparisonIso L hX hY' η').hom =
      (grayHomComparisonIso L hX hY η).hom ≫
        L.map ((ihom (DiagSet.toSSet.obj X)).map (DiagSet.toSSet.map g)) := by
  rw [grayHomComparisonIso_hom, grayHomComparisonIso_hom, ← L.map_comp_assoc, ← Functor.map_comp,
    (grayHomRestrict (sSetDiagSetCounit X)).naturality g, Functor.map_comp, L.map_comp,
    Category.assoc, grayHomSimplicialIso_hom_naturality _ L hY hY' η η' g, Category.assoc]

theorem grayHomRestrict_comp_grayHomComparisonIso_hom (f : X' ⟶ X) (hX' : IsInftyCategory 1 X')
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (DiagSet.toSSet.map ((grayHomRestrict f).app Y)) ≫
        (grayHomComparisonIso L hX' hY η).hom =
      (grayHomComparisonIso L hX hY η).hom ≫
        L.map ((MonoidalClosed.pre (DiagSet.toSSet.map f)).app (DiagSet.toSSet.obj Y)) := by
  have h : (grayHomRestrict f).app Y ≫ (grayHomRestrict (sSetDiagSetCounit X')).app Y =
      (grayHomRestrict (sSetDiagSetCounit X)).app Y ≫
        (grayHomRestrict (SSet.toDiagSet.map (DiagSet.toSSet.map f))).app Y := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← grayHomRestrict_comp, ← grayHomRestrict_comp]
    exact congrArg (fun i => (grayHomRestrict i).app Y) (sSetDiagSetAdj.counit_naturality f).symm
  rw [grayHomComparisonIso_hom, grayHomComparisonIso_hom, ← L.map_comp_assoc, ← Functor.map_comp,
    h, Functor.map_comp, L.map_comp, Category.assoc,
    grayHomRestrict_comp_grayHomSimplicialIso_hom _ L (DiagSet.toSSet.map f) hY η, Category.assoc]

theorem constDiagram_comp_grayHomComparisonIso_hom (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (DiagSet.toSSet.map (constDiagram X Y)) ≫ (grayHomComparisonIso L hX hY η).hom =
      L.map (SSet.constDiagram (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)) := by
  rw [grayHomComparisonIso_hom, ← L.map_comp_assoc, ← Functor.map_comp,
    constDiagram_comp_grayHomRestrict, constDiagram_comp_grayHomSimplicialIso_hom]

theorem grayHomComparisonIso_hom_evalVertex (x : (DiagSet.toSSet.obj X) _⦋0⦌)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (grayHomComparisonIso L hX hY η).hom ≫ L.map (SSet.evalVertex x (DiagSet.toSSet.obj Y)) =
      L.map (DiagSet.toSSet.map (grayHomEval x Y)) := by
  rw [grayHomComparisonIso_hom, Category.assoc, grayHomSimplicialIso_hom_evalVertex L x hY η,
    ← L.map_comp, ← Functor.map_comp, grayHomRestrict_counit_app_comp_grayHomEvalVertex]

variable (X) in
noncomputable def grayHomRestrictCounitHomotopyInv (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) :
    DiagSet.toSSet.obj ((grayHomRight (SSet.toDiagSet.obj (DiagSet.toSSet.obj X))).obj Y) ⟶
      DiagSet.toSSet.obj ((grayHomRight X).obj Y) :=
  have := weakEquivalence_toSSet_map_grayHomRestrict_counit_app hX hY
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).1
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).2
  (RightHomotopyClass.whitehead
    (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y))).choose

private theorem grayHomRestrictCounitHomotopyInv_spec (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) :
    RightHomotopyRel (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y) ≫
        grayHomRestrictCounitHomotopyInv X hX hY) (𝟙 _) ∧
      RightHomotopyRel (grayHomRestrictCounitHomotopyInv X hX hY ≫
        DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y)) (𝟙 _) :=
  have := weakEquivalence_toSSet_map_grayHomRestrict_counit_app hX hY
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).1
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).2
  (RightHomotopyClass.whitehead
    (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y))).choose_spec

noncomputable def grayHomComparisonSpanLeft (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (ihom (DiagSet.toSSet.obj X)).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj ((grayHomRight X).obj Y) :=
  grayHomSimplicialSpanLeft (DiagSet.toSSet.obj X) hY η ≫ grayHomRestrictCounitHomotopyInv X hX hY

theorem weakEquivalence_grayHomComparisonSpanLeft (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (grayHomComparisonSpanLeft hX hY η) := by
  have := weakEquivalence_grayHomSimplicialSpanLeft (DiagSet.toSSet.obj X) hY η
  obtain ⟨h₁, h₂⟩ := grayHomRestrictCounitHomotopyInv_spec hX hY
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).1
  have := (isFibrant_toSSet_grayHomRight_counit (X := X) hY).2
  have : WeakEquivalence (grayHomRestrictCounitHomotopyInv X hX hY) :=
    weakEquivalence_of_rightHomotopyRel _ _ h₂ h₁
  dsimp only [grayHomComparisonSpanLeft]
  infer_instance

theorem grayHomComparisonSpanLeft_comp_grayHomComparisonIso_hom (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (grayHomComparisonSpanLeft hX hY η) ≫ (grayHomComparisonIso L hX hY η).hom =
      L.map (grayHomSimplicialSpanRight (DiagSet.toSSet.obj X) hY η) := by
  have hw : L.map (grayHomRestrictCounitHomotopyInv X hX hY) ≫
      L.map (DiagSet.toSSet.map ((grayHomRestrict (sSetDiagSetCounit X)).app Y)) = 𝟙 _ := by
    have e := (areEqualizedByLocalization_iff L (weakEquivalences _) _ _).1
      (RightHomotopyRel.factorsThroughLocalization _
        (grayHomRestrictCounitHomotopyInv_spec hX hY).2)
    simp only [CategoryTheory.Functor.map_id, L.map_comp] at e
    exact e
  rw [grayHomComparisonIso_hom, grayHomComparisonSpanLeft, L.map_comp, Category.assoc,
    reassoc_of% hw, grayHomSimplicialSpanLeft_comp_grayHomSimplicialIso_hom]

end Infty

open SSet.modelCategoryJoyal in
theorem grayHomComparison_exists {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj ((grayHomRight X).obj Y))
      (r : Z ⟶ (ihom (DiagSet.toSSet.obj X)).obj (DiagSet.toSSet.obj Y)),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨C, _, η, _, -⟩ := exists_weakEquivalence_faceNerveRight Y
  exact ⟨_, _, _, weakEquivalence_grayHomComparisonSpanLeft hX hY η,
    weakEquivalence_grayHomSimplicialSpanRight _ hY η⟩

section FunctorCategory

variable {X X' Y Y' : DiagSet.{u}} {C C' : MarkedSSet.{u}} [IsFibrant C] [IsFibrant C']

theorem isIso_functorCategoryToGrayHom (pseudo : Bool) (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) : IsIso (functorCategoryToGrayHom pseudo X Y) := by
  cases pseudo
  · infer_instance
  · have := isIso_functorCategoryPseudoToGray X hY
    rw [← functorCategoryPseudoToGray_comp_functorCategoryToGrayHom]
    infer_instance

noncomputable def functorCategoryGrayHomIso (pseudo : Bool) (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) : functorCategory pseudo X Y ≅ (grayHomRight X).obj Y :=
  have := isIso_functorCategoryToGrayHom pseudo X hY
  asIso (functorCategoryToGrayHom pseudo X Y)

@[simp]
theorem functorCategoryGrayHomIso_hom (pseudo : Bool) (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    (functorCategoryGrayHomIso pseudo X hY).hom = functorCategoryToGrayHom pseudo X Y :=
  rfl

theorem functorCategoryGrayHomIso_false (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    functorCategoryGrayHomIso false X hY = functorCategoryGrayIso X Y :=
  rfl

theorem functorCategoryGrayHomIso_true (X : DiagSet.{u}) {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    have := isIso_functorCategoryPseudoToGray X hY
    functorCategoryGrayHomIso true X hY =
      asIso (functorCategoryPseudoToGray X Y) ≪≫ functorCategoryGrayIso X Y :=
  Iso.ext (functorCategoryPseudoToGray_comp_functorCategoryToGrayHom X Y).symm

variable {H : Type*} [Category* H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

noncomputable def functorCategoryComparisonIso (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.obj (DiagSet.toSSet.obj (functorCategory pseudo X Y)) ≅
      L.obj ((ihom (DiagSet.toSSet.obj X)).obj (DiagSet.toSSet.obj Y)) :=
  L.mapIso (DiagSet.toSSet.mapIso (functorCategoryGrayHomIso pseudo X hY)) ≪≫
    grayHomComparisonIso L hX hY η

theorem functorCategoryComparisonIso_hom (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (functorCategoryComparisonIso L pseudo hX hY η).hom =
      L.map (DiagSet.toSSet.map (functorCategoryToGrayHom pseudo X Y)) ≫
        (grayHomComparisonIso L hX hY η).hom :=
  rfl

theorem functorCategoryComparisonIso_eq (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] :
    functorCategoryComparisonIso L pseudo hX hY η =
      functorCategoryComparisonIso L pseudo hX hY η' :=
  Iso.ext (by
    rw [functorCategoryComparisonIso_hom, functorCategoryComparisonIso_hom,
      grayHomComparisonIso_eq L hX hY η η'])

theorem functorCategoryComparisonIso_hom_naturality (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (hY' : IsInftyCategory 1 Y') (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (η' : Y' ⟶ faceNerveRight.obj C')
    [WeakEquivalence ((DiagSet.toInfty 1).map η')] (g : Y ⟶ Y')
    (φ : functorCategory pseudo X Y ⟶ functorCategory pseudo X Y')
    (hφ : φ ≫ functorCategoryToGrayHom pseudo X Y' =
      functorCategoryToGrayHom pseudo X Y ≫ (grayHomRight X).map g) :
    L.map (DiagSet.toSSet.map φ) ≫ (functorCategoryComparisonIso L pseudo hX hY' η').hom =
      (functorCategoryComparisonIso L pseudo hX hY η).hom ≫
        L.map ((ihom (DiagSet.toSSet.obj X)).map (DiagSet.toSSet.map g)) := by
  rw [functorCategoryComparisonIso_hom, functorCategoryComparisonIso_hom, ← L.map_comp_assoc,
    ← Functor.map_comp, hφ, Functor.map_comp, L.map_comp, Category.assoc,
    grayHomComparisonIso_hom_naturality L hX hY hY' η η' g, Category.assoc]

theorem functorCategoryComparisonIso_hom_restrict (pseudo : Bool) (f : X' ⟶ X)
    (hX' : IsInftyCategory 1 X') (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)]
    (ψ : functorCategory pseudo X Y ⟶ functorCategory pseudo X' Y)
    (hψ : ψ ≫ functorCategoryToGrayHom pseudo X' Y =
      functorCategoryToGrayHom pseudo X Y ≫ (grayHomRestrict f).app Y) :
    L.map (DiagSet.toSSet.map ψ) ≫ (functorCategoryComparisonIso L pseudo hX' hY η).hom =
      (functorCategoryComparisonIso L pseudo hX hY η).hom ≫
        L.map ((MonoidalClosed.pre (DiagSet.toSSet.map f)).app (DiagSet.toSSet.obj Y)) := by
  rw [functorCategoryComparisonIso_hom, functorCategoryComparisonIso_hom, ← L.map_comp_assoc,
    ← Functor.map_comp, hψ, Functor.map_comp, L.map_comp, Category.assoc,
    grayHomRestrict_comp_grayHomComparisonIso_hom L f hX' hX hY η, Category.assoc]

theorem functorCategoryComparisonIso_hom_constDiagram (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] (c : Y ⟶ functorCategory pseudo X Y)
    (hc : c ≫ functorCategoryToGrayHom pseudo X Y = constDiagram X Y) :
    L.map (DiagSet.toSSet.map c) ≫ (functorCategoryComparisonIso L pseudo hX hY η).hom =
      L.map (SSet.constDiagram (DiagSet.toSSet.obj X) (DiagSet.toSSet.obj Y)) := by
  rw [functorCategoryComparisonIso_hom, ← L.map_comp_assoc, ← Functor.map_comp, hc,
    constDiagram_comp_grayHomComparisonIso_hom]

theorem functorCategoryComparisonIso_hom_evalVertex (pseudo : Bool)
    (x : (DiagSet.toSSet.obj X) _⦋0⦌) (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Y ⟶ faceNerveRight.obj C) [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (functorCategoryComparisonIso L pseudo hX hY η).hom ≫
        L.map (SSet.evalVertex x (DiagSet.toSSet.obj Y)) =
      L.map (DiagSet.toSSet.map (functorCategoryToGrayHom pseudo X Y ≫ grayHomEval x Y)) := by
  rw [functorCategoryComparisonIso_hom, Category.assoc, grayHomComparisonIso_hom_evalVertex,
    ← L.map_comp, ← Functor.map_comp]

noncomputable def functorCategoryComparisonSpanLeft (pseudo : Bool) (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    (ihom (DiagSet.toSSet.obj X)).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C) ⟶
      DiagSet.toSSet.obj (functorCategory pseudo X Y) :=
  grayHomComparisonSpanLeft hX hY η ≫ DiagSet.toSSet.map (functorCategoryGrayHomIso pseudo X hY).inv

theorem weakEquivalence_functorCategoryComparisonSpanLeft (pseudo : Bool)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (functorCategoryComparisonSpanLeft pseudo hX hY η) := by
  have := weakEquivalence_grayHomComparisonSpanLeft hX hY η
  dsimp only [functorCategoryComparisonSpanLeft]
  infer_instance

theorem functorCategoryComparisonSpanLeft_comp_functorCategoryComparisonIso_hom (pseudo : Bool)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (η : Y ⟶ faceNerveRight.obj C)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    L.map (functorCategoryComparisonSpanLeft pseudo hX hY η) ≫
        (functorCategoryComparisonIso L pseudo hX hY η).hom =
      L.map (grayHomSimplicialSpanRight (DiagSet.toSSet.obj X) hY η) := by
  have hι : L.map (DiagSet.toSSet.map (functorCategoryGrayHomIso pseudo X hY).inv) ≫
      L.map (DiagSet.toSSet.map (functorCategoryToGrayHom pseudo X Y)) = 𝟙 _ := by
    rw [← L.map_comp, ← Functor.map_comp, ← functorCategoryGrayHomIso_hom pseudo X hY,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, L.map_id]
  rw [functorCategoryComparisonIso_hom, functorCategoryComparisonSpanLeft, L.map_comp,
    Category.assoc, reassoc_of% hι, grayHomComparisonSpanLeft_comp_grayHomComparisonIso_hom]

end FunctorCategory

open SSet.modelCategoryJoyal in
theorem functorCategoryComparison_exists (pseudo : Bool) {X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (functorCategory pseudo X Y))
      (r : Z ⟶ (ihom (DiagSet.toSSet.obj X)).obj (DiagSet.toSSet.obj Y)),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨C, _, η, _, -⟩ := exists_weakEquivalence_faceNerveRight Y
  exact ⟨_, _, _, weakEquivalence_functorCategoryComparisonSpanLeft pseudo hX hY η,
    weakEquivalence_grayHomSimplicialSpanRight _ hY η⟩

end Atoms.Diagrammatic
