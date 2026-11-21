import Atoms.Diagrammatic.Fibration.MarkedRightAnodyne
import Atoms.Diagrammatic.Fibration.CartesianEdgeComparison
import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.Diagrammatic.Limits.ProductPullback
import Atoms.Diagrammatic.Limits.ConeComparison

open CategoryTheory Limits Simplicial MonoidalClosed HomotopicalAlgebra Opposite
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

theorem rlp_monomorphisms_of_weakEquivalence_toSSet_map
    {A B : DiagSet.{u}} (g : A ⟶ B)
    [Fibration ((DiagSet.toInfty 1).map g)]
    [IsFibrant ((DiagSet.toInfty 1).obj B)]
    [WeakEquivalence (DiagSet.toSSet.map g)] :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp g := by
  have : Fibration (DiagSet.toSSet.map g) :=
    isQuillen_sSetDiagSetAdj.fibration_map ((DiagSet.toInfty 1).map g)
  apply rlp_monomorphisms_of_rlp_I_toSSet_map g
  intro K L i hi
  have : Mono i := SSet.modelCategoryQuillen.I_le_monomorphisms i hi
  have : Cofibration i := (cofibration_iff i).2
    (MorphismProperty.monomorphisms.infer_property i)
  infer_instance

theorem weakEquivalence_toSSet_map_coneObjectMap (α : Bool) {K X Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (d : K ⟶ X) (η : X ⟶ Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map η)] :
    WeakEquivalence (DiagSet.toSSet.map (coneObjectMap α d η)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have hHX := isInftyCategory_grayHomRight K hX
  have hHY := isInftyCategory_grayHomRight K hY
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hHX
  obtain ⟨_, _⟩ := fibration_toSSet_map_grayHomRestrict_and_isFibrant hHY
  have : WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomRight K).map η)) :=
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one K).weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map η)
  have := weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory (ball (atomSimplex 1))
    hHX hHY ((grayHomRight K).map η)
  have := weakEquivalence_toSSet_map_grayHomRight_map_of_isInftyCategory intervalBoundary hHX hHY
    ((grayHomRight K).map η)
  have := isFibrant_toSSet_obj hX
  have := isFibrant_toSSet_obj hY
  have : WeakEquivalence (DiagSet.toSSet.map η) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map η)
  exact (DiagSet.toSSet.map_isPullback
    (isPullback_coneObject α d)).weakEquivalence_map_of_fibration
      (DiagSet.toSSet.map_isPullback (isPullback_coneObject α (d ≫ η)))
      (DiagSet.toSSet.map ((grayHomRight (ball (atomSimplex 1))).map
        ((grayHomRight K).map η)))
      (DiagSet.toSSet.map ((grayHomRight intervalBoundary).map
        ((grayHomRight K).map η)))
      (DiagSet.toSSet.map η) (DiagSet.toSSet.map (coneObjectMap α d η))
      (by rw [← Functor.map_comp, ← Functor.map_comp, (grayHomRestrict _).naturality])
      (by rw [← Functor.map_comp, ← Functor.map_comp, coneObjectBase_comp])
      (by rw [← Functor.map_comp, ← Functor.map_comp, coneObjectMap_ι])
      (by rw [← Functor.map_comp, ← Functor.map_comp, coneObjectMap_π])

theorem weakEquivalence_toSSet_map_coneObjectπ_of_isFinal {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x : X.Vertex)
    (hx : SSet.IsFinal (X.vertexEquivSSet x)) :
    WeakEquivalence (DiagSet.toSSet.map (coneObjectπ true (vertexHom x))) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have := isFibrant_toSSet_obj hX
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    (isFibrant_iff_quasicategory _).1 inferInstance
  obtain ⟨C, _, η, _, -⟩ := exists_weakEquivalence_faceNerveRight X
  have hG := isInftyCategory_faceNerveRight_obj C
  have := isFibrant_toSSet_obj hG
  have : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    (isFibrant_infty_iff 1 _).2 hG
  have : (DiagSet.toSSet.obj (faceNerveRight.obj C)).Quasicategory :=
    (isFibrant_iff_quasicategory _).1 inferInstance
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have : WeakEquivalence (DiagSet.toSSet.map η) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map η)
  have hy : SSet.IsFinal ((faceNerveRight.obj C).vertexEquivSSet (x.map η)) := by
    rw [DiagSet.vertexEquivSSet_map]
    exact (SSet.modelCategoryJoyal.isFinal_iff_of_weakEquivalence _ _).2 hx
  let c := faceNerveRightVertexLift C ((faceNerveRight.obj C).vertexEquivSSet (x.map η))
  have hc := faceNerveRightComparison_app_vertexLift C
    ((faceNerveRight.obj C).vertexEquivSSet (x.map η))
  have := weakEquivalence_faceNerveRightComparison_app C
  have : SSet.Quasicategory ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    (isFibrant_iff_quasicategory _).1 (isFibrant_toSSet_obj hG)
  have hC : SSet.IsFinal c := by
    apply (SSet.modelCategoryJoyal.isFinal_iff_of_weakEquivalence
      (faceNerveRightComparison.app C) c).1
    change SSet.IsFinal ((faceNerveRightComparison.app C).app _
      (faceNerveRightVertexLift C _))
    rw [hc]
    exact hy
  have := (SSet.modelCategoryJoyal.isFinal_iff_weakEquivalence_commaConeπ c).1 hC
  have := weakEquivalence_commaConeToConeObject C hc
  have : WeakEquivalence (commaConeToConeObject C hc ≫
      DiagSet.toSSet.map (coneObjectπ true (vertexHom (x.map η)))) := by
    rw [commaConeToConeObject_π]
    infer_instance
  have : WeakEquivalence (DiagSet.toSSet.map
      (coneObjectπ true (vertexHom (x.map η)))) :=
    weakEquivalence_of_precomp (commaConeToConeObject C hc) _
  have := weakEquivalence_toSSet_map_coneObjectMap true hX hG (vertexHom x) η
  have : WeakEquivalence (DiagSet.toSSet.map
      (coneObjectπ true (vertexHom x ≫ η))) := by
    rw [vertexHom_comp]
    infer_instance
  have : WeakEquivalence (DiagSet.toSSet.map
      (coneObjectMap true (vertexHom x) η) ≫
        DiagSet.toSSet.map (coneObjectπ true (vertexHom x ≫ η))) := inferInstance
  have : WeakEquivalence (DiagSet.toSSet.map (coneObjectπ true (vertexHom x)) ≫
      DiagSet.toSSet.map η) := by
    rwa [← Functor.map_comp, coneObjectMap_π, Functor.map_comp] at this
  exact weakEquivalence_of_postcomp _ (DiagSet.toSSet.map η)

theorem rlp_monomorphisms_coneObjectπ_of_isFinal {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x : X.Vertex)
    (hx : SSet.IsFinal (X.vertexEquivSSet x)) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (coneObjectπ true (vertexHom x)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have := fibration_coneObjectπ true (vertexHom x) hX
  have := weakEquivalence_toSSet_map_coneObjectπ_of_isFinal hX x hx
  exact rlp_monomorphisms_of_weakEquivalence_toSSet_map _

private theorem isIso_sliceRestrict {A B : DiagSet.{u}} (i : A ⟶ B) [IsIso i]
    (p : Under B) : IsIso ((sliceRestrict i).app p) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [CategoryTheory.isIso_iff_bijective]
  let e := WithInitial.joinMapIso (Iso.refl (ball.{u} U.unop)) (asIso i)
  constructor
  · intro c c' h
    apply (WithInitial.sliceObjEquiv B p U.unop).injective
    apply Subtype.ext
    apply (cancel_epi e.hom).1
    exact congrArg (fun t ↦ (WithInitial.sliceObjEquiv A
      ((Under.map i).obj p) U.unop t).1) h
  · intro c
    let f := (WithInitial.sliceObjEquiv A ((Under.map i).obj p) U.unop c).1
    have hf : WithInitial.joinInclRight _ A ≫ f = i ≫ p.hom :=
      (WithInitial.sliceObjEquiv A ((Under.map i).obj p) U.unop c).2
    have hright : WithInitial.joinInclRight _ B ≫ e.inv ≫ f = p.hom := by
      change WithInitial.joinInclRight _ B ≫
        WithInitial.joinMap (𝟙 _) (inv i) ≫ f = p.hom
      exact (WithInitial.joinInclRight_comp_joinMap_assoc (𝟙 _) (inv i) f).trans
        ((congrArg (inv i ≫ ·) hf).trans (IsIso.inv_hom_id_assoc i p.hom))
    refine ⟨(WithInitial.sliceObjEquiv B p U.unop).symm ⟨e.inv ≫ f, hright⟩, ?_⟩
    apply (WithInitial.sliceObjEquiv A ((Under.map i).obj p) U.unop).injective
    apply Subtype.ext
    change e.hom ≫ _ = f
    simp only [Equiv.apply_symm_apply]
    exact e.hom_inv_id_assoc f

private noncomputable def pointSliceRestrictionIso :
    WithInitial.slice (ball.{u} atomPoint) ≅
      Under.map pointIsoToDiagSetStdSimplex.inv ⋙
        WithInitial.slice (SSet.toDiagSet.obj Δ[0]) :=
  have : ∀ p, IsIso ((sliceRestrict pointIsoToDiagSetStdSimplex.{u}.inv).app p) :=
    fun p ↦ isIso_sliceRestrict _ p
  NatIso.ofComponents (fun p ↦ asIso ((sliceRestrict
    pointIsoToDiagSetStdSimplex.inv).app p))
    (fun f ↦ (sliceRestrict pointIsoToDiagSetStdSimplex.inv).naturality f)

private noncomputable def pointUnderUnitIso :
    Under.map pointIsoToDiagSetStdSimplex.{u}.inv ⋙ Under.post DiagSet.toSSet ⋙
      Under.map (sSetDiagSetAdj.unit.app Δ[0]) ≅
        Under.post DiagSet.toSSet ⋙ Under.map toSSetPoint :=
  NatIso.ofComponents (fun p ↦ Under.isoMk (Iso.refl _) (by
    change (sSetDiagSetAdj.unit.app Δ[0] ≫
      DiagSet.toSSet.map (pointIsoToDiagSetStdSimplex.inv ≫ p.hom)) ≫ 𝟙 _ =
        toSSetPoint ≫ DiagSet.toSSet.map p.hom
    rw [Category.comp_id, Functor.map_comp, ← Category.assoc]
    congr 1
    exact (isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _).hom_ext _ _))
    (fun f ↦ Under.UnderMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

private noncomputable def pointSliceIso :
    WithInitial.slice (ball.{u} atomPoint) ⋙ DiagSet.toSSet ≅
      Under.post DiagSet.toSSet ⋙ Under.map toSSetPoint ⋙ SSet.slice Δ[0] :=
  Functor.isoWhiskerRight pointSliceRestrictionIso DiagSet.toSSet ≪≫
    Functor.isoWhiskerLeft (Under.map pointIsoToDiagSetStdSimplex.inv) (toSSetSliceIso Δ[0]) ≪≫
      Functor.isoWhiskerRight pointUnderUnitIso (SSet.slice Δ[0])

private noncomputable def nativeConstantSlice (p : Under (ball.{u} atomPoint)) :
    ball atomPoint ⟶ (WithInitial.slice (ball atomPoint)).obj p :=
  (WithInitial.joinRightUnderAdjunction (ball atomPoint)).homEquiv _ _
    (Under.homMk (isTerminalBallAtomPoint.from _ ≫ p.hom) (by
      rw [← Category.assoc, isTerminalBallAtomPoint.hom_ext (_ ≫ _) (𝟙 _),
        Category.id_comp]))

private theorem nativeConstantSlice_naturality {p q : Under (ball.{u} atomPoint)}
    (f : p ⟶ q) : nativeConstantSlice p ≫ (WithInitial.slice _).map f =
      nativeConstantSlice q := by
  rw [nativeConstantSlice, ← Adjunction.homEquiv_naturality_right]
  congr 1
  apply Under.UnderMorphism.ext
  change (isTerminalBallAtomPoint.from _ ≫ p.hom) ≫ f.right =
    isTerminalBallAtomPoint.from _ ≫ q.hom
  rw [Category.assoc, Under.w]

private noncomputable def simplicialConstantSlice (p : Under (Δ[0] : SSet.{u})) :
    Δ[0] ⟶ (SSet.slice Δ[0]).obj p :=
  (SSet.joinRightUnderAdjunction Δ[0]).homEquiv _ _
    (Under.homMk (SSet.stdSimplex.isTerminalObj₀.from _ ≫ p.hom) (by
      rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _),
        Category.id_comp]))

private theorem simplicialConstantSlice_naturality {p q : Under (Δ[0] : SSet.{u})}
    (f : p ⟶ q) : simplicialConstantSlice p ≫ (SSet.slice _).map f =
      simplicialConstantSlice q := by
  rw [simplicialConstantSlice, ← Adjunction.homEquiv_naturality_right]
  congr 1
  apply Under.UnderMorphism.ext
  change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ p.hom) ≫ f.right =
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ q.hom
  rw [Category.assoc, Under.w]

private theorem pointSliceIso_constant (p : Under (ball.{u} atomPoint)) :
    toSSetPoint ≫ DiagSet.toSSet.map (nativeConstantSlice p) ≫ (pointSliceIso.hom.app p) =
      simplicialConstantSlice
        ((Under.post DiagSet.toSSet ⋙ Under.map toSSetPoint).obj p) := by
  let p₀ : Under (ball.{u} atomPoint) := Under.mk (𝟙 _)
  let f : p₀ ⟶ p := Under.homMk p.hom (Category.id_comp _)
  have h₀ : toSSetPoint ≫ DiagSet.toSSet.map (nativeConstantSlice p₀) ≫
      pointSliceIso.hom.app p₀ = simplicialConstantSlice
        ((Under.post DiagSet.toSSet ⋙ Under.map toSSetPoint).obj p₀) := by
    apply ((SSet.joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm.injective
    apply Under.UnderMorphism.ext
    exact (isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _).hom_ext _ _
  have hn := pointSliceIso.hom.naturality f
  change DiagSet.toSSet.map ((WithInitial.slice _).map f) ≫ _ = _ at hn
  rw [← nativeConstantSlice_naturality f, Functor.map_comp]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc (DiagSet.toSSet.map (nativeConstantSlice p₀)),
    ← Category.assoc, h₀]
  exact simplicialConstantSlice_naturality
    ((Under.post DiagSet.toSSet ⋙ Under.map toSSetPoint).map f)

noncomputable def DiagSet.toSSetSliceAtIso (S : DiagSet.{u}) (b : S.Vertex) :
    DiagSet.toSSet.obj (S.sliceAt b) ≅
      SSet.sliceAt (DiagSet.toSSet.obj S) (S.vertexEquivSSet b) :=
  pointSliceIso.app (Under.mk (vertexHom b)) ≪≫
    (SSet.slice Δ[0]).mapIso (Under.isoMk (Iso.refl _)
      (by
        exact (Category.comp_id _).trans
          (toSSetPoint_comp_toSSet_map_vertexHom b)))

private theorem pointSliceIso_hom_app_comp_sliceπ (p : Under (ball.{u} atomPoint)) :
    pointSliceIso.hom.app p ≫ SSet.sliceπ _ =
      DiagSet.toSSet.map ((sliceProj (ball.{u} atomPoint)).app p) := by
  dsimp only [pointSliceIso, pointSliceRestrictionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, asIso_hom]
  rw [Category.assoc, Category.assoc]
  refine (whisker_eq _ (whisker_eq _ (SSet.slice_map_sliceπ _))).trans ?_
  refine (whisker_eq _ (whisker_eq _ (Category.comp_id _))).trans ?_
  refine (whisker_eq _ (toSSetSliceIso_hom_app_comp_sliceπ _ _)).trans ?_
  exact (DiagSet.toSSet.map_comp _ _).symm.trans
    (congrArg DiagSet.toSSet.map (sliceRestrict_app_comp_sliceProj_app _ _))

theorem DiagSet.toSSetSliceAtIso_hom_comp_sliceAtπ (S : DiagSet.{u}) (b : S.Vertex) :
    (S.toSSetSliceAtIso b).hom ≫ SSet.sliceAtπ (DiagSet.toSSet.obj S) (S.vertexEquivSSet b) =
      DiagSet.toSSet.map (S.sliceAtProj b) := by
  dsimp only [DiagSet.toSSetSliceAtIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (SSet.slice_map_sliceπ _)).trans ?_
  refine (whisker_eq _ (Category.comp_id _)).trans ?_
  exact pointSliceIso_hom_app_comp_sliceπ (Under.mk (vertexHom b))

theorem DiagSet.toSSetSliceAtIso_hom_sliceAtId (S : DiagSet.{u}) (b : S.Vertex) :
    (S.toSSetSliceAtIso b).hom.app _
      ((S.sliceAt b).vertexEquivSSet (uliftYonedaEquiv (S.sliceAtId b))) =
        SSet.sliceId (DiagSet.toSSet.obj S) (S.vertexEquivSSet b) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  rw [← toSSetPoint_comp_toSSet_map_vertexHom]
  change (toSSetPoint ≫ DiagSet.toSSet.map (nativeConstantSlice (Under.mk (vertexHom b)))) ≫
    (S.toSSetSliceAtIso b).hom = _
  change (toSSetPoint ≫ DiagSet.toSSet.map
    (nativeConstantSlice (Under.mk (vertexHom b)))) ≫
      pointSliceIso.hom.app (Under.mk (vertexHom b)) ≫ (SSet.slice Δ[0]).map _ = _
  rw [← Category.assoc, Category.assoc toSSetPoint, pointSliceIso_constant,
    simplicialConstantSlice_naturality]
  rfl

theorem DiagSet.isFinal_toSSet_sliceAtId (S : DiagSet.{u})
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    SSet.IsFinal ((S.sliceAt b).vertexEquivSSet
      (uliftYonedaEquiv (X := atomPoint) (S.sliceAtId b))) := by
  have hs : IsFibrant ((DiagSet.toInfty 1).obj (S.sliceAt b)) :=
    isFibrant_slice_of_isFibrant (vertexHom b)
  have := isFibrant_toSSet_obj ((isFibrant_infty_iff 1 (S.sliceAt b)).1 hs :
    IsInftyCategory 1 (S.sliceAt b))
  have : (DiagSet.toSSet.obj (S.sliceAt b)).Quasicategory :=
    (isFibrant_iff_quasicategory _).1 inferInstance
  have : SSet.Quasicategory
      (SSet.sliceAt (DiagSet.toSSet.obj S) (S.vertexEquivSSet b)) :=
    (isFibrant_iff_quasicategory _).1
      (isFibrant_of_fibration (S.toSSetSliceAtIso b).inv)
  apply (SSet.modelCategoryJoyal.isFinal_iff_of_weakEquivalence
    (S.toSSetSliceAtIso b).hom _).1
  rw [DiagSet.toSSetSliceAtIso_hom_sliceAtId]
  exact SSet.rightAnodyneExtensions_sliceId _ _

theorem DiagSet.rlp_monomorphisms_coneObjectπ_sliceAtId (S : DiagSet.{u})
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (coneObjectπ true (S.sliceAtId b)) := by
  have hs : IsFibrant ((DiagSet.toInfty 1).obj (S.sliceAt b)) :=
    isFibrant_slice_of_isFibrant (vertexHom b)
  have hx := S.isFinal_toSSet_sliceAtId b
  have h := rlp_monomorphisms_coneObjectπ_of_isFinal
    ((isFibrant_infty_iff 1 (S.sliceAt b)).1 hs)
    (uliftYonedaEquiv (X := atomPoint) (S.sliceAtId b)) hx
  change (MorphismProperty.monomorphisms DiagSet.{u}).rlp
    (coneObjectπ true (uliftYonedaEquiv.symm
      (uliftYonedaEquiv (X := atomPoint) (S.sliceAtId b)))) at h
  rw [Equiv.symm_apply_apply] at h
  exact h

private theorem point_constDiagram {X : DiagSet.{u}} (i : ball atomPoint ⟶ X) :
    i ≫ constDiagram (ball atomPoint) X = diagramPoint i := by
  apply (cancel_mono (grayHomRightPointIso.hom.app X)).1
  rw [Category.assoc, constDiagram_comp_grayHomRightPointIso_hom_app, Category.comp_id,
    diagramPoint_comp_grayHomRightPointIso_hom_app,
    isTerminalBallAtomPoint.hom_ext (isTerminalBallAtomPoint.from _) (𝟙 _), Category.id_comp]

private theorem constant_cone_boundary {X : DiagSet.{u}} (i : ball atomPoint ⟶ X) :
    (grayTensorLeft (ball atomPoint)).map intervalBoundaryι ≫
      grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫
        i ≫ constDiagram (ball atomPoint) X =
      grayTensorBoundaryDesc (ball atomPoint)
        (grayTensorFst (ball atomPoint) _ ≫ i ≫ constDiagram (ball atomPoint) X)
        (grayTensorFst (ball atomPoint) _ ≫ i ≫
          isTerminalBallAtomPoint.from X ≫ diagramPoint i) := by
  refine grayTensor_coprod_hom_ext _ ?_ ?_
  · simp only [← Category.assoc, ← Functor.map_comp, coprod.inl_desc,
      grayTensorBoundaryDesc_inl]
    simp only [grayTensorLeft_map_eq, Category.assoc,
      reassoc_of% grayTensorBifunctor_map_grayTensorFst, Category.id_comp]
  · simp only [← Category.assoc, ← Functor.map_comp, coprod.inr_desc,
      grayTensorBoundaryDesc_inr]
    simp only [grayTensorLeft_map_eq, Category.assoc,
      reassoc_of% grayTensorBifunctor_map_grayTensorFst, Category.id_comp]
    simp only [point_constDiagram]
    rw [← Category.assoc i, isTerminalBallAtomPoint.hom_ext (i ≫ _) (𝟙 _),
      Category.id_comp]

private theorem cone_hom_boundary {T X : DiagSet.{u}} (i : ball atomPoint ⟶ X)
    (g : T ⟶ coneObject true i) :
    (grayTensorLeft T).map intervalBoundaryι ≫
        ((coneObjectHomEquiv true i T) g).val.2 ≫ grayHomRightPointIso.hom.app X =
      grayTensorBoundaryDesc T
        (grayTensorFst T (ball atomPoint) ≫ g ≫ coneObjectπ true i)
        (grayTensorFst T (ball atomPoint) ≫ isTerminalBallAtomPoint.from T ≫ i) := by
  rw [← Category.assoc, ((coneObjectHomEquiv true i T) g).property]
  refine grayTensor_coprod_hom_ext T ?_ ?_ <;>
    simp only [← Category.assoc, grayTensorBoundaryDesc_inl, grayTensorBoundaryDesc_inr]
  · simp only [Category.assoc, Bool.cond_true,
      constDiagram_comp_grayHomRightPointIso_hom_app, Category.comp_id]
    exact Category.assoc _ g (coneObjectπ true i)
  · simp only [Category.assoc, Bool.cond_true,
      diagramPoint_comp_grayHomRightPointIso_hom_app]
    apply congrArg (grayTensorFst T (ball atomPoint) ≫ ·)
    simpa only [Category.assoc] using congrArg (· ≫ i) (isTerminalBallAtomPoint.hom_ext
      (((coneObjectHomEquiv true i T) g).val.1 ≫
        isTerminalBallAtomPoint.from X ≫ isTerminalBallAtomPoint.from (ball atomPoint))
      (isTerminalBallAtomPoint.from T))

private theorem cone_hom_precomp {T U X : DiagSet.{u}} (i : ball atomPoint ⟶ X)
    (g : T ⟶ coneObject true i) (f : U ⟶ T) :
    (grayTensorRight (ball (atomSimplex 1))).map f ≫
        ((coneObjectHomEquiv true i T) g).val.2 =
      ((coneObjectHomEquiv true i U) (f ≫ g)).val.2 := by
  exact ((grayTensorRightAdjunction _).homEquiv_naturality_left_symm f
    (g ≫ coneObjectι true i)).symm

theorem exists_contraction_of_rlp_coneObjectπ {X : DiagSet.{u}}
    (i : ball atomPoint ⟶ X)
    (hi : (MorphismProperty.monomorphisms DiagSet.{u}).rlp (coneObjectπ true i)) :
    ∃ h : grayTensor X (ball (atomSimplex 1)) ⟶ X,
      (grayTensorLeft X).map intervalBoundaryι ≫ h = grayTensorBoundaryDesc X
        (GrayDiagSet.rightUnitor X).hom
        (grayTensorFst X (ball atomPoint) ≫ isTerminalBallAtomPoint.from X ≫ i) ∧
      (grayTensorRight (ball (atomSimplex 1))).map i ≫ h =
        grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫ i := by
  let a := grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫
    i ≫ constDiagram (ball atomPoint) X
  let q := (coneObjectHomEquiv true i (ball atomPoint)).symm
    ⟨(i, a), constant_cone_boundary i⟩
  have hq := (coneObjectHomEquiv true i (ball atomPoint)).apply_symm_apply
    ⟨(i, a), constant_cone_boundary i⟩
  have hqπ : q ≫ coneObjectπ true i = i := congrArg (fun t ↦ t.val.1) hq
  have : IsSplitMono i := isTerminalBallAtomPoint.isSplitMono_from i
  have : HasLiftingProperty i (coneObjectπ true i) :=
    hi i (MorphismProperty.monomorphisms.infer_property i)
  let sq : CommSq q i (coneObjectπ true i) (𝟙 X) :=
    ⟨hqπ.trans (Category.comp_id _).symm⟩
  obtain ⟨l⟩ := CommSq.HasLift.exists_lift (sq := sq)
  have hleft := l.fac_left
  have hright := l.fac_right
  let t := (coneObjectHomEquiv true i X) l.l
  let h := t.val.2 ≫ grayHomRightPointIso.hom.app X
  refine ⟨h, ?_, ?_⟩
  · dsimp only [h, t]
    rw [cone_hom_boundary, hright, Category.comp_id]
    exact congrArg (fun f ↦ grayTensorBoundaryDesc X f
      (grayTensorFst X (ball atomPoint) ≫ isTerminalBallAtomPoint.from X ≫ i))
        (grayTensorFst_point X)
  · dsimp only [h, t]
    rw [← Category.assoc, cone_hom_precomp, hleft]
    have hqa := congrArg (fun t ↦ t.val.2) hq
    change ((coneObjectHomEquiv true i (ball atomPoint)) q).val.2 = a at hqa
    rw [hqa]
    change (grayTensorFst _ _ ≫ i ≫ constDiagram _ X) ≫ _ = _
    rw [Category.assoc, Category.assoc, constDiagram_comp_grayHomRightPointIso_hom_app,
      Category.comp_id]

theorem DiagSet.exists_sliceContraction (S : DiagSet.{u})
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    ∃ h : grayTensor (S.sliceAt b) (ball (atomSimplex 1)) ⟶ S.sliceAt b,
      (grayTensorLeft (S.sliceAt b)).map intervalBoundaryι ≫ h =
        grayTensorBoundaryDesc (S.sliceAt b) (GrayDiagSet.rightUnitor (S.sliceAt b)).hom
          (grayTensorFst (S.sliceAt b) (ball atomPoint) ≫
            isTerminalBallAtomPoint.from (S.sliceAt b) ≫ S.sliceAtId b) ∧
      (grayTensorRight (ball (atomSimplex 1))).map (S.sliceAtId b) ≫ h =
        grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫ S.sliceAtId b :=
  exists_contraction_of_rlp_coneObjectπ _ (S.rlp_monomorphisms_coneObjectπ_sliceAtId b)

private noncomputable def markedLastEnd (ε : Bool) (B : MarkedDiagSet.{u}) :
    B ⟶ markedTensor false B markedInterval :=
  (markedTensorRightUnitor false B).inv ≫ markedTensorMap false (𝟙 B) (markedIntervalVertex ε)

private theorem markedLastEnd_naturality (ε : Bool) {A B : MarkedDiagSet.{u}} (i : A ⟶ B) :
    i ≫ markedLastEnd ε B = markedLastEnd ε A ≫ markedTensorMap false i (𝟙 markedInterval) := by
  dsimp only [markedLastEnd]
  have hu : i ≫ (markedTensorRightUnitor false B).inv =
      (markedTensorRightUnitor false A).inv ≫ markedTensorMap false i (𝟙 _) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← markedTensorRightUnitor_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hu, Category.assoc, Category.assoc]
  apply congrArg ((markedTensorRightUnitor false A).inv ≫ ·)
  exact ((markedTensorBifunctor false).map_comp (X := (A, _)) (Y := (B, _)) (Z := (B, _))
    (i, 𝟙 _) (𝟙 B, markedIntervalVertex ε)).symm.trans
      ((congrArg (markedTensorBifunctor false).map (Prod.ext
        ((Category.comp_id i).trans (Category.id_comp i).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm))).trans
          ((markedTensorBifunctor false).map_comp (X := (A, _)) (Y := (A, _)) (Z := (B, _))
            (𝟙 A, markedIntervalVertex ε) (i, 𝟙 _)))

private theorem cellular_of_marked_contraction {B : MarkedDiagSet.{u}}
    (i : markedTensorUnit ⟶ B) [Mono i]
    (h : markedTensor false B markedInterval ⟶ B)
    (h₀ : markedLastEnd false B ≫ h = 𝟙 B)
    (h₁ : markedLastEnd true B ≫ h = isTerminalMarkedTensorUnit.from B ≫ i)
    (hrel : markedTensorMap false i (𝟙 markedInterval) ≫ h =
      isTerminalMarkedTensorUnit.from _ ≫ i) :
    MarkedDiagSet.cellularMarkedRightAnodyne i := by
  let box := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor false)) i (markedIntervalVertex true)
  let a := markedLastEnd false markedTensorUnit ≫ box.inr
  have ha : a ≫ box.ι = i ≫ markedLastEnd false B :=
    (Category.assoc _ _ _).trans ((congrArg (markedLastEnd false markedTensorUnit ≫ ·)
      box.inr_ι).trans (markedLastEnd_naturality false i).symm)
  have hr : box.ι ≫ h = isTerminalMarkedTensorUnit.from box.pt ≫ i := by
    apply box.isPushout.hom_ext
    · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) box.inl_ι).trans
        ((cancel_epi (markedTensorRightUnitor false B).inv).1 ?_))
      exact (Category.assoc _ _ _).symm.trans (h₁.trans
        ((congrArg (· ≫ i) (isTerminalMarkedTensorUnit.hom_ext _ _)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) box.inr_ι).trans
        (hrel.trans ((congrArg (· ≫ i) (isTerminalMarkedTensorUnit.hom_ext _ _)).trans
          (Category.assoc _ _ _))))
  let r : RetractArrow i box.ι :=
    { i := Arrow.homMk a (markedLastEnd false B) ha
      r := Arrow.homMk (isTerminalMarkedTensorUnit.from box.pt) h hr.symm
      retract := Arrow.hom_ext _ _ (isTerminalMarkedTensorUnit.hom_ext _ _) h₀ }
  exact MarkedDiagSet.cellularMarkedRightAnodyne.of_retract r
    (MorphismProperty.le_saturation _ _ (MarkedDiagSet.rightCylinderMaps.mk i))

private noncomputable def simplexMarkedIntervalIso :
    ball.{u} (atomSimplex 1) ≅ markedInterval.underlying :=
  intervalIsoGlobe ≪≫ intervalBallIso

private theorem simplexMarkedIntervalIso_end (ε : Bool) :
    cond ε intervalTarget.{u} intervalSource ≫ simplexMarkedIntervalIso.hom =
      MarkedPresheaf.forget.map (markedIntervalVertex ε) := by
  rw [simplexMarkedIntervalIso, Iso.trans_hom, ← Category.assoc,
    intervalEnd_comp_intervalIsoGlobe, forget_map_markedIntervalVertex]
  rfl

private theorem contraction_end {X : DiagSet.{u}} (i : ball atomPoint ⟶ X)
    (h : grayTensor X (ball (atomSimplex 1)) ⟶ X)
    (hb : (grayTensorLeft X).map intervalBoundaryι ≫ h = grayTensorBoundaryDesc X
      (GrayDiagSet.rightUnitor X).hom
      (grayTensorFst X (ball atomPoint) ≫ isTerminalBallAtomPoint.from X ≫ i)) (ε : Bool) :
    (GrayDiagSet.rightUnitor X).inv ≫
        (grayTensorLeft X).map (cond ε intervalTarget intervalSource) ≫ h =
      cond ε (isTerminalBallAtomPoint.from X ≫ i) (𝟙 X) := by
  cases ε with
  | false =>
    have he := congrArg ((grayTensorLeft X).map coprod.inl ≫ ·) hb
    rw [← Functor.map_comp_assoc, intervalBoundaryι, coprod.inl_desc,
      grayTensorBoundaryDesc_inl] at he
    simp only [cond_false]
    rw [he, Iso.inv_hom_id]
  | true =>
    have he := congrArg ((grayTensorLeft X).map coprod.inr ≫ ·) hb
    rw [← Functor.map_comp_assoc, intervalBoundaryι, coprod.inr_desc,
      grayTensorBoundaryDesc_inr] at he
    simp only [cond_true]
    rw [he, grayTensorFst_point, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem forget_markedLastEnd_comp {X : DiagSet.{u}} (ε : Bool) :
    MarkedPresheaf.forget.map (markedLastEnd ε ((MarkedPresheaf.sharp atomMarking).obj X)) ≫
        (grayTensorLeft X).map simplexMarkedIntervalIso.inv =
      (GrayDiagSet.rightUnitor X).inv ≫
        (grayTensorLeft X).map (cond ε intervalTarget intervalSource) := by
  simp only [markedLastEnd, Functor.map_comp, forget_map_markedTensorRightUnitor_inv,
    forget_map_markedTensorMap]
  change (GrayDiagSet.rightUnitor X).inv ≫
    (grayTensorLeft X).map (MarkedPresheaf.forget.map (markedIntervalVertex ε)) ≫
      (grayTensorLeft X).map simplexMarkedIntervalIso.inv = _
  have he : MarkedPresheaf.forget.map (markedIntervalVertex ε) ≫
      simplexMarkedIntervalIso.inv = cond ε intervalTarget intervalSource :=
    (simplexMarkedIntervalIso.comp_inv_eq).2 (simplexMarkedIntervalIso_end ε).symm
  exact congrArg ((GrayDiagSet.rightUnitor X).inv ≫ ·)
    (((grayTensorLeft X).map_comp _ _).symm.trans (congrArg (grayTensorLeft X).map he))

private theorem forget_marked_contraction_arrow {X : DiagSet.{u}}
    (h : grayTensor X (ball (atomSimplex 1)) ⟶ X)
    (H : markedTensor false ((MarkedPresheaf.sharp atomMarking).obj X) markedInterval ⟶
      (MarkedPresheaf.sharp atomMarking).obj X)
    (hH : MarkedPresheaf.forget.map H =
      (grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h)
    (ε : Bool) :
    MarkedPresheaf.forget.map (markedLastEnd ε ((MarkedPresheaf.sharp atomMarking).obj X) ≫ H) =
      (GrayDiagSet.rightUnitor X).inv ≫
        (grayTensorLeft X).map (cond ε intervalTarget intervalSource) ≫ h := by
  exact (MarkedPresheaf.forget.map_comp _ H).trans
    ((congrArg (MarkedPresheaf.forget.map (markedLastEnd ε _) ≫ ·) hH).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) (forget_markedLastEnd_comp ε)).trans
        (Category.assoc _ _ _))))

private theorem forget_marked_contraction_end {X : DiagSet.{u}}
    (i : markedTensorUnit ⟶ (MarkedPresheaf.sharp atomMarking).obj X)
    (h : grayTensor X (ball (atomSimplex 1)) ⟶ X)
    (H : markedTensor false ((MarkedPresheaf.sharp atomMarking).obj X) markedInterval ⟶
      (MarkedPresheaf.sharp atomMarking).obj X)
    (hH : MarkedPresheaf.forget.map H =
      (grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h)
    (hb : (grayTensorLeft X).map intervalBoundaryι ≫ h = grayTensorBoundaryDesc X
      (GrayDiagSet.rightUnitor X).hom
      (grayTensorFst X (ball atomPoint) ≫ isTerminalBallAtomPoint.from X ≫
        MarkedPresheaf.forget.map i))
    (ε : Bool) :
    MarkedPresheaf.forget.map (markedLastEnd ε ((MarkedPresheaf.sharp atomMarking).obj X) ≫ H) =
      cond ε (isTerminalBallAtomPoint.from X ≫ MarkedPresheaf.forget.map i) (𝟙 X) := by
  exact (forget_marked_contraction_arrow h H hH ε).trans
    (contraction_end (MarkedPresheaf.forget.map i) h hb ε)

private theorem marked_contraction_relative {X : DiagSet.{u}}
    (i : markedTensorUnit ⟶ (MarkedPresheaf.sharp atomMarking).obj X)
    (h : grayTensor X (ball (atomSimplex 1)) ⟶ X)
    (H : markedTensor false ((MarkedPresheaf.sharp atomMarking).obj X) markedInterval ⟶
      (MarkedPresheaf.sharp atomMarking).obj X)
    (hH : MarkedPresheaf.forget.map H =
      (grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h)
    (hr : (grayTensorRight (ball (atomSimplex 1))).map (MarkedPresheaf.forget.map i) ≫ h =
      grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫ MarkedPresheaf.forget.map i) :
    markedTensorMap false i (𝟙 markedInterval) ≫ H =
      isTerminalMarkedTensorUnit.from _ ≫ i := by
  apply MarkedPresheaf.hom_ext
  simp only [Functor.map_comp, forget_map_markedTensorMap, hH]
  change (grayTensorRight markedInterval.underlying).map (MarkedPresheaf.forget.map i) ≫
    (grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h = _
  have hn := (Functor.curry.obj grayTensorBifunctor).map
    (MarkedPresheaf.forget.map i) |>.naturality simplexMarkedIntervalIso.inv
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) hn.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg
      ((grayTensorLeft (ball atomPoint)).map simplexMarkedIntervalIso.inv ≫ ·) hr).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ MarkedPresheaf.forget.map i)
          (isTerminalBallAtomPoint.hom_ext _ _))))))

private theorem cellular_sharp_of_contraction {X : DiagSet.{u}}
    (i : markedTensorUnit ⟶ (MarkedPresheaf.sharp atomMarking).obj X) [Mono i]
    (h : grayTensor X (ball (atomSimplex 1)) ⟶ X)
    (hb : (grayTensorLeft X).map intervalBoundaryι ≫ h = grayTensorBoundaryDesc X
      (GrayDiagSet.rightUnitor X).hom
      (grayTensorFst X (ball atomPoint) ≫ isTerminalBallAtomPoint.from X ≫
        MarkedPresheaf.forget.map i))
    (hr : (grayTensorRight (ball (atomSimplex 1))).map (MarkedPresheaf.forget.map i) ≫ h =
      grayTensorFst (ball atomPoint) (ball (atomSimplex 1)) ≫ MarkedPresheaf.forget.map i) :
    MarkedDiagSet.cellularMarkedRightAnodyne i := by
  let H := (MarkedPresheaf.forgetSharpAdjunction atomMarking).homEquiv
    (markedTensor false ((MarkedPresheaf.sharp atomMarking).obj X) markedInterval) X
    ((grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h)
  have hH : MarkedPresheaf.forget.map H =
      (grayTensorLeft X).map simplexMarkedIntervalIso.inv ≫ h := rfl
  have h₀ : markedLastEnd false ((MarkedPresheaf.sharp atomMarking).obj X) ≫ H = 𝟙 _ := by
    apply MarkedPresheaf.hom_ext
    have he := forget_marked_contraction_end i h H hH hb false
    exact he.trans (MarkedPresheaf.forget.map_id
      ((MarkedPresheaf.sharp atomMarking).obj X)).symm
  have h₁ : markedLastEnd true ((MarkedPresheaf.sharp atomMarking).obj X) ≫ H =
      isTerminalMarkedTensorUnit.from _ ≫ i := by
    apply MarkedPresheaf.hom_ext
    have he := forget_marked_contraction_end i h H hH hb true
    exact he.trans ((congrArg (· ≫ MarkedPresheaf.forget.map i)
      (isTerminalBallAtomPoint.hom_ext _
        (MarkedPresheaf.forget.map (isTerminalMarkedTensorUnit.from
          ((MarkedPresheaf.sharp atomMarking).obj X))))).trans
            (MarkedPresheaf.forget.map_comp _ i).symm)
  exact cellular_of_marked_contraction i H h₀ h₁
    (marked_contraction_relative i h H hH hr)

theorem DiagSet.cellularMarkedRightAnodyne_sharpSliceAtId_of_rlp_coneObjectπ
    (S : DiagSet.{u}) (b : S.Vertex)
    (hb : (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (coneObjectπ true (S.sliceAtId b))) :
    MarkedDiagSet.cellularMarkedRightAnodyne (S.sharpSliceAtId b) := by
  have : IsSplitMono (S.sharpSliceAtId b) :=
    isTerminalMarkedTensorUnit.isSplitMono_from (S.sharpSliceAtId b)
  obtain ⟨h, he, hr⟩ := exists_contraction_of_rlp_coneObjectπ (S.sliceAtId b) hb
  exact cellular_sharp_of_contraction (S.sharpSliceAtId b) h he hr

theorem DiagSet.cellularMarkedRightAnodyne_sharpSliceAtId (S : DiagSet.{u})
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    MarkedDiagSet.cellularMarkedRightAnodyne (S.sharpSliceAtId b) :=
  S.cellularMarkedRightAnodyne_sharpSliceAtId_of_rlp_coneObjectπ b
    (S.rlp_monomorphisms_coneObjectπ_sliceAtId b)

theorem DiagSet.markedRightAnodyne_sharpSliceAtId (S : DiagSet.{u})
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex) :
    MarkedDiagSet.markedRightAnodyne (S.sharpSliceAtId b) :=
  MarkedDiagSet.cellularMarkedRightAnodyne_le_markedRightAnodyne _
    (S.cellularMarkedRightAnodyne_sharpSliceAtId b)

theorem DiagSet.trivialFibration_cartesianYoneda_of_rlp_rightCylinderMaps
    {E S : DiagSet.{u}} (p : E ⟶ S) [IsFibrant ((DiagSet.toInfty 1).obj S)] (b : S.Vertex)
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b) :=
  DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_cellularMarkedRightAnodyne p b
    (S.cellularMarkedRightAnodyne_sharpSliceAtId b) hp

theorem DiagSet.cartesianFunOver_comparison_of_rlp_rightCylinderMaps
    {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (b : S.Vertex)
    (hp : MarkedDiagSet.rightCylinderMaps.rlp (DiagSet.cartesianMarkedHom p)) :
    let : SSet.IsCartesianFibration (DiagSet.toSSet.map p) :=
      (DiagSet.isCartesianFibration_iff_toSSet p).1
        (DiagSet.isCartesianFibration_of_rlp_rightCylinderMaps p hp)
    ∃ f : DiagSet.toSSet.obj (DiagSet.cartesianFunOver p b) ⟶
        SSet.cartesianFunOver (DiagSet.toSSet.map p) (S.vertexEquivSSet b),
      WeakEquivalence f ∧
        f ≫ SSet.cartesianYonedaEval (DiagSet.toSSet.map p) (S.vertexEquivSSet b) =
          DiagSet.toSSet.map (DiagSet.cartesianYonedaEval p b) ≫
            (DiagSet.toSSetFiberIso p b).hom := by
  let : SSet.IsCartesianFibration (DiagSet.toSSet.map p) :=
    (DiagSet.isCartesianFibration_iff_toSSet p).1
      (DiagSet.isCartesianFibration_of_rlp_rightCylinderMaps p hp)
  exact DiagSet.cartesianFunOver_comparison_of_rlp p b
    (DiagSet.trivialFibration_cartesianYoneda_of_rlp_rightCylinderMaps p b hp)

end Atoms.Diagrammatic
