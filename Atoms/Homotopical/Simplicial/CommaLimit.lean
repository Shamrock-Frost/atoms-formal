import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpace
import Atoms.Homotopical.Simplicial.FatJoin
import Atoms.Homotopical.Simplicial.FinalObject

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

section Comparison

noncomputable def sliceToCommaCone {K X : SSet.{u}} (d : K ⟶ X) :
    (slice K).obj (Under.mk d) ⟶ commaCone d :=
  (sliceToFatSlice K).app (Under.mk d) ≫ (commaConeIsoFatSlice d).inv

@[reassoc]
theorem sliceToCommaCone_commaConeπ {K X : SSet.{u}} (d : K ⟶ X) :
    sliceToCommaCone d ≫ commaConeπ d = sliceπ (Under.mk d) := by
  rw [sliceToCommaCone, Category.assoc, commaConeIsoFatSlice_inv_commaConeπ,
    Adjunction.homEquiv_counit, sliceToFatSlice, conjugateEquiv_counit, Under.comp_right]
  exact fatJoinInclLeft_fatJoinToJoin_assoc _ _ _

namespace modelCategoryJoyal

theorem weakEquivalence_sliceToCommaCone {K X : SSet.{u}} [X.Quasicategory] (d : K ⟶ X) :
    WeakEquivalence (sliceToCommaCone d) := by
  have := weakEquivalence_sliceToFatSlice d
  rw [sliceToCommaCone]
  infer_instance

theorem isFinal_iff_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (F : X ⟶ Y) [WeakEquivalence F] (x : X _⦋0⦌) : IsFinal (F.app _ x) ↔ IsFinal x := by
  let φ : Under.mk (yonedaEquiv.symm x) ⟶ Under.mk (yonedaEquiv.symm (F.app _ x)) :=
    Under.homMk F (yonedaEquiv_symm_comp x F)
  have : WeakEquivalence φ := (weakEquivalences_under_iff _ _).2 ‹_›
  have : IsFibrant (Under.mk (yonedaEquiv.symm x)) :=
    (isFibrant_under_iff _ _).2 ((isFibrant_iff_quasicategory X).2 inferInstance)
  have : IsFibrant (Under.mk (yonedaEquiv.symm (F.app _ x))) :=
    (isFibrant_under_iff _ _).2 ((isFibrant_iff_quasicategory Y).2 inferInstance)
  have := (isQuillen_joinRightUnderAdjunction Δ[0]).weakEquivalence_map_of_isFibrant φ
  have h : (slice Δ[0]).map φ ≫ sliceAtπ Y (F.app _ x) = sliceAtπ X x ≫ F :=
    slice_map_sliceπ φ
  rw [isFinal_iff_weakEquivalence_sliceAtπ, isFinal_iff_weakEquivalence_sliceAtπ]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : WeakEquivalence (sliceAtπ X x ≫ F) := by
      rw [← h]
      infer_instance
    exact weakEquivalence_of_postcomp _ F
  · have : WeakEquivalence ((slice Δ[0]).map φ ≫ sliceAtπ Y (F.app _ x)) := by
      rw [h]
      infer_instance
    exact weakEquivalence_of_precomp ((slice Δ[0]).map φ) _

end modelCategoryJoyal

open modelCategoryJoyal in
theorem isFinal_iff_isLimitCone_sliceToCommaCone {K X : SSet.{u}} [X.Quasicategory] (d : K ⟶ X)
    (w : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    IsFinal w ↔ IsLimitCone d ((sliceToCommaCone d).app _ w) :=
  have : (Under.mk d).right.Quasicategory := ‹X.Quasicategory›
  have := weakEquivalence_sliceToCommaCone d
  (isFinal_iff_of_weakEquivalence (sliceToCommaCone d) w).symm

end Comparison

section MappingSpace

noncomputable def mappingSpaceIsoOfIso {X Y : SSet.{u}} (e : X ≅ Y) {x y : X _⦋0⦌}
    {x' y' : Y _⦋0⦌} (hx : e.hom.app _ x = x') (hy : e.hom.app _ y = y') :
    mappingSpace X x y ≅ mappingSpace Y x' y' :=
  IsPullback.isoPullback (IsPullback.of_iso (IsPullback.of_hasPullback _ _) (Iso.refl _)
    ((ihom Δ[1]).mapIso e) (Iso.refl _) (e ⊗ᵢ e) (Category.id_comp _).symm
    (Category.id_comp _).symm
    (by
      ext1
      · simp [ihomStdSimplexOneEval, ihom_map_comp_evalVertex]
      · simp [ihomStdSimplexOneEval, ihom_map_comp_evalVertex])
    (by
      ext1
      · simp [← hx]
      · simp [← hy]))

end MappingSpace

section Fibres

open modelCategoryJoyal in
theorem modelCategoryJoyal.fibration_sliceAtπ (X : SSet.{u}) [X.Quasicategory] (y : X _⦋0⦌) :
    Fibration (sliceAtπ X y) := by
  have hπ := rightFibrations_sliceAtπ X y
  have : InnerFibration (sliceAtπ X y) := innerFibration_of_rightFibrations hπ
  have : (Under.mk (yonedaEquiv.symm y)).right.Quasicategory := ‹X.Quasicategory›
  exact (fibration_iff_isofibration _).2 (Isofibration.of_hasLiftingProperty_vertex _
    (rightAnodyneExtensions_coherentIso_vertex false _ hπ))

private lemma ihomStdSimplexZeroIso_hom_app_constDiagram (X : SSet.{u}) (x : X _⦋0⦌) :
    (ihomStdSimplexZeroIso X).hom.app _ ((constDiagram Δ[0] X).app _ x) = x :=
  ConcreteCategory.congr_hom (congr_app (ihomStdSimplexZeroIso X).inv_hom_id _) x

private lemma ihomStdSimplexZeroIso_hom_app_ihomPointEquiv (X : SSet.{u}) (y : X _⦋0⦌) :
    (ihomStdSimplexZeroIso X).hom.app _
      (yonedaEquiv ((ihomPointEquiv Δ[0] X).symm (yonedaEquiv.symm y))) = y := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp, Equiv.symm_apply_apply]
  have h : (ihomPointEquiv Δ[0] X).symm (yonedaEquiv.symm y) =
      yonedaEquiv.symm y ≫ (ihomStdSimplexZeroIso X).inv := by
    have hinv : (ihomStdSimplexZeroIso X).inv = constDiagram Δ[0] X := rfl
    rw [hinv, constDiagram, ← curry_natural_left, whiskerLeft_snd]
    exact congrArg curry (congrArg (· ≫ yonedaEquiv.symm y)
      (stdSimplex.isTerminalObj₀.hom_ext _ _))
  rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def sliceAtFibreToMappingSpace (X : SSet.{u}) (x y : X _⦋0⦌) :
    pullback (sliceAtπ X y) (yonedaEquiv.symm x) ⟶ mappingSpace X x y :=
  pullback.map _ _ _ _ (sliceToCommaCone (yonedaEquiv.symm y)) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, sliceToCommaCone_commaConeπ]; rfl)
      (by rw [Category.comp_id, Category.id_comp]) ≫
    (commaConeFibreIsoMappingSpace (yonedaEquiv.symm y) x).hom ≫
      (mappingSpaceIsoOfIso (ihomStdSimplexZeroIso X)
        (ihomStdSimplexZeroIso_hom_app_constDiagram X x)
        (ihomStdSimplexZeroIso_hom_app_ihomPointEquiv X y)).hom

open modelCategoryJoyal in
theorem modelCategoryJoyal.weakEquivalence_sliceAtFibreToMappingSpace {X : SSet.{u}}
    [X.Quasicategory] (x y : X _⦋0⦌) : WeakEquivalence (sliceAtFibreToMappingSpace X x y) := by
  have := fibration_sliceAtπ X y
  have : Fibration (commaConeπ (yonedaEquiv.symm y)) :=
    (fibration_iff_isofibration _).2 (isofibration_commaConeπ _)
  have := weakEquivalence_sliceToCommaCone (yonedaEquiv.symm y)
  have := weakEquivalence_pullback_map_of_fibration (yonedaEquiv.symm x) (sliceAtπ X y)
    (commaConeπ (yonedaEquiv.symm y)) (sliceToCommaCone (yonedaEquiv.symm y))
    (sliceToCommaCone_commaConeπ _)
  rw [sliceAtFibreToMappingSpace]
  infer_instance

open modelCategoryJoyal in
private lemma rlp_iff_of_weakEquivalence {F G : SSet.{u}} (φ : F ⟶ G) [WeakEquivalence φ]
    (p : F ⟶ Δ[0]) (q : G ⟶ Δ[0]) [Fibration p] [Fibration q] :
    modelCategoryQuillen.I.rlp p ↔ modelCategoryQuillen.I.rlp q := by
  have h {Z : SSet.{u}} (r : Z ⟶ Δ[0]) [Fibration r] :
      modelCategoryQuillen.I.rlp r ↔ WeakEquivalence r := by
    rw [← rlp_monomorphisms]
    change (cofibrations SSet.{u}).rlp _ ↔ _
    rw [cofibrations_rlp, mem_trivialFibrations_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩
  have hpq : φ ≫ q = p := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, h, ← hpq]
  exact ⟨fun _ ↦ weakEquivalence_of_precomp φ q, fun _ ↦ inferInstance⟩

open modelCategoryJoyal in
theorem isFinal_iff_mappingSpace {X : SSet.{u}} [X.Quasicategory] (ω : X _⦋0⦌) :
    IsFinal ω ↔ ∀ x : X _⦋0⦌,
      modelCategoryQuillen.I.rlp (stdSimplex.isTerminalObj₀.from (mappingSpace X x ω)) := by
  rw [isFinal_iff_trivialFibration_fiber]
  refine forall_congr' fun x ↦ ?_
  have := fibration_sliceAtπ X ω
  have : Fibration (pullback.snd (sliceAtπ X ω) (yonedaEquiv.symm x)) := by
    rw [fibration_iff] at this ⊢
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) this
  have := kanComplex_mappingSpace X x ω
  have : Fibration (stdSimplex.isTerminalObj₀.from (mappingSpace X x ω)) :=
    (isFibrant_iff_of_isTerminal _ stdSimplex.isTerminalObj₀).1
      ((isFibrant_iff_quasicategory _).2 inferInstance)
  have := weakEquivalence_sliceAtFibreToMappingSpace x ω
  exact rlp_iff_of_weakEquivalence (sliceAtFibreToMappingSpace X x ω) _ _

end Fibres

end SSet

open SSet.modelCategoryJoyal in
theorem SSet.modelCategoryJoyal.isFinal_iff_weakEquivalence_commaConeπ
    {X : SSet.{u}} [X.Quasicategory]
    (x : X _⦋0⦌) : SSet.IsFinal x ↔ WeakEquivalence (SSet.commaConeπ
      (SSet.yonedaEquiv.symm x)) := by
  have := SSet.modelCategoryJoyal.weakEquivalence_sliceToCommaCone
    (SSet.yonedaEquiv.symm x)
  rw [SSet.modelCategoryJoyal.isFinal_iff_weakEquivalence_sliceAtπ]
  change WeakEquivalence (SSet.sliceπ (Under.mk (SSet.yonedaEquiv.symm x))) ↔ _
  rw [← SSet.sliceToCommaCone_commaConeπ]
  exact ⟨fun _ ↦ weakEquivalence_of_precomp (SSet.sliceToCommaCone _) _, fun _ ↦ inferInstance⟩
