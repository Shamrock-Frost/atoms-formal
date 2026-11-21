import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Product
import Atoms.Homotopical.Simplicial.FinalCriterion
import Atoms.Homotopical.Simplicial.JoyalKan
import Atoms.Homotopical.Simplicial.ProductCone

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u v w

namespace SSet

section YonedaSpan

variable {E F X : SSet.{u}}

noncomputable def yonedaSpanLeft (p : E ⟶ X) {e : E _⦋0⦌} {a : X _⦋0⦌} (ha : p.app _ e = a)
    (t : X _⦋0⦌) : pullback (sliceAtπ E e ≫ p) (yonedaEquiv.symm t) ⟶ mappingSpace X t a :=
  fiberMap (sliceAtMapOfEq p ha) (sliceAtMapOfEq_comp_sliceAtπ p ha) t ≫
    sliceAtFibreToMappingSpace X t a

noncomputable abbrev yonedaSpanRight (p : E ⟶ X) (e : E _⦋0⦌) (t : X _⦋0⦌) :
    pullback (sliceAtπ E e ≫ p) (yonedaEquiv.symm t) ⟶ pullback p (yonedaEquiv.symm t) :=
  fiberMap (sliceAtπ E e) rfl t

noncomputable def yonedaSpanMap {Φ : E ⟶ F} {q : F ⟶ X} {p : E ⟶ X} (hΦ : Φ ≫ q = p)
    (e : E _⦋0⦌) (t : X _⦋0⦌) : pullback (sliceAtπ E e ≫ p) (yonedaEquiv.symm t) ⟶
      pullback (sliceAtπ F (Φ.app _ e) ≫ q) (yonedaEquiv.symm t) :=
  fiberMap (sliceAtMap Φ e) (by rw [sliceAtMap_comp_sliceAtπ_assoc, hΦ]) t

@[reassoc]
theorem yonedaSpanMap_comp_yonedaSpanLeft {Φ : E ⟶ F} {q : F ⟶ X} {p : E ⟶ X} (hΦ : Φ ≫ q = p)
    {e : E _⦋0⦌} {a : X _⦋0⦌} (ha : q.app _ (Φ.app _ e) = a) (ha' : p.app _ e = a)
    (t : X _⦋0⦌) : yonedaSpanMap hΦ e t ≫ yonedaSpanLeft q ha t = yonedaSpanLeft p ha' t := by
  rw [yonedaSpanMap, yonedaSpanLeft, yonedaSpanLeft, ← Category.assoc, ← fiberMap_comp]
  congr 2
  exact sliceAtMap_comp_sliceAtMapOfEq hΦ ha ha'

@[reassoc]
theorem yonedaSpanMap_comp_yonedaSpanRight {Φ : E ⟶ F} {q : F ⟶ X} {p : E ⟶ X}
    (hΦ : Φ ≫ q = p) (e : E _⦋0⦌) (t : X _⦋0⦌) :
    yonedaSpanMap hΦ e t ≫ yonedaSpanRight q (Φ.app _ e) t =
      yonedaSpanRight p e t ≫ fiberMap Φ hΦ t := by
  rw [yonedaSpanMap, yonedaSpanRight, yonedaSpanRight, ← fiberMap_comp, ← fiberMap_comp]
  congr 1
  exact sliceAtMap_comp_sliceAtπ Φ e

namespace modelCategoryJoyal

theorem weakEquivalence_yonedaSpanLeft [X.Quasicategory] {p : E ⟶ X} (hp : rightFibrations p)
    {e : E _⦋0⦌} {a : X _⦋0⦌} (ha : p.app _ e = a) (t : X _⦋0⦌) :
    WeakEquivalence (yonedaSpanLeft p ha t) := by
  have := weakEquivalence_of_rlp_I (trivialFibration_fiberMap _
    (sliceAtMapOfEq_comp_sliceAtπ p ha) (trivialFibration_sliceAtMapOfEq hp ha) t)
  have := weakEquivalence_sliceAtFibreToMappingSpace t a
  rw [yonedaSpanLeft]
  infer_instance

theorem isFinal_iff_weakEquivalence_yonedaSpanRight [X.Quasicategory] {p : E ⟶ X}
    (hp : rightFibrations p) (e : E _⦋0⦌) :
    IsFinal e ↔ ∀ t : X _⦋0⦌, WeakEquivalence (yonedaSpanRight p e t) := by
  have := innerFibration_of_rightFibrations hp
  have := quasicategory_of_innerFibration p
  rw [isFinal_iff_weakEquivalence_sliceAtπ]
  exact weakEquivalence_iff_fiberMap
    (rightHornInclusions.rlp.comp_mem _ _ (rightFibrations_sliceAtπ E e) hp) hp _ rfl

end modelCategoryJoyal

end YonedaSpan

section Pair

variable {X : SSet.{u}}

theorem isPullback_sliceToSliceAt_vertexPair (x y : X _⦋0⦌) :
    IsPullback (sliceToSliceAt (vertexPair x y) coprod.inl (coprod.inl_desc _ _))
      (sliceToSliceAt (vertexPair x y) coprod.inr (coprod.inr_desc _ _))
      (sliceAtπ X x) (sliceAtπ X y) := by
  have h := isPullback_sliceRes isPushout_bot_ι_coprod (vertexPair x y)
  have hx : coprod.inl ≫ vertexPair x y = yonedaEquiv.symm x := coprod.inl_desc _ _
  have hy : coprod.inr ≫ vertexPair x y = yonedaEquiv.symm y := coprod.inr_desc _ _
  have (t : Under ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})) : IsIso (sliceπ t) :=
    isIso_sliceπ_of_isEmpty t
  refine h.of_iso (Iso.refl _) (sliceIsoOfEq hx) (sliceIsoOfEq hy) (asIso (sliceπ _)) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (sliceRes_sliceπ _ _).trans (sliceIsoOfEq_hom_sliceπ hx).symm
  · refine ((Category.assoc _ _ _).trans ?_).trans (sliceIsoOfEq_hom_sliceπ hy).symm
    exact (congrArg (sliceRes _ _ ≫ ·) ((slice_map_sliceπ _).trans (Category.comp_id _))).trans
      (sliceRes_sliceπ _ _)

noncomputable def slicePairFibreToMappingSpace (X : SSet.{u}) (t x y : X _⦋0⦌) :
    pullback (sliceπ (Under.mk (vertexPair x y))) (yonedaEquiv.symm t) ⟶
      mappingSpace X t x ⨯ mappingSpace X t y :=
  prod.lift
    (fiberMap (sliceToSliceAt (vertexPair x y) coprod.inl (coprod.inl_desc _ _))
      (sliceToSliceAt_comp_sliceAtπ _ _ _) t ≫ sliceAtFibreToMappingSpace X t x)
    (fiberMap (sliceToSliceAt (vertexPair x y) coprod.inr (coprod.inr_desc _ _))
      (sliceToSliceAt_comp_sliceAtπ _ _ _) t ≫ sliceAtFibreToMappingSpace X t y)

@[reassoc]
theorem slicePairFibreToMappingSpace_fst (t x y : X _⦋0⦌) :
    slicePairFibreToMappingSpace X t x y ≫ prod.fst =
      fiberMap (sliceToSliceAt (vertexPair x y) coprod.inl (coprod.inl_desc _ _))
        (sliceToSliceAt_comp_sliceAtπ _ _ _) t ≫ sliceAtFibreToMappingSpace X t x :=
  prod.lift_fst _ _

@[reassoc]
theorem slicePairFibreToMappingSpace_snd (t x y : X _⦋0⦌) :
    slicePairFibreToMappingSpace X t x y ≫ prod.snd =
      fiberMap (sliceToSliceAt (vertexPair x y) coprod.inr (coprod.inr_desc _ _))
        (sliceToSliceAt_comp_sliceAtπ _ _ _) t ≫ sliceAtFibreToMappingSpace X t y :=
  prod.lift_snd _ _

open modelCategoryJoyal in
theorem modelCategoryJoyal.weakEquivalence_slicePairFibreToMappingSpace [X.Quasicategory]
    (t x y : X _⦋0⦌) : WeakEquivalence (slicePairFibreToMappingSpace X t x y) := by
  have hP := isPullback_fiberMap_of_isPullback (isPullback_sliceToSliceAt_vertexPair x y)
    (sliceToSliceAt_comp_sliceAtπ _ _ _) (sliceToSliceAt_comp_sliceAtπ _ _ _) t
  have : IsIso (prod.lift (fiberMap _ (sliceToSliceAt_comp_sliceAtπ (vertexPair x y) coprod.inl
      (coprod.inl_desc _ _)) t) (fiberMap _ (sliceToSliceAt_comp_sliceAtπ (vertexPair x y)
      coprod.inr (coprod.inr_desc _ _)) t)) :=
    ⟨hP.lift prod.fst prod.snd (stdSimplex.isTerminalObj₀.hom_ext _ _),
      hP.hom_ext (by rw [Category.assoc, hP.lift_fst, prod.lift_fst, Category.id_comp])
        (by rw [Category.assoc, hP.lift_snd, prod.lift_snd, Category.id_comp]),
      by ext <;> simp⟩
  have := kanComplex_fiber_of_rightFibrations (rightFibrations_sliceAtπ X x) t
  have := kanComplex_fiber_of_rightFibrations (rightFibrations_sliceAtπ X y) t
  have := kanComplex_mappingSpace X t x
  have := kanComplex_mappingSpace X t y
  have (Z : SSet.{u}) [Z.KanComplex] : IsFibrant Z :=
    (isFibrant_iff_quasicategory Z).2 inferInstance
  have := weakEquivalence_sliceAtFibreToMappingSpace t x
  have := weakEquivalence_sliceAtFibreToMappingSpace t y
  have := weakEquivalence_prodMap (sliceAtFibreToMappingSpace X t x)
    (sliceAtFibreToMappingSpace X t y)
  rw [slicePairFibreToMappingSpace, ← prod.lift_map]
  infer_instance

noncomputable def pairCompositionSpanRight {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pullback (sliceAtπ _ c ≫ sliceπ (Under.mk (vertexPair x y))) (yonedaEquiv.symm t) ⟶
      mappingSpace X t x ⨯ mappingSpace X t y :=
  yonedaSpanRight (sliceπ (Under.mk (vertexPair x y))) c t ≫ slicePairFibreToMappingSpace X t x y

noncomputable def pairCompositionSpanLeft {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pullback (sliceAtπ _ c ≫ sliceπ (Under.mk (vertexPair x y))) (yonedaEquiv.symm t) ⟶
      mappingSpace X t (productConeApex c) :=
  yonedaSpanLeft (sliceπ (Under.mk (vertexPair x y))) rfl t

open modelCategoryJoyal in
theorem modelCategoryJoyal.weakEquivalence_pairCompositionSpanLeft [X.Quasicategory]
    {x y : X _⦋0⦌} (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    WeakEquivalence (pairCompositionSpanLeft c t) :=
  weakEquivalence_yonedaSpanLeft (X := X) (rightFibrations_sliceπ (vertexPair x y)) rfl t

open modelCategoryJoyal in
theorem modelCategoryJoyal.isProductCone_iff_weakEquivalence_pairCompositionSpanRight
    [X.Quasicategory] {x y : X _⦋0⦌} (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    IsProductCone c ↔ ∀ t : X _⦋0⦌, WeakEquivalence (pairCompositionSpanRight c t) := by
  have := fun t ↦ weakEquivalence_slicePairFibreToMappingSpace t x y
  rw [IsProductCone, isFinal_iff_weakEquivalence_yonedaSpanRight (X := X)
    (rightFibrations_sliceπ (vertexPair x y)) c]
  exact forall_congr' fun t ↦ (weakEquivalence_postcomp_iff _ _).symm

theorem pairCompositionSpanRight_fst {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pairCompositionSpanRight c t ≫ prod.fst =
      yonedaSpanMap (sliceToSliceAt_comp_sliceAtπ (vertexPair x y) coprod.inl
        (coprod.inl_desc _ _)) c t ≫ yonedaSpanRight (sliceAtπ X x) _ t ≫
          sliceAtFibreToMappingSpace X t x := by
  rw [pairCompositionSpanRight, Category.assoc, slicePairFibreToMappingSpace_fst,
    yonedaSpanMap_comp_yonedaSpanRight_assoc]

theorem yonedaSpanMap_inl_comp_yonedaSpanLeft {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    yonedaSpanMap (sliceToSliceAt_comp_sliceAtπ (vertexPair x y) coprod.inl
      (coprod.inl_desc _ _)) c t ≫ yonedaSpanLeft (sliceAtπ X x)
        (sliceAtπ_app_sliceToSliceAt_app _ _ _ c) t = pairCompositionSpanLeft c t :=
  yonedaSpanMap_comp_yonedaSpanLeft _ _ _ t

theorem pairCompositionSpanRight_snd {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pairCompositionSpanRight c t ≫ prod.snd =
      yonedaSpanMap (sliceToSliceAt_comp_sliceAtπ (vertexPair x y) coprod.inr
        (coprod.inr_desc _ _)) c t ≫ yonedaSpanRight (sliceAtπ X y) _ t ≫
          sliceAtFibreToMappingSpace X t y := by
  rw [pairCompositionSpanRight, Category.assoc, slicePairFibreToMappingSpace_snd,
    yonedaSpanMap_comp_yonedaSpanRight_assoc]

theorem yonedaSpanMap_inr_comp_yonedaSpanLeft {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    yonedaSpanMap (sliceToSliceAt_comp_sliceAtπ (vertexPair x y) coprod.inr
      (coprod.inr_desc _ _)) c t ≫ yonedaSpanLeft (sliceAtπ X y)
        (sliceAtπ_app_sliceToSliceAt_app _ _ _ c) t = pairCompositionSpanLeft c t :=
  yonedaSpanMap_comp_yonedaSpanLeft _ _ _ t

end Pair

section Localized

open Atoms.Homotopical

variable {H : Type v} [Category.{w} H] (L : SSet.{u} ⥤ H) [L.IsLocalization kanWeak]
  {E F X : SSet.{u}} [X.Quasicategory]

theorem kanWeak_yonedaSpanLeft {p : E ⟶ X} (hp : rightFibrations p) {e : E _⦋0⦌} {a : X _⦋0⦌}
    (ha : p.app _ e = a) (t : X _⦋0⦌) : kanWeak (yonedaSpanLeft p ha t) :=
  joyal_weakEquivalences_le_kanWeak _
    (modelCategoryJoyal.weakEquivalence_yonedaSpanLeft hp ha t).mem

noncomputable def yonedaMapHo {p : E ⟶ X} (hp : rightFibrations p) {e : E _⦋0⦌} {a : X _⦋0⦌}
    (ha : p.app _ e = a) (t : X _⦋0⦌) :
    L.obj (mappingSpace X t a) ⟶ L.obj (pullback p (yonedaEquiv.symm t)) :=
  (Localization.isoOfHom L kanWeak _ (kanWeak_yonedaSpanLeft hp ha t)).inv ≫
    L.map (yonedaSpanRight p e t)

@[reassoc]
theorem map_yonedaSpanLeft_comp_yonedaMapHo {p : E ⟶ X} (hp : rightFibrations p) {e : E _⦋0⦌}
    {a : X _⦋0⦌} (ha : p.app _ e = a) (t : X _⦋0⦌) :
    L.map (yonedaSpanLeft p ha t) ≫ yonedaMapHo L hp ha t = L.map (yonedaSpanRight p e t) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

theorem yonedaMapHo_comp_map_fiberMap {Φ : E ⟶ F} {q : F ⟶ X} {p : E ⟶ X} (hΦ : Φ ≫ q = p)
    (hq : rightFibrations q) (hp : rightFibrations p) {e : E _⦋0⦌} {a : X _⦋0⦌}
    (ha : q.app _ (Φ.app _ e) = a) (ha' : p.app _ e = a) (t : X _⦋0⦌) :
    yonedaMapHo L hp ha' t ≫ L.map (fiberMap Φ hΦ t) = yonedaMapHo L hq ha t := by
  rw [← (Localization.isoOfHom L kanWeak _ (kanWeak_yonedaSpanLeft hp ha' t)).cancel_iso_hom_left,
    Localization.isoOfHom_hom, map_yonedaSpanLeft_comp_yonedaMapHo_assoc, ← L.map_comp,
    ← yonedaSpanMap_comp_yonedaSpanRight hΦ e t, L.map_comp,
    ← map_yonedaSpanLeft_comp_yonedaMapHo L hq ha t, ← L.map_comp_assoc,
    yonedaSpanMap_comp_yonedaSpanLeft hΦ ha ha' t]

open modelCategoryJoyal in
theorem isFinal_iff_isIso_yonedaMapHo {p : E ⟶ X} (hp : rightFibrations p) {e : E _⦋0⦌}
    {a : X _⦋0⦌} (ha : p.app _ e = a) :
    IsFinal e ↔ ∀ t : X _⦋0⦌, IsIso (yonedaMapHo L hp ha t) := by
  have := innerFibration_of_rightFibrations hp
  have := quasicategory_of_innerFibration p
  rw [isFinal_iff_weakEquivalence_yonedaSpanRight hp e]
  refine forall_congr' fun t ↦ ?_
  have := kanComplex_fiber_of_rightFibrations hp t
  have := kanComplex_fiber_of_rightFibrations
    (rightHornInclusions.rlp.comp_mem _ _ (rightFibrations_sliceAtπ E e) hp) t
  rw [yonedaMapHo, isIso_comp_left_iff, ← kanWeak_iff_isIso_map L,
    ← joyal_weakEquivalences_iff_kanWeak]
  exact weakEquivalence_iff _

noncomputable def pairCompositionHo {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    L.obj (mappingSpace X t (productConeApex c)) ⟶
      L.obj (mappingSpace X t x ⨯ mappingSpace X t y) :=
  yonedaMapHo L (X := X) (rightFibrations_sliceπ (vertexPair x y))
      (rfl : _ = productConeApex c) t ≫
    L.map (slicePairFibreToMappingSpace X t x y)

theorem map_pairCompositionSpanLeft_comp_pairCompositionHo {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    L.map (pairCompositionSpanLeft c t) ≫ pairCompositionHo L c t =
      L.map (pairCompositionSpanRight c t) :=
  (map_yonedaSpanLeft_comp_yonedaMapHo_assoc L (X := X) (rightFibrations_sliceπ (vertexPair x y))
    (rfl : _ = productConeApex c) t _).trans (L.map_comp _ _).symm

theorem pairCompositionHo_comp_map_fst {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pairCompositionHo L c t ≫ L.map prod.fst =
      yonedaMapHo L (rightFibrations_sliceAtπ X x) (sliceAtπ_app_sliceToSliceAt_app
        (vertexPair x y) coprod.inl (coprod.inl_desc _ _) c) t ≫
          L.map (sliceAtFibreToMappingSpace X t x) := by
  rw [pairCompositionHo, Category.assoc, ← L.map_comp, slicePairFibreToMappingSpace_fst,
    L.map_comp, ← Category.assoc]
  exact congrArg (· ≫ L.map (sliceAtFibreToMappingSpace X t x))
    (yonedaMapHo_comp_map_fiberMap L (sliceToSliceAt_comp_sliceAtπ _ _ _)
      (rightFibrations_sliceAtπ X x) _ _ _ t)

theorem pairCompositionHo_comp_map_snd {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) (t : X _⦋0⦌) :
    pairCompositionHo L c t ≫ L.map prod.snd =
      yonedaMapHo L (rightFibrations_sliceAtπ X y) (sliceAtπ_app_sliceToSliceAt_app
        (vertexPair x y) coprod.inr (coprod.inr_desc _ _) c) t ≫
          L.map (sliceAtFibreToMappingSpace X t y) := by
  rw [pairCompositionHo, Category.assoc, ← L.map_comp, slicePairFibreToMappingSpace_snd,
    L.map_comp, ← Category.assoc]
  exact congrArg (· ≫ L.map (sliceAtFibreToMappingSpace X t y))
    (yonedaMapHo_comp_map_fiberMap L (sliceToSliceAt_comp_sliceAtπ _ _ _)
      (rightFibrations_sliceAtπ X y) _ _ _ t)

theorem isProductCone_iff_isIso_pairCompositionHo {x y : X _⦋0⦌}
    (c : ((slice _).obj (Under.mk (vertexPair x y))) _⦋0⦌) :
    IsProductCone c ↔ ∀ t : X _⦋0⦌, IsIso (pairCompositionHo L c t) := by
  rw [IsProductCone, isFinal_iff_isIso_yonedaMapHo L (X := X)
    (rightFibrations_sliceπ (vertexPair x y)) (rfl : _ = productConeApex c)]
  refine forall_congr' fun t ↦ ?_
  have : IsIso (L.map (slicePairFibreToMappingSpace X t x y)) :=
    (kanWeak_iff_isIso_map L _).1 (joyal_weakEquivalences_le_kanWeak _
      (modelCategoryJoyal.weakEquivalence_slicePairFibreToMappingSpace t x y).mem)
  rw [pairCompositionHo, isIso_comp_right_iff]

end Localized

end SSet
