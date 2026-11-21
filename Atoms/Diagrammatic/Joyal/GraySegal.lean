import Atoms.Diagrammatic.Joyal.NativeSpine

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

noncomputable def graySpineVerticesι (p : ℕ) :
    graySimplexVertices.{u} p ⟶ nativeGraySpine.{u} p :=
  Sigma.desc (nativeGraySpineVertex p)

theorem intervalSource_comp_graySpineEdge (p : ℕ) (i : Fin p) :
    intervalSource ≫ nativeGraySpineEdge.{u} p i =
      Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) i.castSucc ≫ graySpineVerticesι p := by
  rw [graySpineVerticesι, Sigma.ι_desc]
  exact intervalSource_nativeGraySpineEdge p i

theorem intervalTarget_comp_graySpineEdge (p : ℕ) (i : Fin p) :
    intervalTarget ≫ nativeGraySpineEdge.{u} p i =
      Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) i.succ ≫ graySpineVerticesι p := by
  rw [graySpineVerticesι, Sigma.ι_desc]
  exact intervalTarget_nativeGraySpineEdge p i

noncomputable def graySpineSubcomplexDesc {T X : DiagSet.{u}} {p : ℕ}
    (x : Fin (p + 1) → X.Vertex)
    (F : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hF : ∀ i, IsFixedEnds (x i.castSucc) (x i.succ) (F i)) :
    grayTensor T (nativeGraySpine p) ⟶ X :=
  nativeGraySpineTensorDesc (fun k => grayTensorSnd T _ ≫ vertexHom (x k)) F
    (fun i => (hF i).1) (fun i => (hF i).2)

theorem grayTensorLeft_map_ι_graySpineVerticesι_graySpineSubcomplexDesc
    {T X : DiagSet.{u}} {p : ℕ} (x : Fin (p + 1) → X.Vertex)
    (F : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hF : ∀ i, IsFixedEnds (x i.castSucc) (x i.succ) (F i)) (k : Fin (p + 1)) :
    (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ graySpineVerticesι p) ≫
      graySpineSubcomplexDesc x F hF = grayTensorSnd T _ ≫ vertexHom (x k) := by
  rw [graySpineVerticesι, Sigma.ι_desc]
  exact nativeGraySpineVertex_tensorDesc _ _ _ _ k

theorem grayTensorLeft_map_graySpineEdge_graySpineSubcomplexDesc
    {T X : DiagSet.{u}} {p : ℕ} (x : Fin (p + 1) → X.Vertex)
    (F : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hF : ∀ i, IsFixedEnds (x i.castSucc) (x i.succ) (F i)) (i : Fin p) :
    (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ graySpineSubcomplexDesc x F hF = F i :=
  nativeGraySpineEdge_tensorDesc _ _ _ _ i

noncomputable def graySpineDesc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    grayTensor T (nativeGraySpine 2) ⟶ X :=
  nativeGraySpineTensorDesc
    ![(grayTensorLeft T).map intervalSource ≫ F₀₁,
      (grayTensorLeft T).map intervalTarget ≫ F₀₁,
      (grayTensorLeft T).map intervalTarget ≫ F₁₂]
    ![F₀₁, F₁₂]
    (by
      intro i
      fin_cases i
      · rfl
      · exact h.symm)
    (by intro i; fin_cases i <;> rfl)

private noncomputable def simplexVertexMap (p : ℕ) (k : Fin (p + 1)) :
    ball.{u} atomPoint ⟶ ball.{u} (atomSimplex p) :=
  uliftYoneda.map (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom)

private noncomputable def simplexEdgeMap (p : ℕ) (i : Fin p) :
    ball.{u} (atomSimplex 1) ⟶ ball.{u} (atomSimplex p) :=
  uliftYoneda.map (simplexHom (SimplexCategory.mkOfSucc i).toOrderHom)

private theorem simplexEdgeMap_source (p : ℕ) (i : Fin p) :
    intervalSource ≫ simplexEdgeMap.{u} p i = simplexVertexMap p i.castSucc := by
  change (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.δ 1) ≫
    (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.mkOfSucc i) = _
  rw [← Functor.map_comp]
  exact congrArg (simplexFunctor ⋙ uliftYoneda.{u}).map
    (SimplexCategory.Hom.ext_zero_left _ _ rfl)

private theorem simplexEdgeMap_target (p : ℕ) (i : Fin p) :
    intervalTarget ≫ simplexEdgeMap.{u} p i = simplexVertexMap p i.succ := by
  change (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.δ 0) ≫
    (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.mkOfSucc i) = _
  rw [← Functor.map_comp]
  exact congrArg (simplexFunctor ⋙ uliftYoneda.{u}).map
    (SimplexCategory.Hom.ext_zero_left _ _ rfl)

noncomputable def nativeGraySpineι (p : ℕ) :
    nativeGraySpine.{u} p ⟶ ball.{u} (atomSimplex p) :=
  nativeGraySpineDesc (simplexVertexMap p) (simplexEdgeMap p)
    (simplexEdgeMap_source p) (simplexEdgeMap_target p)

@[reassoc]
theorem nativeGraySpineVertex_ι (p : ℕ) (k : Fin (p + 1)) :
    nativeGraySpineVertex.{u} p k ≫ nativeGraySpineι p =
      uliftYoneda.map (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom) :=
  nativeGraySpineVertex_desc _ _ (simplexEdgeMap_source p) (simplexEdgeMap_target p) k

@[reassoc]
theorem nativeGraySpineEdge_ι (p : ℕ) (i : Fin p) :
    nativeGraySpineEdge.{u} p i ≫ nativeGraySpineι p =
      uliftYoneda.map (simplexHom (SimplexCategory.mkOfSucc i).toOrderHom) :=
  nativeGraySpineEdge_desc _ _ (simplexEdgeMap_source p) (simplexEdgeMap_target p) i

noncomputable def graySimplexVerticesι (p : ℕ) :
    graySimplexVertices.{u} p ⟶ ball.{u} (atomSimplex p) :=
  graySpineVerticesι p ≫ nativeGraySpineι p

noncomputable abbrev graySimplexFibre (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : DiagSet.{u} :=
  relativeMappingSpace (graySimplexVerticesι p) ((graySimplexVerticesHomEquiv p X).symm x)

noncomputable abbrev graySpineFibre (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : DiagSet.{u} :=
  relativeMappingSpace (graySpineVerticesι p) ((graySimplexVerticesHomEquiv p X).symm x)

noncomputable def graySegalMap (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : graySimplexFibre X x ⟶ graySpineFibre X x :=
  relativeMappingSpaceRestrict (graySpineVerticesι p) (nativeGraySpineι p) _

theorem relativeMappingSpaceHomEquiv_graySegalMap (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) {T : DiagSet.{u}} (t : T ⟶ graySimplexFibre X x) :
    (relativeMappingSpaceHomEquiv _ _ T (t ≫ graySegalMap X x)).1 =
      (grayTensorLeft T).map (nativeGraySpineι p) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 :=
  relativeMappingSpaceHomEquiv_relativeMappingSpaceRestrict _ _ _ t

@[reassoc]
theorem graySpineVerticesι_comparison (p : ℕ) :
    graySpineVerticesι.{u} p ≫ (nativeSpineToDiagSetIso p).hom = legacyGraySpineVerticesι p := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [graySpineVerticesι, Sigma.ι_desc_assoc]
  change nativeGraySpineVertex p k ≫ nativeSpineToDiagSet p = _
  exact nativeGraySpineVertex_desc _ _ (intervalSource_comp_legacyGraySpineEdge p)
    (intervalTarget_comp_legacyGraySpineEdge p) k

@[reassoc]
theorem nativeGraySpineι_comparison (p : ℕ) :
    nativeGraySpineι.{u} p = (nativeSpineToDiagSetIso p).hom ≫
      SSet.toDiagSet.map (SSet.spineSubcomplex p).ι ≫ (toDiagSetObjStdSimplexIso p).hom := by
  apply nativeGraySpine_hom_ext
  · intro k
    dsimp only [nativeSpineToDiagSetIso]
    rw [nativeGraySpineι, nativeGraySpineVertex_desc, nativeSpineToDiagSet,
      nativeGraySpineVertex_desc_assoc]
    change simplexVertexMap p k = Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫
      legacyGraySimplexVerticesι p ≫ (toDiagSetObjStdSimplexIso p).hom
    exact (ι_graySimplexVerticesι_comp_hom p k).symm
  · intro i
    dsimp only [nativeSpineToDiagSetIso]
    rw [nativeGraySpineι, nativeGraySpineEdge_desc, nativeSpineToDiagSet,
      nativeGraySpineEdge_desc_assoc, ← Category.assoc,
      legacyGraySpineEdge_comp_ι, Category.assoc,
      toDiagSet_map_stdSimplex_map_comp_hom, Iso.inv_hom_id_assoc]
    rfl

private theorem simplexVertices_comparison (p : ℕ) :
    graySimplexVerticesι.{u} p =
      legacyGraySimplexVerticesι p ≫ (toDiagSetObjStdSimplexIso p).hom := by
  rw [graySimplexVerticesι, nativeGraySpineι_comparison, ← Category.assoc,
    graySpineVerticesι_comparison]
  rfl

noncomputable def nativeGraySimplexFibreIso (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : graySimplexFibre X x ≅ legacyGraySimplexFibre X x :=
  relativeMappingSpaceIsoOfIso (Iso.refl _) (toDiagSetObjStdSimplexIso p).symm
    (by rw [Iso.symm_hom, simplexVertices_comparison, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.refl_hom, Category.id_comp])
    (by rw [Iso.refl_hom, Category.id_comp])

noncomputable def nativeGraySpineFibreIso (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : graySpineFibre X x ≅ legacyGraySpineFibre X x :=
  relativeMappingSpaceIsoOfIso (Iso.refl _) (nativeSpineToDiagSetIso p)
    (by rw [graySpineVerticesι_comparison, Iso.refl_hom, Category.id_comp])
    (by rw [Iso.refl_hom, Category.id_comp])

theorem isInftyCategory_zero_graySimplexFibre {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) : IsInftyCategory 0 (graySimplexFibre X x) :=
  isInftyCategory_of_iso (nativeGraySimplexFibreIso X x)
    (isInftyCategory_zero_legacyGraySimplexFibre hX x)

@[reassoc]
theorem graySpineEdge_comparison (p : ℕ) (i : Fin p) :
    nativeGraySpineEdge.{u} p i ≫ (nativeSpineToDiagSetIso p).hom = legacyGraySpineEdge p i :=
  nativeGraySpineEdge_desc _ _ (intervalSource_comp_legacyGraySpineEdge p)
    (intervalTarget_comp_legacyGraySpineEdge p) i

theorem graySpineSubcomplexDesc_comparison {T X : DiagSet.{u}} {p : ℕ}
    (x : Fin (p + 1) → X.Vertex)
    (F : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hF : ∀ i, IsFixedEnds (x i.castSucc) (x i.succ) (F i)) :
    (grayTensorLeft T).map (nativeSpineToDiagSetIso p).hom ≫
      legacyGraySpineSubcomplexDesc x F hF = graySpineSubcomplexDesc x F hF := by
  apply nativeGraySpineTensor_hom_ext
  · intro k
    rw [← Category.assoc, ← Functor.map_comp]
    change (grayTensorLeft T).map
      (nativeGraySpineVertex p k ≫ nativeSpineToDiagSet p) ≫ _ = _
    rw [nativeSpineToDiagSet, nativeGraySpineVertex_desc,
      grayTensorLeft_map_ι_graySpineVerticesι_legacyGraySpineSubcomplexDesc]
    exact (nativeGraySpineVertex_tensorDesc (fun k => grayTensorSnd T _ ≫ vertexHom (x k))
      F (fun i => (hF i).1) (fun i => (hF i).2) k).symm
  · intro i
    rw [← Category.assoc, ← Functor.map_comp, graySpineEdge_comparison,
      grayTensorLeft_map_legacyGraySpineEdge_legacyGraySpineSubcomplexDesc,
      grayTensorLeft_map_graySpineEdge_graySpineSubcomplexDesc]

@[reassoc]
theorem graySegalMap_comparison (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    graySegalMap X x ≫ (nativeGraySpineFibreIso X x).hom =
      (nativeGraySimplexFibreIso X x).hom ≫ legacyGraySegalMap X x := by
  apply (relativeMappingSpaceHomEquiv _ _ _).injective
  apply Subtype.ext
  have hid : (relativeMappingSpaceHomEquiv _ _ _ (graySegalMap X x)).1 =
      (grayTensorLeft (graySimplexFibre X x)).map (nativeGraySpineι p) ≫
        (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySimplexFibre X x))).1 := by
    simpa only [Category.id_comp] using relativeMappingSpaceHomEquiv_graySegalMap X x (𝟙 _)
  have hi : (relativeMappingSpaceHomEquiv _ _ _ (nativeGraySimplexFibreIso X x).hom).1 =
      (grayTensorLeft (graySimplexFibre X x)).map (toDiagSetObjStdSimplexIso p).hom ≫
        (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySimplexFibre X x))).1 := by
    simpa only [Category.id_comp, nativeGraySimplexFibreIso, Iso.symm_inv] using
      relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso (Iso.refl _)
        (toDiagSetObjStdSimplexIso p).symm
        (by rw [Iso.symm_hom, simplexVertices_comparison, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, Iso.refl_hom, Category.id_comp])
        (by rw [Iso.refl_hom, Category.id_comp]) (𝟙 (graySimplexFibre X x))
  rw [nativeGraySpineFibreIso,
    relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso, hid,
    relativeMappingSpaceHomEquiv_legacyGraySegalMap, hi,
    ← Category.assoc, ← Functor.map_comp, nativeGraySpineι_comparison,
    Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]

theorem rlp_monomorphisms_graySegalMap {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (graySegalMap X x) := by
  have h₁ : (monomorphisms DiagSet.{u}).rlp (nativeGraySimplexFibreIso X x).hom :=
    fun _ _ _ _ => inferInstance
  have h := (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ h₁
    (rlp_monomorphisms_legacyGraySegalMap hX x)
  have hw : graySegalMap X x =
      (nativeGraySimplexFibreIso X x).hom ≫ legacyGraySegalMap X x ≫
        (nativeGraySpineFibreIso X x).inv := by
    rw [← graySegalMap_comparison_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hw, ← Category.assoc]
  exact (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ h (fun _ _ _ _ => inferInstance)

theorem grayTensor_spineSubcomplex_hom_ext {p : ℕ} {T X : DiagSet.{u}}
    {f g : grayTensor T (nativeGraySpine p) ⟶ X}
    (hv : ∀ k, (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ graySpineVerticesι p) ≫ f =
      (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ graySpineVerticesι p) ≫ g)
    (he : ∀ i, (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ f =
      (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ g) : f = g := by
  apply nativeGraySpineTensor_hom_ext
  · intro k
    simpa only [graySpineVerticesι, Sigma.ι_desc] using hv k
  · exact he

section NativeProduct

variable (X : DiagSet.{u}) {p : ℕ} (x : Fin (p + 1) → X.Vertex)

private noncomputable def nativeSpineFibreHom {T : DiagSet.{u}} (t : T ⟶ graySpineFibre X x) :
    T ⟶ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor :=
  Pi.lift fun i => (X.mappingSpaceHomEquiv _ _ T).symm
    ⟨(grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ (relativeMappingSpaceHomEquiv _ _ T t).1,
      isFixedEnds_grayTensorLeft_map_comp _ x (relativeMappingSpaceHomEquiv _ _ T t).2
        (intervalSource_comp_graySpineEdge p i) (intervalTarget_comp_graySpineEdge p i)⟩

private theorem nativeSpineFibreHom_π {T : DiagSet.{u}} (t : T ⟶ graySpineFibre X x) (i : Fin
  p) :
    (X.mappingSpaceHomEquiv _ _ T (nativeSpineFibreHom X x t ≫ Pi.π _ i)).1 =
      (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [nativeSpineFibreHom, Pi.lift_π, Equiv.apply_symm_apply]

private noncomputable def nativeSpineFibreInv {T : DiagSet.{u}}
    (s : T ⟶ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor) :
    T ⟶ graySpineFibre X x :=
  (relativeMappingSpaceHomEquiv _ _ T).symm
    ⟨graySpineSubcomplexDesc x (fun i => (X.mappingSpaceHomEquiv _ _ T (s ≫ Pi.π _ i)).1)
      (fun i => (X.mappingSpaceHomEquiv _ _ T (s ≫ Pi.π _ i)).2), by
      refine grayTensor_sigma_hom_ext T _ fun k => ?_
      rw [← Category.assoc, ← Functor.map_comp,
        grayTensorLeft_map_ι_graySpineVerticesι_graySpineSubcomplexDesc, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, ι_graySimplexVerticesHomEquiv_symm]⟩

private theorem nativeSpineFibreHom_comp {T T' : DiagSet.{u}} (g : T' ⟶ T)
    (t : T ⟶ graySpineFibre X x) :
    nativeSpineFibreHom X x (g ≫ t) = g ≫ nativeSpineFibreHom X x t :=
  Pi.hom_ext _ _ fun i => (X.mappingSpaceHomEquiv _ _ T').injective (Subtype.ext (by
    rw [nativeSpineFibreHom_π, Category.assoc, DiagSet.mappingSpaceHomEquiv_comp,
      nativeSpineFibreHom_π, relativeMappingSpaceHomEquiv_comp, ← Category.assoc,
      ← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map]))

noncomputable def graySpineFibreIso :
    graySpineFibre X x ≅ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x
      i.succ)).toFunctor :=
  Yoneda.ext _ _ (nativeSpineFibreHom X x) (nativeSpineFibreInv X x)
    (fun {T} t => (relativeMappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
      rw [nativeSpineFibreInv, Equiv.apply_symm_apply]
      dsimp only
      refine grayTensor_spineSubcomplex_hom_ext (fun k => ?_) (fun i => ?_)
      · rw [grayTensorLeft_map_ι_graySpineVerticesι_graySpineSubcomplexDesc,
          grayTensorLeft_map_ι_comp_of_comp_eq _ x (relativeMappingSpaceHomEquiv _ _ T t).2]
      · rw [grayTensorLeft_map_graySpineEdge_graySpineSubcomplexDesc, nativeSpineFibreHom_π])))
    (fun {T} s => Pi.hom_ext _ _ fun i => (X.mappingSpaceHomEquiv _ _ T).injective
      (Subtype.ext (by
        rw [nativeSpineFibreHom_π, nativeSpineFibreInv, Equiv.apply_symm_apply]
        dsimp only
        exact grayTensorLeft_map_graySpineEdge_graySpineSubcomplexDesc x _
          (fun i => (X.mappingSpaceHomEquiv _ _ T (s ≫ Pi.π _ i)).2) i)))
    (nativeSpineFibreHom_comp X x)

theorem mappingSpaceHomEquiv_graySpineFibreIso (i : Fin p) {T : DiagSet.{u}}
    (t : T ⟶ graySpineFibre X x) :
    (X.mappingSpaceHomEquiv _ _ T (t ≫ (graySpineFibreIso X x).hom ≫ Pi.π _ i)).1 =
      (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  have e : t ≫ (graySpineFibreIso X x).hom = nativeSpineFibreHom X x t :=
    (nativeSpineFibreHom_comp X x t (𝟙 _)).symm.trans (congrArg _ (Category.comp_id t))
  rw [← Category.assoc, e, nativeSpineFibreHom_π]

end NativeProduct

noncomputable def graySpineFibreTwoIso (X : DiagSet.{u}) (x : Fin 3 → X.Vertex) :
    graySpineFibre X x ≅
      (X.mappingSpace (x 0) (x 1)).toFunctor ⨯ (X.mappingSpace (x 1) (x 2)).toFunctor :=
  graySpineFibreIso X x ≪≫
    { hom := prod.lift (Pi.π _ 0) (Pi.π _ 1)
      inv := Pi.lift (Fin.cases prod.fst (Fin.cases prod.snd (fun j => Fin.elim0 j)))
      hom_inv_id := by
        apply Pi.hom_ext
        intro i
        fin_cases i
        · simp only [Category.assoc, Pi.lift_π, Category.id_comp]
          exact prod.lift_fst _ _
        · simp only [Category.assoc, Pi.lift_π, Category.id_comp]
          exact prod.lift_snd _ _
      inv_hom_id := by
        apply prod.hom_ext
        · simp only [Category.assoc, prod.lift_fst, Pi.lift_π, Category.id_comp]
          rfl
        · simp only [Category.assoc, prod.lift_snd, Pi.lift_π, Category.id_comp]
          rfl }

theorem graySpineFibreTwoIso_hom (X : DiagSet.{u}) (x : Fin 3 → X.Vertex) :
    (graySpineFibreTwoIso X x).hom =
      (graySpineFibreIso X x).hom ≫ prod.lift (Pi.π _ 0) (Pi.π _ 1) :=
  rfl

theorem graySpineFibreIso_comparison (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    (graySpineFibreIso X x).hom =
      (nativeGraySpineFibreIso X x).hom ≫ (legacyGraySpineFibreIso X x).hom := by
  apply Pi.hom_ext
  intro i
  apply (X.mappingSpaceHomEquiv _ _ _).injective
  apply Subtype.ext
  have h₁ := mappingSpaceHomEquiv_graySpineFibreIso X x i (𝟙 _)
  rw [Category.id_comp] at h₁
  rw [h₁, Category.assoc, mappingSpaceHomEquiv_legacyGraySpineFibreIso]
  have hi : (relativeMappingSpaceHomEquiv _ _ _ (nativeGraySpineFibreIso X x).hom).1 =
      (grayTensorLeft (graySpineFibre X x)).map (nativeSpineToDiagSetIso p).inv ≫
        (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySpineFibre X x))).1 := by
    simpa only [Category.id_comp, nativeGraySpineFibreIso] using
      relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso (Iso.refl _)
        (nativeSpineToDiagSetIso p)
        (by rw [graySpineVerticesι_comparison, Iso.refl_hom, Category.id_comp])
        (by rw [Iso.refl_hom, Category.id_comp]) (𝟙 (graySpineFibre X x))
  rw [hi, ← Category.assoc, ← Functor.map_comp,
    ← graySpineEdge_comparison_assoc, Iso.hom_inv_id, Category.comp_id]

theorem graySpineEdge_zero_desc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    (grayTensorLeft T).map (nativeGraySpineEdge 2 0) ≫ graySpineDesc F₀₁ F₁₂ h = F₀₁ :=
  nativeGraySpineEdge_tensorDesc _ _ _ _ 0

theorem graySpineEdge_one_desc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    (grayTensorLeft T).map (nativeGraySpineEdge 2 1) ≫ graySpineDesc F₀₁ F₁₂ h = F₁₂ :=
  nativeGraySpineEdge_tensorDesc _ _ _ _ 1

private theorem legacySpineEdge_zero :
    legacyGraySpineEdge.{u} 2 0 = legacyGraySpineEdge₀₁ := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι) := SSet.toDiagSet.map_mono _
  apply (cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι)).1
  rw [legacyGraySpineEdge_comp_ι, legacyGraySpineEdge₀₁, Category.assoc,
    ← Functor.map_comp, SSet.spineSubcomplex.ι₀₁_ι]
  exact congrArg (fun σ => (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
    SSet.toDiagSet.map (SSet.stdSimplex.map σ))
    (SimplexCategory.Hom.ext_one_left (SimplexCategory.mkOfSucc (0 : Fin 2))
      (SimplexCategory.δ 2))

private theorem legacySpineEdge_one :
    legacyGraySpineEdge.{u} 2 1 = legacyGraySpineEdge₁₂ := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι) := SSet.toDiagSet.map_mono _
  apply (cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι)).1
  rw [legacyGraySpineEdge_comp_ι, legacyGraySpineEdge₁₂, Category.assoc,
    ← Functor.map_comp, SSet.spineSubcomplex.ι₁₂_ι]
  exact congrArg (fun σ => (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
    SSet.toDiagSet.map (SSet.stdSimplex.map σ))
    (SimplexCategory.Hom.ext_one_left (SimplexCategory.mkOfSucc (1 : Fin 2))
      (SimplexCategory.δ 0))

theorem graySpineDesc_comparison {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    (grayTensorLeft T).map (nativeSpineToDiagSetIso 2).hom ≫
      legacyGraySpineDesc F₀₁ F₁₂ h = graySpineDesc F₀₁ F₁₂ h := by
  have he : ∀ i : Fin 2, (grayTensorLeft T).map (nativeGraySpineEdge 2 i) ≫
      (grayTensorLeft T).map (nativeSpineToDiagSetIso 2).hom ≫ legacyGraySpineDesc F₀₁ F₁₂ h =
      (grayTensorLeft T).map (nativeGraySpineEdge 2 i) ≫ graySpineDesc F₀₁ F₁₂ h := by
    intro i
    rw [← Category.assoc, ← Functor.map_comp, graySpineEdge_comparison]
    fin_cases i
    · change (grayTensorLeft T).map (legacyGraySpineEdge 2 0) ≫ _ =
        (grayTensorLeft T).map (nativeGraySpineEdge 2 0) ≫ _
      rw [legacySpineEdge_zero, grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc,
        graySpineEdge_zero_desc]
    · change (grayTensorLeft T).map (legacyGraySpineEdge 2 1) ≫ _ =
        (grayTensorLeft T).map (nativeGraySpineEdge 2 1) ≫ _
      rw [legacySpineEdge_one, grayTensorLeft_map_legacyGraySpineEdge₁₂_legacyGraySpineDesc,
        graySpineEdge_one_desc]
  apply nativeGraySpineTensor_hom_ext _ he
  intro k
  fin_cases k
  · change (grayTensorLeft T).map (nativeGraySpineVertex 2 0) ≫ _ =
      (grayTensorLeft T).map (nativeGraySpineVertex 2 0) ≫ _
    have hv : nativeGraySpineVertex 2 0 = intervalSource ≫ nativeGraySpineEdge 2 0 :=
      (intervalSource_nativeGraySpineEdge 2 (0 : Fin 2)).symm
    rw [hv, Functor.map_comp, Category.assoc,
      Category.assoc, he]
  · change (grayTensorLeft T).map (nativeGraySpineVertex 2 1) ≫ _ =
      (grayTensorLeft T).map (nativeGraySpineVertex 2 1) ≫ _
    have hv : nativeGraySpineVertex 2 1 = intervalTarget ≫ nativeGraySpineEdge 2 0 :=
      (intervalTarget_nativeGraySpineEdge 2 (0 : Fin 2)).symm
    rw [hv, Functor.map_comp, Category.assoc,
      Category.assoc, he]
  · change (grayTensorLeft T).map (nativeGraySpineVertex 2 2) ≫ _ =
      (grayTensorLeft T).map (nativeGraySpineVertex 2 2) ≫ _
    have hv : nativeGraySpineVertex 2 2 = intervalTarget ≫ nativeGraySpineEdge 2 1 :=
      (intervalTarget_nativeGraySpineEdge 2 (1 : Fin 2)).symm
    rw [hv, Functor.map_comp, Category.assoc,
      Category.assoc, he]

theorem graySpineFibreTwoIso_comparison (X : DiagSet.{u}) (x : Fin 3 → X.Vertex) :
    (graySpineFibreTwoIso X x).hom =
      (nativeGraySpineFibreIso X x).hom ≫ (legacyGraySpineFibreTwoIso X x).hom := by
  have hi : (relativeMappingSpaceHomEquiv _ _ _ (nativeGraySpineFibreIso X x).hom).1 =
      (grayTensorLeft (graySpineFibre X x)).map (nativeSpineToDiagSetIso 2).inv ≫
        (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySpineFibre X x))).1 := by
    simpa only [Category.id_comp, nativeGraySpineFibreIso] using
      relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso (Iso.refl _)
        (nativeSpineToDiagSetIso 2)
        (by rw [graySpineVerticesι_comparison, Iso.refl_hom, Category.id_comp])
        (by rw [Iso.refl_hom, Category.id_comp]) (𝟙 (graySpineFibre X x))
  apply prod.hom_ext
  · apply (X.mappingSpaceHomEquiv _ _ _).injective
    apply Subtype.ext
    dsimp only [graySpineFibreTwoIso, Iso.trans_hom]
    rw [Category.assoc, prod.lift_fst, Category.assoc,
      mappingSpaceHomEquiv_graySpineFibreTwoIso_fst, hi]
    have hl := mappingSpaceHomEquiv_graySpineFibreIso X x (0 : Fin 2) (𝟙 _)
    rw [Category.id_comp] at hl
    have hl' : (X.mappingSpaceHomEquiv (x 0) (x 1) _
        ((graySpineFibreIso X x).hom ≫ Pi.π _ (0 : Fin 2))).1 =
        (grayTensorLeft (graySpineFibre X x)).map (nativeGraySpineEdge 2 0) ≫
          (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySpineFibre X x))).1 := hl
    rw [hl', ← Category.assoc, ← Functor.map_comp, ← legacySpineEdge_zero,
      ← graySpineEdge_comparison_assoc, Iso.hom_inv_id, Category.comp_id]
  · apply (X.mappingSpaceHomEquiv _ _ _).injective
    apply Subtype.ext
    dsimp only [graySpineFibreTwoIso, Iso.trans_hom]
    rw [Category.assoc, prod.lift_snd, Category.assoc,
      mappingSpaceHomEquiv_graySpineFibreTwoIso_snd, hi]
    have hl := mappingSpaceHomEquiv_graySpineFibreIso X x (1 : Fin 2) (𝟙 _)
    rw [Category.id_comp] at hl
    have hl' : (X.mappingSpaceHomEquiv (x 1) (x 2) _
        ((graySpineFibreIso X x).hom ≫ Pi.π _ (1 : Fin 2))).1 =
        (grayTensorLeft (graySpineFibre X x)).map (nativeGraySpineEdge 2 1) ≫
          (relativeMappingSpaceHomEquiv _ _ _ (𝟙 (graySpineFibre X x))).1 := hl
    rw [hl', ← Category.assoc, ← Functor.map_comp, ← legacySpineEdge_one,
      ← graySpineEdge_comparison_assoc, Iso.hom_inv_id, Category.comp_id]

end Atoms.Diagrammatic
