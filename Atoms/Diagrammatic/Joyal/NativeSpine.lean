import Atoms.Diagrammatic.Joyal.GrayCompositionAssoc

open CategoryTheory Limits Opposite
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

private noncomputable abbrev spinePoints (p : ℕ) : DiagSet.{u} :=
  ∐ fun _ : Fin (p + 1) => ball.{u} atomPoint

private noncomputable abbrev spineEdges (p : ℕ) : DiagSet.{u} :=
  ∐ fun _ : Fin p => ball.{u} (atomSimplex 1)

private noncomputable abbrev spineEnds (p : ℕ) : DiagSet.{u} :=
  ∐ fun _ : Fin p × Bool => ball.{u} atomPoint

private def spineEndVertex {p : ℕ} (i : Fin p × Bool) : Fin (p + 1) :=
  if i.2 then i.1.succ else i.1.castSucc

private noncomputable def spineEndMap (b : Bool) :
    ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1) :=
  cond b intervalTarget intervalSource

private noncomputable def spineVertexRelation (p : ℕ) :
    spineEnds.{u} p ⟶ spinePoints.{u} p ⨿ spineEdges.{u} p :=
  Sigma.desc fun i =>
    Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) (spineEndVertex i) ≫ coprod.inl

private noncomputable def spineEdgeRelation (p : ℕ) :
    spineEnds.{u} p ⟶ spinePoints.{u} p ⨿ spineEdges.{u} p :=
  Sigma.desc fun i =>
    spineEndMap i.2 ≫ Sigma.ι (fun _ : Fin p => ball.{u} (atomSimplex 1)) i.1 ≫ coprod.inr

noncomputable abbrev nativeGraySpine (p : ℕ) : DiagSet.{u} :=
  coequalizer (spineVertexRelation p) (spineEdgeRelation p)

noncomputable def nativeGraySpineVertex (p : ℕ) (k : Fin (p + 1)) :
    ball.{u} atomPoint ⟶ nativeGraySpine.{u} p :=
  Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ coprod.inl ≫ coequalizer.π _ _

noncomputable def nativeGraySpineEdge (p : ℕ) (i : Fin p) :
    ball.{u} (atomSimplex 1) ⟶ nativeGraySpine.{u} p :=
  Sigma.ι (fun _ : Fin p => ball.{u} (atomSimplex 1)) i ≫ coprod.inr ≫ coequalizer.π _ _

private theorem spine_endpoint (p : ℕ) (i : Fin p × Bool) :
    spineEndMap i.2 ≫ nativeGraySpineEdge.{u} p i.1 =
      nativeGraySpineVertex p (spineEndVertex i) := by
  let q := coequalizer.π (spineVertexRelation.{u} p) (spineEdgeRelation p)
  have hv : Sigma.ι (fun _ : Fin p × Bool => ball.{u} atomPoint) i ≫
      spineVertexRelation p =
      Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) (spineEndVertex i) ≫ coprod.inl :=
    Sigma.ι_desc _ i
  have he : Sigma.ι (fun _ : Fin p × Bool => ball.{u} atomPoint) i ≫
      spineEdgeRelation p = spineEndMap i.2 ≫
      Sigma.ι (fun _ : Fin p => ball.{u} (atomSimplex 1)) i.1 ≫ coprod.inr :=
    Sigma.ι_desc _ i
  have h := congrArg (Sigma.ι (fun _ : Fin p × Bool => ball.{u} atomPoint) i ≫ ·)
    (coequalizer.condition (spineVertexRelation.{u} p) (spineEdgeRelation p))
  rw [← Category.assoc, ← Category.assoc] at h
  have hh := (congrArg (· ≫ q) he).symm.trans (h.symm.trans (congrArg (· ≫ q) hv))
  simpa only [nativeGraySpineVertex, nativeGraySpineEdge, Category.assoc] using hh

@[reassoc]
theorem intervalSource_nativeGraySpineEdge (p : ℕ) (i : Fin p) :
    intervalSource ≫ nativeGraySpineEdge.{u} p i = nativeGraySpineVertex p i.castSucc :=
  spine_endpoint p (i, false)

@[reassoc]
theorem intervalTarget_nativeGraySpineEdge (p : ℕ) (i : Fin p) :
    intervalTarget ≫ nativeGraySpineEdge.{u} p i = nativeGraySpineVertex p i.succ :=
  spine_endpoint p (i, true)

noncomputable def nativeGraySpineDesc {p : ℕ} {X : DiagSet.{u}}
    (v : Fin (p + 1) → (ball.{u} atomPoint ⟶ X))
    (e : Fin p → (ball.{u} (atomSimplex 1) ⟶ X))
    (hs : ∀ i, intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, intervalTarget ≫ e i = v i.succ) : nativeGraySpine p ⟶ X :=
  coequalizer.desc (coprod.desc (Sigma.desc v) (Sigma.desc e)) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    rcases i with ⟨i, b⟩
    cases b <;>
      simp only [spineVertexRelation, spineEdgeRelation, Sigma.ι_desc_assoc,
        coprod.inl_desc, coprod.inr_desc, Sigma.ι_desc, spineEndMap,
        spineEndVertex, cond_false, cond_true, Bool.false_eq_true, ↓reduceIte, Category.assoc]
    · exact (hs i).symm
    · exact (ht i).symm)

@[reassoc]
theorem nativeGraySpineVertex_desc {p : ℕ} {X : DiagSet.{u}}
    (v : Fin (p + 1) → (ball.{u} atomPoint ⟶ X))
    (e : Fin p → (ball.{u} (atomSimplex 1) ⟶ X))
    (hs : ∀ i, intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, intervalTarget ≫ e i = v i.succ) (k : Fin (p + 1)) :
    nativeGraySpineVertex p k ≫ nativeGraySpineDesc v e hs ht = v k := by
  simp only [nativeGraySpineVertex, nativeGraySpineDesc, Category.assoc,
    coequalizer.π_desc, coprod.inl_desc, Sigma.ι_desc]

@[reassoc]
theorem nativeGraySpineEdge_desc {p : ℕ} {X : DiagSet.{u}}
    (v : Fin (p + 1) → (ball.{u} atomPoint ⟶ X))
    (e : Fin p → (ball.{u} (atomSimplex 1) ⟶ X))
    (hs : ∀ i, intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, intervalTarget ≫ e i = v i.succ) (i : Fin p) :
    nativeGraySpineEdge p i ≫ nativeGraySpineDesc v e hs ht = e i := by
  simp only [nativeGraySpineEdge, nativeGraySpineDesc, Category.assoc,
    coequalizer.π_desc, coprod.inr_desc, Sigma.ι_desc]

@[ext]
theorem nativeGraySpine_hom_ext {p : ℕ} {X : DiagSet.{u}}
    {f g : nativeGraySpine.{u} p ⟶ X}
    (hv : ∀ k, nativeGraySpineVertex p k ≫ f = nativeGraySpineVertex p k ≫ g)
    (he : ∀ i, nativeGraySpineEdge p i ≫ f = nativeGraySpineEdge p i ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply coprod.hom_ext
  · refine Sigma.hom_ext _ _ fun k => ?_
    simpa only [nativeGraySpineVertex, Category.assoc] using hv k
  · refine Sigma.hom_ext _ _ fun i => ?_
    simpa only [nativeGraySpineEdge, Category.assoc] using he i

noncomputable def nativeGraySpineTensorDesc {p : ℕ} {T X : DiagSet.{u}}
    (v : Fin (p + 1) → (grayTensor T (ball.{u} atomPoint) ⟶ X))
    (e : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hs : ∀ i, (grayTensorLeft T).map intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, (grayTensorLeft T).map intervalTarget ≫ e i = v i.succ) :
    grayTensor T (nativeGraySpine p) ⟶ X :=
  ((grayTensorLeftAdjunction T).homEquiv _ _).symm (nativeGraySpineDesc
    (fun k => (grayTensorLeftAdjunction T).homEquiv _ _ (v k))
    (fun i => (grayTensorLeftAdjunction T).homEquiv _ _ (e i))
    (fun i => by rw [← Adjunction.homEquiv_naturality_left, hs i])
    (fun i => by rw [← Adjunction.homEquiv_naturality_left, ht i]))

@[reassoc]
theorem nativeGraySpineVertex_tensorDesc {p : ℕ} {T X : DiagSet.{u}}
    (v : Fin (p + 1) → (grayTensor T (ball.{u} atomPoint) ⟶ X))
    (e : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hs : ∀ i, (grayTensorLeft T).map intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, (grayTensorLeft T).map intervalTarget ≫ e i = v i.succ)
    (k : Fin (p + 1)) :
    (grayTensorLeft T).map (nativeGraySpineVertex p k) ≫
      nativeGraySpineTensorDesc v e hs ht = v k := by
  rw [nativeGraySpineTensorDesc, ← Adjunction.homEquiv_naturality_left_symm,
    nativeGraySpineVertex_desc, Equiv.symm_apply_apply]

@[reassoc]
theorem nativeGraySpineEdge_tensorDesc {p : ℕ} {T X : DiagSet.{u}}
    (v : Fin (p + 1) → (grayTensor T (ball.{u} atomPoint) ⟶ X))
    (e : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
    (hs : ∀ i, (grayTensorLeft T).map intervalSource ≫ e i = v i.castSucc)
    (ht : ∀ i, (grayTensorLeft T).map intervalTarget ≫ e i = v i.succ) (i : Fin p) :
    (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫
      nativeGraySpineTensorDesc v e hs ht = e i := by
  rw [nativeGraySpineTensorDesc, ← Adjunction.homEquiv_naturality_left_symm,
    nativeGraySpineEdge_desc, Equiv.symm_apply_apply]

theorem nativeGraySpineTensor_hom_ext {p : ℕ} {T X : DiagSet.{u}}
    {f g : grayTensor T (nativeGraySpine p) ⟶ X}
    (hv : ∀ k, (grayTensorLeft T).map (nativeGraySpineVertex p k) ≫ f =
      (grayTensorLeft T).map (nativeGraySpineVertex p k) ≫ g)
    (he : ∀ i, (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ f =
      (grayTensorLeft T).map (nativeGraySpineEdge p i) ≫ g) : f = g := by
  apply ((grayTensorLeftAdjunction T).homEquiv _ _).injective
  apply nativeGraySpine_hom_ext
  · intro k
    rw [← Adjunction.homEquiv_naturality_left,
      ← Adjunction.homEquiv_naturality_left, hv k]
  · intro i
    rw [← Adjunction.homEquiv_naturality_left,
      ← Adjunction.homEquiv_naturality_left, he i]

noncomputable def nativeSpineToDiagSet (p : ℕ) :
    nativeGraySpine.{u} p ⟶ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet) :=
  nativeGraySpineDesc
    (fun k => Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p)
    (legacyGraySpineEdge p) (intervalSource_comp_legacyGraySpineEdge p)
    (intervalTarget_comp_legacyGraySpineEdge p)

private noncomputable def spineNativeVertexTuple (p : ℕ) :
    Fin (p + 1) → (nativeGraySpine.{u} p).Vertex :=
  fun k => uliftYonedaEquiv (nativeGraySpineVertex p k)

private theorem vertexHom_spineNativeVertexTuple (p : ℕ) (k : Fin (p + 1)) :
    vertexHom (spineNativeVertexTuple.{u} p k) = nativeGraySpineVertex p k :=
  uliftYonedaEquiv.symm_apply_apply _

private noncomputable def spineNativeTensorDesc (p : ℕ) :
    grayTensor (ball.{u} atomPoint)
      (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet)) ⟶ nativeGraySpine p :=
  legacyGraySpineSubcomplexDesc (spineNativeVertexTuple p)
    (fun i => grayTensorSnd _ _ ≫ nativeGraySpineEdge p i) (fun i => ⟨by
      rw [← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.assoc,
        intervalSource_nativeGraySpineEdge, vertexHom_spineNativeVertexTuple], by
      rw [← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.assoc,
        intervalTarget_nativeGraySpineEdge, vertexHom_spineNativeVertexTuple]⟩)

private noncomputable def spineToNative (p : ℕ) :
    SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet) ⟶ nativeGraySpine.{u} p :=
  inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ spineNativeTensorDesc p

private theorem spine_vertex_toNative (p : ℕ) (k : Fin (p + 1)) :
    (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p) ≫
      spineToNative p = nativeGraySpineVertex p k := by
  apply (cancel_epi (grayTensorSnd (ball.{u} atomPoint) _)).1
  rw [← Category.assoc, ← grayTensorLeft_map_grayTensorSnd, Category.assoc, spineToNative,
    IsIso.hom_inv_id_assoc, spineNativeTensorDesc]
  simpa only [vertexHom_spineNativeVertexTuple] using
    grayTensorLeft_map_ι_graySpineVerticesι_legacyGraySpineSubcomplexDesc
      (spineNativeVertexTuple.{u} p) _ _ k

private theorem spine_edge_toNative (p : ℕ) (i : Fin p) :
    legacyGraySpineEdge.{u} p i ≫ spineToNative p = nativeGraySpineEdge p i := by
  apply (cancel_epi (grayTensorSnd (ball.{u} atomPoint) _)).1
  rw [← Category.assoc, ← grayTensorLeft_map_grayTensorSnd, Category.assoc, spineToNative,
    IsIso.hom_inv_id_assoc, spineNativeTensorDesc]
  exact grayTensorLeft_map_legacyGraySpineEdge_legacyGraySpineSubcomplexDesc _ _ _ i

noncomputable def nativeSpineToDiagSetIso (p : ℕ) :
    nativeGraySpine.{u} p ≅ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet) where
  hom := nativeSpineToDiagSet p
  inv := spineToNative p
  hom_inv_id := by
    apply nativeGraySpine_hom_ext
    · intro k
      rw [nativeSpineToDiagSet, nativeGraySpineVertex_desc_assoc,
        spine_vertex_toNative, Category.comp_id]
    · intro i
      rw [nativeSpineToDiagSet, nativeGraySpineEdge_desc_assoc,
        spine_edge_toNative, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (grayTensorSnd (ball.{u} atomPoint) _)).1
    apply legacyGrayTensor_spineSubcomplex_hom_ext
    · intro k
      have h := (congrArg (· ≫ nativeSpineToDiagSet p) (spine_vertex_toNative.{u} p k)).trans
        (nativeGraySpineVertex_desc _ _ _ _ k)
      simpa only [← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.comp_id]
        using congrArg (grayTensorSnd (ball.{u} atomPoint) (ball atomPoint) ≫ ·) h
    · intro i
      have h := (congrArg (· ≫ nativeSpineToDiagSet p) (spine_edge_toNative.{u} p i)).trans
        (nativeGraySpineEdge_desc _ _ _ _ i)
      simpa only [← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.comp_id]
        using congrArg (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1)) ≫ ·) h

end Atoms.Diagrammatic
