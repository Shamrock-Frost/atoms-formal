import Atoms.Diagrammatic.Joyal.GraySegalBridge

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Homotopical Atoms.Shape Simplicial

universe u v w

namespace Atoms.Diagrammatic

theorem toDiagSet_map_stdSimplex_map_comp_hom {a b : ℕ} (σ : ⦋a⦌ ⟶ ⦋b⦌) :
    SSet.toDiagSet.map (SSet.stdSimplex.map σ) ≫ (toDiagSetObjStdSimplexIso.{u} b).hom =
      (toDiagSetObjStdSimplexIso.{u} a).hom ≫ uliftYoneda.map (simplexHom σ.toOrderHom) :=
  stdSimplexCompToDiagSetIso.hom.naturality σ

private theorem uliftYoneda_map_δ_comp_toDiagSet_map {b : ℕ} (i : Fin 2) (σ : ⦋1⦌ ⟶ ⦋b⦌)
    {k : Fin (b + 1)} (hk : σ.toOrderHom ((SimplexCategory.δ i).toOrderHom 0) = k) :
    (uliftYoneda.map (simplexHom (SimplexCategory.δ i).toOrderHom) :
        ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)) ≫ (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map σ) =
      Sigma.ι (fun _ : Fin (b + 1) => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι b := by
  rw [← cancel_mono (toDiagSetObjStdSimplexIso.{u} b).hom, Category.assoc, Category.assoc,
    toDiagSet_map_stdSimplex_map_comp_hom, Iso.inv_hom_id_assoc, Category.assoc,
    ι_graySimplexVerticesι_comp_hom]
  exact (Functor.map_comp (simplexFunctor ⋙ uliftYoneda.{u}) (SimplexCategory.δ i) σ).symm.trans
    (congrArg (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.Hom.ext_zero_left _ _ hk))

theorem intervalSource_comp_toDiagSet_map {b : ℕ} (σ : ⦋1⦌ ⟶ ⦋b⦌) {k : Fin (b + 1)}
    (hk : σ.toOrderHom 0 = k) :
    intervalSource ≫ (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map σ) =
      Sigma.ι (fun _ : Fin (b + 1) => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι b :=
  uliftYoneda_map_δ_comp_toDiagSet_map 1 σ hk

theorem intervalTarget_comp_toDiagSet_map {b : ℕ} (σ : ⦋1⦌ ⟶ ⦋b⦌) {k : Fin (b + 1)}
    (hk : σ.toOrderHom 1 = k) :
    intervalTarget ≫ (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map σ) =
      Sigma.ι (fun _ : Fin (b + 1) => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι b :=
  uliftYoneda_map_δ_comp_toDiagSet_map 0 σ hk

theorem grayTensorLeft_map_ι_comp_of_comp_eq {p : ℕ} {A X T : DiagSet.{u}}
    (i : graySimplexVertices.{u} p ⟶ A) (x : Fin (p + 1) → X.Vertex)
    {F : grayTensor T A ⟶ X}
    (hF : (grayTensorLeft T).map i ≫ F =
      grayTensorSnd T _ ≫ (graySimplexVerticesHomEquiv p X).symm x) (k : Fin (p + 1)) :
    (grayTensorLeft T).map (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ i) ≫
        F = grayTensorSnd T _ ≫ vertexHom (x k) := by
  rw [Functor.map_comp, Category.assoc, hF, ← Category.assoc, grayTensorLeft_map_grayTensorSnd,
    Category.assoc, ι_graySimplexVerticesHomEquiv_symm]

theorem isFixedEnds_grayTensorLeft_map_comp {p : ℕ} {A X T : DiagSet.{u}}
    (i : graySimplexVertices.{u} p ⟶ A) (x : Fin (p + 1) → X.Vertex)
    {F : grayTensor T A ⟶ X}
    (hF : (grayTensorLeft T).map i ≫ F =
      grayTensorSnd T _ ≫ (graySimplexVerticesHomEquiv p X).symm x)
    {e : ball.{u} (atomSimplex 1) ⟶ A} {k l : Fin (p + 1)}
    (hk : intervalSource ≫ e = Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ i)
    (hl : intervalTarget ≫ e = Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) l ≫ i) :
    IsFixedEnds (x k) (x l) ((grayTensorLeft T).map e ≫ F) :=
  ⟨by rw [← Category.assoc, ← Functor.map_comp, hk, grayTensorLeft_map_ι_comp_of_comp_eq i x hF],
    by rw [← Category.assoc, ← Functor.map_comp, hl, grayTensorLeft_map_ι_comp_of_comp_eq i x hF]⟩

noncomputable def graySimplexVerticesOneIso : graySimplexVertices.{u} 1 ≅ intervalBoundary.{u} where
  hom := Sigma.desc (Fin.cases (motive := fun _ => ball.{u} atomPoint ⟶ intervalBoundary)
    coprod.inl fun _ => coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin 2 => ball.{u} atomPoint) 0)
    (Sigma.ι (fun _ : Fin 2 => ball.{u} atomPoint) 1)
  hom_inv_id := Sigma.hom_ext _ _ fun k => by
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    fin_cases k
    · exact coprod.inl_desc _ _
    · exact coprod.inr_desc _ _
  inv_hom_id := coprod.hom_ext
    (by rw [coprod.inl_desc_assoc, Sigma.ι_desc, Category.comp_id]; rfl)
    (by rw [coprod.inr_desc_assoc, Sigma.ι_desc, Category.comp_id]; rfl)

private theorem graySimplexVerticesι_one_comp_hom :
    legacyGraySimplexVerticesι.{u} 1 ≫ (toDiagSetObjStdSimplexIso.{u} 1).hom =
      graySimplexVerticesOneIso.hom ≫ intervalBoundaryι := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [ι_graySimplexVerticesι_comp_hom, graySimplexVerticesOneIso,
    Sigma.ι_desc_assoc]
  fin_cases k
  · exact (congrArg (fun τ : ⦋0⦌ ⟶ ⦋1⦌ => uliftYoneda.{u}.map (simplexHom τ.toOrderHom))
      (SimplexCategory.eq_const_of_zero (SimplexCategory.δ 1)).symm).trans
        (coprod.inl_desc _ _).symm
  · exact (congrArg (fun τ : ⦋0⦌ ⟶ ⦋1⦌ => uliftYoneda.{u}.map (simplexHom τ.toOrderHom))
      (SimplexCategory.eq_const_of_zero (SimplexCategory.δ 0)).symm).trans
        (coprod.inr_desc _ _).symm

private theorem graySimplexVerticesHomEquiv_one_symm {X : DiagSet.{u}}
    (x : Fin 2 → X.Vertex) :
    (graySimplexVerticesHomEquiv 1 X).symm x =
      graySimplexVerticesOneIso.hom ≫ coprod.desc (vertexHom (x 0)) (vertexHom (x 1)) := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [ι_graySimplexVerticesHomEquiv_symm, graySimplexVerticesOneIso, Sigma.ι_desc_assoc]
  fin_cases k
  · exact (coprod.inl_desc _ _).symm
  · exact (coprod.inr_desc _ _).symm

noncomputable def graySimplexFibreOneIso (X : DiagSet.{u})
    (x : Fin 2 → X.Vertex) :
    legacyGraySimplexFibre X x ≅ (X.mappingSpace (x 0) (x 1)).toFunctor :=
  relativeMappingSpaceIsoOfIso graySimplexVerticesOneIso (toDiagSetObjStdSimplexIso 1)
      graySimplexVerticesι_one_comp_hom (graySimplexVerticesHomEquiv_one_symm x) ≪≫
    (DiagSet.mappingSpaceIsoRelativeMappingSpace (x 0) (x 1)).symm

theorem mappingSpaceHomEquiv_graySimplexFibreOneIso (X : DiagSet.{u})
    (x : Fin 2 → X.Vertex) {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (X.mappingSpaceHomEquiv (x 0) (x 1) T (t ≫ (graySimplexFibreOneIso X x).hom)).1 =
      (grayTensorLeft T).map (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [graySimplexFibreOneIso, Iso.trans_hom, Iso.symm_hom,
    ← DiagSet.relativeMappingSpaceHomEquiv_mappingSpaceIsoRelativeMappingSpace, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    relativeMappingSpaceHomEquiv_relativeMappingSpaceIsoOfIso]

noncomputable def legacyGraySpineEdge₀₁ :
    ball.{u} (atomSimplex 1) ⟶ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} 2 : SSet) :=
  (toDiagSetObjStdSimplexIso 1).inv ≫ SSet.toDiagSet.map SSet.spineSubcomplex.ι₀₁

noncomputable def legacyGraySpineEdge₁₂ :
    ball.{u} (atomSimplex 1) ⟶ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} 2 : SSet) :=
  (toDiagSetObjStdSimplexIso 1).inv ≫ SSet.toDiagSet.map SSet.spineSubcomplex.ι₁₂

private theorem graySpineVerticesι_two_ext {e : ball.{u} atomPoint ⟶
    SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} 2 : SSet)} {k : Fin 3}
    (h : e ≫ SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι =
      Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι 2) :
    e = Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι 2 := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι) := SSet.toDiagSet.map_mono _
  exact (cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} 2).ι)).1
    (h.trans (Category.assoc _ _ _).symm)

theorem intervalSource_comp_legacyGraySpineEdge₀₁ :
    intervalSource ≫ legacyGraySpineEdge₀₁.{u} =
      Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) 0 ≫ legacyGraySpineVerticesι 2 :=
  graySpineVerticesι_two_ext (by
    rw [legacyGraySpineEdge₀₁, Category.assoc, Category.assoc, ← Functor.map_comp,
      SSet.spineSubcomplex.ι₀₁_ι]
    exact intervalSource_comp_toDiagSet_map (SimplexCategory.δ 2) rfl)

theorem intervalTarget_comp_legacyGraySpineEdge₀₁ :
    intervalTarget ≫ legacyGraySpineEdge₀₁.{u} =
      Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) 1 ≫ legacyGraySpineVerticesι 2 :=
  graySpineVerticesι_two_ext (by
    rw [legacyGraySpineEdge₀₁, Category.assoc, Category.assoc, ← Functor.map_comp,
      SSet.spineSubcomplex.ι₀₁_ι]
    exact intervalTarget_comp_toDiagSet_map (SimplexCategory.δ 2) rfl)

theorem intervalSource_comp_legacyGraySpineEdge₁₂ :
    intervalSource ≫ legacyGraySpineEdge₁₂.{u} =
      Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) 1 ≫ legacyGraySpineVerticesι 2 :=
  graySpineVerticesι_two_ext (by
    rw [legacyGraySpineEdge₁₂, Category.assoc, Category.assoc, ← Functor.map_comp,
      SSet.spineSubcomplex.ι₁₂_ι]
    exact intervalSource_comp_toDiagSet_map (SimplexCategory.δ 0) rfl)

theorem intervalTarget_comp_legacyGraySpineEdge₁₂ :
    intervalTarget ≫ legacyGraySpineEdge₁₂.{u} =
      Sigma.ι (fun _ : Fin 3 => ball.{u} atomPoint) 2 ≫ legacyGraySpineVerticesι 2 :=
  graySpineVerticesι_two_ext (by
    rw [legacyGraySpineEdge₁₂, Category.assoc, Category.assoc, ← Functor.map_comp,
      SSet.spineSubcomplex.ι₁₂_ι]
    exact intervalTarget_comp_toDiagSet_map (SimplexCategory.δ 0) rfl)

theorem isPushout_grayTensorLeft_toDiagSet_spine (T : DiagSet.{u}) :
    IsPushout ((grayTensorLeft T).map (SSet.toDiagSet.map (SSet.stdSimplex.δ (0 : Fin 2))))
      ((grayTensorLeft T).map (SSet.toDiagSet.map (SSet.stdSimplex.δ (1 : Fin 2))))
      ((grayTensorLeft T).map (SSet.toDiagSet.map SSet.spineSubcomplex.ι₀₁.{u}))
      ((grayTensorLeft T).map (SSet.toDiagSet.map SSet.spineSubcomplex.ι₁₂.{u})) :=
  have := sSetDiagSetAdj.{u}.leftAdjoint_preservesColimits
  (SSet.spineSubcomplex.isPushout_two.map SSet.toDiagSet).map (grayTensorLeft T)

theorem grayTensor_spine_hom_ext {T Y : DiagSet.{u}}
    {φ ψ : grayTensor T (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} 2 : SSet)) ⟶ Y}
    (h₀₁ : (grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ φ =
      (grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ ψ)
    (h₁₂ : (grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ φ =
      (grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ ψ) :
    φ = ψ := by
  have e (ι : Δ[1] ⟶ (SSet.spineSubcomplex.{u} 2 : SSet)) :
      (grayTensorLeft T).map (SSet.toDiagSet.map ι) = (grayTensorLeft T).map
        (toDiagSetObjStdSimplexIso 1).hom ≫ (grayTensorLeft T).map
          ((toDiagSetObjStdSimplexIso 1).inv ≫ SSet.toDiagSet.map ι) := by
    rw [← Functor.map_comp, Iso.hom_inv_id_assoc]
  refine (isPushout_grayTensorLeft_toDiagSet_spine T).hom_ext ?_ ?_
  · rw [e, Category.assoc, Category.assoc]
    exact congrArg _ h₀₁
  · rw [e, Category.assoc, Category.assoc]
    exact congrArg _ h₁₂

noncomputable def legacyGraySpineDesc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    grayTensor T (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} 2 : SSet)) ⟶ X :=
  (isPushout_grayTensorLeft_toDiagSet_spine T).desc
    ((grayTensorLeft T).map (toDiagSetObjStdSimplexIso 1).hom ≫ F₀₁)
    ((grayTensorLeft T).map (toDiagSetObjStdSimplexIso 1).hom ≫ F₁₂) (by
      have h₀ : SSet.toDiagSet.map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (toDiagSetObjStdSimplexIso.{u} 1).hom =
          (toDiagSetObjStdSimplexIso.{u} 0).hom ≫ intervalTarget :=
        toDiagSet_map_stdSimplex_map_comp_hom _
      have h₁ : SSet.toDiagSet.map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
          (toDiagSetObjStdSimplexIso.{u} 1).hom =
          (toDiagSetObjStdSimplexIso.{u} 0).hom ≫ intervalSource :=
        toDiagSet_map_stdSimplex_map_comp_hom _
      rw [← Category.assoc, ← Functor.map_comp, h₀, ← Category.assoc, ← Functor.map_comp, h₁]
      exact (Functor.map_comp_assoc _ _ _ _).trans
        ((congrArg ((grayTensorLeft T).map (toDiagSetObjStdSimplexIso.{u} 0).hom ≫ ·) h).trans
          (Functor.map_comp_assoc _ _ _ _).symm))

@[reassoc]
theorem grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    (grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ legacyGraySpineDesc F₀₁ F₁₂ h = F₀₁ := by
  rw [legacyGraySpineEdge₀₁, Functor.map_comp, Category.assoc, legacyGraySpineDesc,
    IsPushout.inl_desc,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

@[reassoc]
theorem grayTensorLeft_map_legacyGraySpineEdge₁₂_legacyGraySpineDesc {T X : DiagSet.{u}}
    (F₀₁ F₁₂ : grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X)
    (h : (grayTensorLeft T).map intervalTarget ≫ F₀₁ =
      (grayTensorLeft T).map intervalSource ≫ F₁₂) :
    (grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ legacyGraySpineDesc F₀₁ F₁₂ h = F₁₂ := by
  rw [legacyGraySpineEdge₁₂, Functor.map_comp, Category.assoc, legacyGraySpineDesc,
    IsPushout.inr_desc,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

theorem relativeMappingSpaceHomEquiv_legacyGraySegalMap (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySimplexFibre X x) :
    (relativeMappingSpaceHomEquiv _ _ T (t ≫ legacyGraySegalMap X x)).1 =
      (grayTensorLeft T).map (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 :=
  relativeMappingSpaceHomEquiv_relativeMappingSpaceRestrict _ _ _ t

section SpineFibre

variable (X : DiagSet.{u}) (x : Fin 3 → X.Vertex)

private noncomputable def graySpineFibreTwoHom {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X
  x) :
    T ⟶ (X.mappingSpace (x 0) (x 1)).toFunctor ⨯ (X.mappingSpace (x 1) (x 2)).toFunctor :=
  prod.lift
    ((X.mappingSpaceHomEquiv (x 0) (x 1) T).symm
      ⟨(grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1,
        isFixedEnds_grayTensorLeft_map_comp _ x (relativeMappingSpaceHomEquiv _ _ T t).2
          intervalSource_comp_legacyGraySpineEdge₀₁ intervalTarget_comp_legacyGraySpineEdge₀₁⟩)
    ((X.mappingSpaceHomEquiv (x 1) (x 2) T).symm
      ⟨(grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1,
        isFixedEnds_grayTensorLeft_map_comp _ x (relativeMappingSpaceHomEquiv _ _ T t).2
          intervalSource_comp_legacyGraySpineEdge₁₂ intervalTarget_comp_legacyGraySpineEdge₁₂⟩)

private theorem graySpineFibreTwoHom_fst {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X x) :
    (X.mappingSpaceHomEquiv (x 0) (x 1) T (graySpineFibreTwoHom X x t ≫ prod.fst)).1 =
      (grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [graySpineFibreTwoHom, prod.lift_fst, Equiv.apply_symm_apply]

private theorem graySpineFibreTwoHom_snd {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X x) :
    (X.mappingSpaceHomEquiv (x 1) (x 2) T (graySpineFibreTwoHom X x t ≫ prod.snd)).1 =
      (grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [graySpineFibreTwoHom, prod.lift_snd, Equiv.apply_symm_apply]

private noncomputable def graySpineFibreTwoInv {T : DiagSet.{u}}
    (s : T ⟶ (X.mappingSpace (x 0) (x 1)).toFunctor ⨯ (X.mappingSpace (x 1) (x 2)).toFunctor) :
    T ⟶ legacyGraySpineFibre X x :=
  (relativeMappingSpaceHomEquiv _ _ T).symm
    ⟨legacyGraySpineDesc (X.mappingSpaceHomEquiv (x 0) (x 1) T (s ≫ prod.fst)).1
      (X.mappingSpaceHomEquiv (x 1) (x 2) T (s ≫ prod.snd)).1
      ((X.mappingSpaceHomEquiv (x 0) (x 1) T (s ≫ prod.fst)).2.2.trans
        (X.mappingSpaceHomEquiv (x 1) (x 2) T (s ≫ prod.snd)).2.1.symm), by
      refine grayTensor_sigma_hom_ext T _ fun k => ?_
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, ι_graySimplexVerticesHomEquiv_symm]
      match k with
      | 0 =>
        rw [← intervalSource_comp_legacyGraySpineEdge₀₁, Functor.map_comp, Category.assoc,
          grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc]
        exact (X.mappingSpaceHomEquiv (x 0) (x 1) T (s ≫ prod.fst)).2.1
      | 1 =>
        rw [← intervalTarget_comp_legacyGraySpineEdge₀₁, Functor.map_comp, Category.assoc,
          grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc]
        exact (X.mappingSpaceHomEquiv (x 0) (x 1) T (s ≫ prod.fst)).2.2
      | 2 =>
        rw [← intervalTarget_comp_legacyGraySpineEdge₁₂, Functor.map_comp, Category.assoc,
          grayTensorLeft_map_legacyGraySpineEdge₁₂_legacyGraySpineDesc]
        exact (X.mappingSpaceHomEquiv (x 1) (x 2) T (s ≫ prod.snd)).2.2⟩

private theorem graySpineFibreTwoHom_comp {T T' : DiagSet.{u}} (g : T' ⟶ T)
    (t : T ⟶ legacyGraySpineFibre X x) :
    graySpineFibreTwoHom X x (g ≫ t) = g ≫ graySpineFibreTwoHom X x t := by
  refine prod.hom_ext ((X.mappingSpaceHomEquiv _ _ T').injective (Subtype.ext ?_))
    ((X.mappingSpaceHomEquiv _ _ T').injective (Subtype.ext ?_))
  · rw [graySpineFibreTwoHom_fst, Category.assoc, DiagSet.mappingSpaceHomEquiv_comp,
      graySpineFibreTwoHom_fst, relativeMappingSpaceHomEquiv_comp, ← Category.assoc,
      ← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map]
  · rw [graySpineFibreTwoHom_snd, Category.assoc, DiagSet.mappingSpaceHomEquiv_comp,
      graySpineFibreTwoHom_snd, relativeMappingSpaceHomEquiv_comp, ← Category.assoc,
      ← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map]

noncomputable def legacyGraySpineFibreTwoIso :
    legacyGraySpineFibre X x ≅
      (X.mappingSpace (x 0) (x 1)).toFunctor ⨯ (X.mappingSpace (x 1) (x 2)).toFunctor :=
  Yoneda.ext _ _ (graySpineFibreTwoHom X x) (graySpineFibreTwoInv X x)
    (fun {T} t => (relativeMappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
      rw [graySpineFibreTwoInv, Equiv.apply_symm_apply]
      dsimp only
      refine grayTensor_spine_hom_ext ?_ ?_
      · rw [grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc, graySpineFibreTwoHom_fst]
      · rw [grayTensorLeft_map_legacyGraySpineEdge₁₂_legacyGraySpineDesc,
        graySpineFibreTwoHom_snd])))
    (fun {T} s => prod.hom_ext ((X.mappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
        rw [graySpineFibreTwoHom_fst, graySpineFibreTwoInv, Equiv.apply_symm_apply]
        dsimp only
        exact grayTensorLeft_map_legacyGraySpineEdge₀₁_legacyGraySpineDesc _ _ _)))
      ((X.mappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
        rw [graySpineFibreTwoHom_snd, graySpineFibreTwoInv, Equiv.apply_symm_apply]
        dsimp only
        exact grayTensorLeft_map_legacyGraySpineEdge₁₂_legacyGraySpineDesc _ _ _))))
    (graySpineFibreTwoHom_comp X x)

private theorem comp_graySpineFibreTwoIso_hom {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X x) :
    t ≫ (legacyGraySpineFibreTwoIso X x).hom = graySpineFibreTwoHom X x t :=
  (graySpineFibreTwoHom_comp X x t (𝟙 _)).symm.trans (congrArg _ (Category.comp_id t))

theorem mappingSpaceHomEquiv_graySpineFibreTwoIso_fst {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySpineFibre X x) :
    (X.mappingSpaceHomEquiv (x 0) (x 1) T (t ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.fst)).1 =
      (grayTensorLeft T).map legacyGraySpineEdge₀₁ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [← Category.assoc, comp_graySpineFibreTwoIso_hom, graySpineFibreTwoHom_fst]

theorem mappingSpaceHomEquiv_graySpineFibreTwoIso_snd {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySpineFibre X x) :
    (X.mappingSpaceHomEquiv (x 1) (x 2) T (t ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.snd)).1 =
      (grayTensorLeft T).map legacyGraySpineEdge₁₂ ≫ (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [← Category.assoc, comp_graySpineFibreTwoIso_hom, graySpineFibreTwoHom_snd]

end SpineFibre

private noncomputable abbrev grayLongEdgeι : ball.{u} (atomSimplex 1) ⟶ SSet.toDiagSet.obj Δ[2] :=
  (toDiagSetObjStdSimplexIso.{u} 1).inv ≫ SSet.toDiagSet.map (SSet.stdSimplex.δ (1 : Fin 3))

noncomputable def grayLongEdge (X : DiagSet.{u}) (x : Fin 3 → X.Vertex) :
    legacyGraySimplexFibre X x ⟶ (X.mappingSpace (x 0) (x 2)).toFunctor :=
  (X.mappingSpaceHomEquiv (x 0) (x 2) _).symm
    ⟨(grayTensorLeft _).map grayLongEdgeι ≫ (relativeMappingSpaceHomEquiv _ _ _ (𝟙 _)).1,
      isFixedEnds_grayTensorLeft_map_comp _ x (relativeMappingSpaceHomEquiv _ _ _ (𝟙 _)).2
        (intervalSource_comp_toDiagSet_map (SimplexCategory.δ 1) rfl)
        (intervalTarget_comp_toDiagSet_map (SimplexCategory.δ 1) rfl)⟩

theorem mappingSpaceHomEquiv_grayLongEdge (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (X.mappingSpaceHomEquiv (x 0) (x 2) T (t ≫ grayLongEdge X x)).1 =
      (grayTensorLeft T).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.δ (1 : Fin 3))) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  have h : (X.mappingSpaceHomEquiv (x 0) (x 2) _ (grayLongEdge X x)).1 =
      (grayTensorLeft _).map grayLongEdgeι ≫ (relativeMappingSpaceHomEquiv _ _ _ (𝟙 _)).1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  rw [DiagSet.mappingSpaceHomEquiv_comp, h, ← Category.assoc,
    ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
    ← relativeMappingSpaceHomEquiv_comp, Category.comp_id]

theorem rlp_monomorphisms_graySpineFibreTwo {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x : Fin 3 → X.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) :=
  (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ (rlp_monomorphisms_legacyGraySegalMap hX x)
    fun _ _ _ _ => inferInstance

noncomputable def grayComposition {H : Type v} [Category.{w} H] (L : DiagSet.Infty.{u} 0 ⥤ H)
    [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))] {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x : Fin 3 → X.Vertex) :
    L.obj ((DiagSet.toInfty 0).obj
        ((X.mappingSpace (x 0) (x 1)).toFunctor ⨯ (X.mappingSpace (x 1) (x 2)).toFunctor)) ⟶
      L.obj ((DiagSet.toInfty 0).obj (X.mappingSpace (x 0) (x 2)).toFunctor) :=
  have := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_graySpineFibreTwo hX x)
  (Localization.isoOfHom L (weakEquivalences _)
      ((DiagSet.toInfty 0).map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom))
      ((weakEquivalence_iff _).1 this)).inv ≫
    L.map ((DiagSet.toInfty 0).map (grayLongEdge X x))

theorem map_graySpineFibreTwo_comp_grayComposition {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (x : Fin 3 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X
      x).hom)) ≫
        grayComposition L hX x =
      L.map ((DiagSet.toInfty 0).map (grayLongEdge X x)) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

section Vertices

variable {X : DiagSet.{u}}

noncomputable def graySimplexFibreSimplex {n : ℕ} (x : Fin (n + 1) → X.Vertex)
    (t : (DiagSet.toSSet.obj (legacyGraySimplexFibre X x)) _⦋0⦌) : (DiagSet.toSSet.obj X) _⦋n⦌ :=
  uliftYonedaEquiv (X := atomSimplex n) (F := X) ((toDiagSetObjStdSimplexIso.{u} n).inv ≫
    inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (relativeMappingSpaceHomEquiv _ _ _ (vertexHom t)).1)

theorem mappingSpaceVerticesEquiv_edge_of_restriction {n : ℕ}
    {x : Fin (n + 1) → X.Vertex} {a b : X.Vertex}
    (g : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor) (φ : ⦋1⦌ ⟶ ⦋n⦌)
    (t : (DiagSet.toSSet.obj (legacyGraySimplexFibre X x)) _⦋0⦌)
    (hg : (X.mappingSpaceHomEquiv a b _ (vertexHom t ≫ g)).1 =
      (grayTensorLeft _).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map φ)) ≫
          (relativeMappingSpaceHomEquiv _ _ _ (vertexHom t)).1) :
    (X.edgeEquivSSet (X.mappingSpaceVerticesEquiv a b
        ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.map g).app _ t)))).edge =
      (DiagSet.toSSet.obj X).map φ.op (graySimplexFibreSimplex x t) := by
  have e : (toDiagSetObjStdSimplexIso.{u} 1).inv ≫ SSet.toDiagSet.map (SSet.stdSimplex.map φ) =
      uliftYoneda.map (simplexHom φ.toOrderHom) ≫ (toDiagSetObjStdSimplexIso.{u} n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, toDiagSet_map_stdSimplex_map_comp_hom]
  have hs : inv (grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1))) ≫
      (grayTensorLeft _).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map φ)) =
      ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫ SSet.toDiagSet.map (SSet.stdSimplex.map φ)) ≫
        inv (grayTensorSnd (ball.{u} atomPoint) _) := by
    rw [IsIso.eq_comp_inv, Category.assoc, grayTensorLeft_map_grayTensorSnd,
      IsIso.inv_hom_id_assoc]
  have hc : vertexHom ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.map g).app (op ⦋0⦌) t)) =
      vertexHom t ≫ g :=
    (vertexHom_comp t g).symm
  rw [DiagSet.mappingSpaceVerticesEquiv_edge, ← DiagSet.mappingSpaceHomEquiv_vertexHom, hc, hg,
    ← Category.assoc, hs, e, Category.assoc, Category.assoc]
  exact (uliftYonedaEquiv_naturality _ (simplexHom φ.toOrderHom).op).symm

theorem mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_fst
    (x : Fin 3 → X.Vertex) {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (X.mappingSpaceHomEquiv (x 0) (x 1) T
        (t ≫ legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.fst)).1 =
      (grayTensorLeft T).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.δ 2))) ≫
          (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [← Category.assoc t, mappingSpaceHomEquiv_graySpineFibreTwoIso_fst,
    relativeMappingSpaceHomEquiv_legacyGraySegalMap, ← Category.assoc, ← Functor.map_comp,
    legacyGraySpineEdge₀₁, Category.assoc, ← Functor.map_comp, SSet.spineSubcomplex.ι₀₁_ι]
  rfl

theorem mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_snd
    (x : Fin 3 → X.Vertex) {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (X.mappingSpaceHomEquiv (x 1) (x 2) T
        (t ≫ legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.snd)).1 =
      (grayTensorLeft T).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.δ 0))) ≫
          (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  rw [← Category.assoc t, mappingSpaceHomEquiv_graySpineFibreTwoIso_snd,
    relativeMappingSpaceHomEquiv_legacyGraySegalMap, ← Category.assoc, ← Functor.map_comp,
    legacyGraySpineEdge₁₂, Category.assoc, ← Functor.map_comp, SSet.spineSubcomplex.ι₁₂_ι]
  rfl

theorem homMk_comp_homMk_grayLongEdge (hX : IsInftyCategory 1 X)
    (x : Fin 3 → X.Vertex)
    (t : (legacyGraySimplexFibre X x).Vertex) :
    HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv _ _
        (t.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.fst))) ≫
      HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv _ _
        (t.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.snd))) =
    HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv _ _ (t.map (grayLongEdge X x))) :=
  homMk_comp_homMk_of_compStruct hX (SSet.Edge.CompStruct.mk (graySimplexFibreSimplex x t)
    (mappingSpaceVerticesEquiv_edge_of_restriction _ _ t
      (mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_fst x _)).symm
    (mappingSpaceVerticesEquiv_edge_of_restriction _ _ t
      (mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_snd x _)).symm
    (mappingSpaceVerticesEquiv_edge_of_restriction _ (SimplexCategory.δ 1) t
      (mappingSpaceHomEquiv_grayLongEdge X x _)).symm)

theorem exists_vertex_graySimplexFibre (hX : IsInftyCategory 1 X)
    (x : Fin 3 → X.Vertex)
    (a : DiagSet.Vertex (X.mappingSpace (x 0) (x 1)).toFunctor)
    (b : DiagSet.Vertex (X.mappingSpace (x 1) (x 2)).toFunctor) :
    ∃ t : (legacyGraySimplexFibre X x).Vertex,
      t.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.fst) = a ∧
        t.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.snd) = b := by
  have sq : CommSq (initial.to _) (initial.to (ball.{u} atomPoint))
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) (prod.lift (vertexHom a)
        (vertexHom b)) :=
    ⟨initial.hom_ext _ _⟩
  have := rlp_monomorphisms_graySpineFibreTwo hX x (initial.to (ball.{u} atomPoint))
    inferInstance
  have hl : vertexHom (uliftYonedaEquiv (X := atomSimplex 0) (F := legacyGraySimplexFibre X x)
    sq.lift) =
      sq.lift :=
    Equiv.symm_apply_apply _ _
  refine ⟨uliftYonedaEquiv (X := atomSimplex 0) (F := legacyGraySimplexFibre X x) sq.lift,
    (uliftYonedaEquiv (X := atomSimplex 0)).symm.injective ?_,
    (uliftYonedaEquiv (X := atomSimplex 0)).symm.injective ?_⟩
  · refine (vertexHom_comp _
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.fst)).symm.trans ?_
    rw [hl, ← Category.assoc (legacyGraySegalMap X x), ← Category.assoc, sq.fac_right,
      prod.lift_fst]
    rfl
  · refine (vertexHom_comp _
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom ≫ prod.snd)).symm.trans ?_
    rw [hl, ← Category.assoc (legacyGraySegalMap X x), ← Category.assoc, sq.fac_right,
      prod.lift_snd]
    rfl

end Vertices

end Atoms.Diagrammatic
