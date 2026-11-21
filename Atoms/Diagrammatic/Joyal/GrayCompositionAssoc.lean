import Atoms.Diagrammatic.Joyal.GrayComposition

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Homotopical Atoms.Shape Simplicial

universe u v w

namespace Atoms.Diagrammatic

section SimplexFibreMap

variable (X : DiagSet.{u})

theorem graySimplexVerticesι_comp_toDiagSet_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    legacyGraySimplexVerticesι.{u} m ≫ SSet.toDiagSet.map (SSet.stdSimplex.map f) =
      Sigma.desc (fun k => Sigma.ι (fun _ : Fin (n + 1) => ball.{u} atomPoint)
        (f.toOrderHom k)) ≫ legacyGraySimplexVerticesι n := by
  rw [← cancel_mono (toDiagSetObjStdSimplexIso.{u} n).hom]
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [Category.assoc, toDiagSet_map_stdSimplex_map_comp_hom, ← Category.assoc,
    ← Category.assoc, Category.assoc _ (legacyGraySimplexVerticesι m),
      ι_graySimplexVerticesι_comp_hom,
    Category.assoc, Sigma.ι_desc_assoc, ι_graySimplexVerticesι_comp_hom]
  exact (Functor.map_comp (simplexFunctor ⋙ uliftYoneda.{u}) _ f).symm.trans
    (congrArg (simplexFunctor ⋙ uliftYoneda.{u}).map (SimplexCategory.const_comp _ f k))

theorem graySimplexVerticesHomEquiv_symm_of_comp {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : Fin (n + 1) → X.Vertex) (y : Fin (m + 1) → X.Vertex)
    (h : ∀ k, x (f.toOrderHom k) = y k) :
    (graySimplexVerticesHomEquiv m X).symm y =
      Sigma.desc (fun k => Sigma.ι (fun _ : Fin (n + 1) => ball.{u} atomPoint)
        (f.toOrderHom k)) ≫ (graySimplexVerticesHomEquiv n X).symm x := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [ι_graySimplexVerticesHomEquiv_symm, Sigma.ι_desc_assoc, ι_graySimplexVerticesHomEquiv_symm,
    h k]

noncomputable def graySimplexFibreMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : Fin (n + 1) → X.Vertex) (y : Fin (m + 1) → X.Vertex)
    (h : ∀ k, x (f.toOrderHom k) = y k) :
    legacyGraySimplexFibre X x ⟶ legacyGraySimplexFibre X y :=
  relativeMappingSpaceMapOfSquare (SSet.toDiagSet.map (SSet.stdSimplex.map f)) _
    (graySimplexVerticesι_comp_toDiagSet_map f)
    (graySimplexVerticesHomEquiv_symm_of_comp X f x y h)

theorem relativeMappingSpaceHomEquiv_graySimplexFibreMap {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (x : Fin (n + 1) → X.Vertex)
    (y : Fin (m + 1) → X.Vertex) (h : ∀ k, x (f.toOrderHom k) = y k)
    {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (relativeMappingSpaceHomEquiv _ _ T (t ≫ graySimplexFibreMap X f x y h)).1 =
      (grayTensorLeft T).map (SSet.toDiagSet.map (SSet.stdSimplex.map f)) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 :=
  relativeMappingSpaceHomEquiv_relativeMappingSpaceMapOfSquare _ _ _ _ t

theorem graySimplexFibreMap_id {n : ℕ} (x : Fin (n + 1) → X.Vertex) :
    graySimplexFibreMap X (𝟙 ⦋n⦌) x x (fun _ => rfl) = 𝟙 _ := by
  have h := relativeMappingSpaceHomEquiv_graySimplexFibreMap X (𝟙 ⦋n⦌) x x (fun _ => rfl) (𝟙 _)
  have e : SSet.stdSimplex.{u}.map (𝟙 ⦋n⦌) = 𝟙 _ := SSet.stdSimplex.map_id _
  rw [Category.id_comp, e, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact (relativeMappingSpaceHomEquiv _ _ _).injective (Subtype.ext h)

theorem graySimplexFibreMap_comp {l m n : ℕ} (f : ⦋l⦌ ⟶ ⦋m⦌)
    (g : ⦋m⦌ ⟶ ⦋n⦌) (x : Fin (n + 1) → X.Vertex)
    (y : Fin (m + 1) → X.Vertex) (z : Fin (l + 1) → X.Vertex)
    (hg : ∀ k, x (g.toOrderHom k) = y k) (hf : ∀ k, y (f.toOrderHom k) = z k) :
    graySimplexFibreMap X g x y hg ≫ graySimplexFibreMap X f y z hf =
      graySimplexFibreMap X (f ≫ g) x z (fun k => (hg _).trans (hf k)) := by
  have h := relativeMappingSpaceHomEquiv_graySimplexFibreMap X (f ≫ g) x z
    (fun k => (hg _).trans (hf k)) (𝟙 _)
  rw [Category.id_comp] at h
  refine (relativeMappingSpaceHomEquiv _ _ _).injective (Subtype.ext ?_)
  rw [h, relativeMappingSpaceHomEquiv_graySimplexFibreMap,
    ← Category.id_comp (graySimplexFibreMap X g x y hg),
    relativeMappingSpaceHomEquiv_graySimplexFibreMap, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← SSet.stdSimplex.{u}.map_comp f g]

end SimplexFibreMap

def IsEdgeRestriction {X : DiagSet.{u}} {n : ℕ}
    {x : Fin (n + 1) → X.Vertex} {a b : X.Vertex}
    (g : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor) (φ : ⦋1⦌ ⟶ ⦋n⦌) : Prop :=
  ∀ ⦃T : DiagSet.{u}⦄ (t : T ⟶ legacyGraySimplexFibre X x),
    (X.mappingSpaceHomEquiv a b T (t ≫ g)).1 =
      (grayTensorLeft T).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map φ)) ≫ (relativeMappingSpaceHomEquiv _ _ T t).1

namespace IsEdgeRestriction

variable {X : DiagSet.{u}} {n : ℕ} {x : Fin (n + 1) → X.Vertex}
  {a b : X.Vertex}

theorem eq {g g' : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor}
    {φ : ⦋1⦌ ⟶ ⦋n⦌} (hg : IsEdgeRestriction g φ) (hg' : IsEdgeRestriction g' φ) : g = g' := by
  have h := hg (𝟙 _)
  have h' := hg' (𝟙 _)
  rw [Category.id_comp] at h h'
  exact (X.mappingSpaceHomEquiv a b _).injective (Subtype.ext (h.trans h'.symm))

theorem comp {m : ℕ} {y : Fin (m + 1) → X.Vertex}
    {g : legacyGraySimplexFibre X y ⟶ (X.mappingSpace a b).toFunctor} {φ : ⦋1⦌ ⟶ ⦋m⦌}
    (hg : IsEdgeRestriction g φ) (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k) :
    IsEdgeRestriction (graySimplexFibreMap X f x y h ≫ g) (φ ≫ f) := fun T t => by
  rw [← Category.assoc, hg, relativeMappingSpaceHomEquiv_graySimplexFibreMap, ← Category.assoc,
    ← Functor.map_comp, Category.assoc, ← Functor.map_comp, ← SSet.stdSimplex.{u}.map_comp]

end IsEdgeRestriction

noncomputable def graySimplexEdge (X : DiagSet.{u}) {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) (i j : Fin (n + 1)) (hij : i ≤ j) :
    legacyGraySimplexFibre X x ⟶ (X.mappingSpace (x i) (x j)).toFunctor :=
  graySimplexFibreMap X (SimplexCategory.mkOfLe i j hij) x ![x i, x j]
      (fun k => by fin_cases k <;> rfl) ≫
    (graySimplexFibreOneIso X ![x i, x j]).hom

theorem mappingSpaceHomEquiv_graySimplexEdge (X : DiagSet.{u}) {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) (i j : Fin (n + 1)) (hij : i ≤ j)
    {T : DiagSet.{u}} (t : T ⟶ legacyGraySimplexFibre X x) :
    (X.mappingSpaceHomEquiv (x i) (x j) T (t ≫ graySimplexEdge X x i j hij)).1 =
      (grayTensorLeft T).map ((toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.mkOfLe i j hij))) ≫
        (relativeMappingSpaceHomEquiv _ _ T t).1 := by
  have h := mappingSpaceHomEquiv_graySimplexFibreOneIso X ![x i, x j]
    (t ≫ graySimplexFibreMap X (SimplexCategory.mkOfLe i j hij) x ![x i, x j]
      (fun k => by fin_cases k <;> rfl))
  rw [relativeMappingSpaceHomEquiv_graySimplexFibreMap, ← Category.assoc, ← Functor.map_comp,
    Category.assoc] at h
  exact h

private theorem isEdgeRestriction_graySimplexEdge (X : DiagSet.{u}) {n : ℕ}
    (x : Fin (n + 1) → X.Vertex) (i j : Fin (n + 1)) (hij : i ≤ j) :
    IsEdgeRestriction (graySimplexEdge X x i j hij) (SimplexCategory.mkOfLe i j hij) :=
  fun _ t => mappingSpaceHomEquiv_graySimplexEdge X x i j hij t

theorem isEdgeRestriction_grayLongEdge (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    IsEdgeRestriction (grayLongEdge X x) (SimplexCategory.δ 1) :=
  fun _ t => mappingSpaceHomEquiv_grayLongEdge X x t

theorem grayLongEdge_eq_graySimplexEdge (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    grayLongEdge X x = graySimplexEdge X x 0 2 (by decide) := by
  have e : SimplexCategory.δ (1 : Fin 3) = SimplexCategory.mkOfLe 0 2 (by decide) := by decide
  exact (isEdgeRestriction_grayLongEdge X x).eq
    (e ▸ isEdgeRestriction_graySimplexEdge X x 0 2 (by decide))

section SpineHom

variable {T Y : DiagSet.{u}}

private theorem graySpineVerticesι_comp_ι (p : ℕ) :
    legacyGraySpineVerticesι.{u} p ≫ SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι =
      legacyGraySimplexVerticesι p :=
  rfl

private noncomputable def grayTensorToDiagSetHomEquiv (T : DiagSet.{u}) (K : SSet.{u})
    (Y : DiagSet.{u}) :
    (grayTensor T (SSet.toDiagSet.obj K) ⟶ Y) ≃ (K ⟶ DiagSet.toSSet.obj ((grayHomLeft T).obj Y)) :=
  ((grayTensorLeftAdjunction T).homEquiv _ _).trans (sSetDiagSetAdj.homEquiv _ _)

private theorem grayTensorToDiagSetHomEquiv_comp {K K' : SSet.{u}} (g : K' ⟶ K)
    (G : grayTensor T (SSet.toDiagSet.obj K) ⟶ Y) :
    grayTensorToDiagSetHomEquiv T K' Y ((grayTensorLeft T).map (SSet.toDiagSet.map g) ≫ G) =
      g ≫ grayTensorToDiagSetHomEquiv T K Y G := by
  dsimp only [grayTensorToDiagSetHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]

private theorem grayTensorLeft_map_toDiagSet_map_yonedaEquiv_symm_comp {K : SSet.{u}} {d : ℕ}
    (G : grayTensor T (SSet.toDiagSet.obj K) ⟶ Y) (v : K _⦋d⦌) :
    (grayTensorLeft T).map (SSet.toDiagSet.map (SSet.yonedaEquiv.symm v)) ≫ G =
      (grayTensorToDiagSetHomEquiv T _ Y).symm
        (SSet.yonedaEquiv.symm ((grayTensorToDiagSetHomEquiv T K Y G).app _ v)) := by
  refine (grayTensorToDiagSetHomEquiv T _ Y).injective ?_
  rw [Equiv.apply_symm_apply]
  refine SSet.yonedaEquiv.injective ?_
  rw [Equiv.apply_symm_apply, grayTensorToDiagSetHomEquiv_comp, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply]

private noncomputable def toDiagSetObjStdSimplexZeroIso :
    SSet.toDiagSet.{u}.obj Δ[0] ≅ ball.{u} atomPoint :=
  toDiagSetObjStdSimplexIso 0

private theorem ι_graySpineVerticesι (p : ℕ) (k : Fin (p + 1)) :
    Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p =
      toDiagSetObjStdSimplexZeroIso.{u}.inv ≫
        SSet.toDiagSet.map
          (SSet.yonedaEquiv.symm ((SSet.spineSubcomplex.spineId.{u} p).vertex k)) := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) := SSet.toDiagSet.map_mono _
  rw [← cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι), Category.assoc,
    graySpineVerticesι_comp_ι, Category.assoc, ← Functor.map_comp,
    ← cancel_mono (toDiagSetObjStdSimplexIso.{u} p).hom, Category.assoc,
    ι_graySimplexVerticesι_comp_hom, Category.assoc]
  exact (toDiagSetObjStdSimplexZeroIso.{u}.inv_comp_eq.2
    (toDiagSet_map_stdSimplex_map_comp_hom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k))).symm

noncomputable def legacyGraySpineEdge (p : ℕ) (i : Fin p) :
    ball.{u} (atomSimplex 1) ⟶ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet) :=
  (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
    SSet.toDiagSet.map (SSet.yonedaEquiv.symm ((SSet.spineSubcomplex.spineId.{u} p).arrow i))

theorem legacyGraySpineEdge_comp_ι (p : ℕ) (i : Fin p) :
    legacyGraySpineEdge.{u} p i ≫ SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι =
      (toDiagSetObjStdSimplexIso.{u} 1).inv ≫
        SSet.toDiagSet.map (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i)) := by
  rw [legacyGraySpineEdge, Category.assoc, ← Functor.map_comp]
  rfl

theorem intervalSource_comp_legacyGraySpineEdge (p : ℕ) (i : Fin p) :
    intervalSource ≫ legacyGraySpineEdge.{u} p i =
      Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) i.castSucc ≫
        legacyGraySpineVerticesι p := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) := SSet.toDiagSet.map_mono _
  rw [← cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι), Category.assoc,
    legacyGraySpineEdge_comp_ι, Category.assoc, graySpineVerticesι_comp_ι]
  exact intervalSource_comp_toDiagSet_map _ rfl

theorem intervalTarget_comp_legacyGraySpineEdge (p : ℕ) (i : Fin p) :
    intervalTarget ≫ legacyGraySpineEdge.{u} p i =
      Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) i.succ ≫
        legacyGraySpineVerticesι p := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) := SSet.toDiagSet.map_mono _
  rw [← cancel_mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι), Category.assoc,
    legacyGraySpineEdge_comp_ι, Category.assoc, graySpineVerticesι_comp_ι]
  exact intervalTarget_comp_toDiagSet_map _ rfl

theorem legacyGrayTensor_spineSubcomplex_hom_ext {p : ℕ}
    {φ ψ : grayTensor T (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet)) ⟶ Y}
    (hv : ∀ k, (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p) ≫ φ =
      (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p) ≫ ψ)
    (he : ∀ i, (grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ φ =
      (grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ ψ) :
    φ = ψ := by
  have key {d : ℕ} (v : (SSet.spineSubcomplex.{u} p : SSet) _⦋d⦌) (e : _ ⟶ ball.{u} (atomSimplex d))
      [IsIso e] (h : (grayTensorLeft T).map (inv e ≫ SSet.toDiagSet.map (SSet.yonedaEquiv.symm v)) ≫
        φ = (grayTensorLeft T).map (inv e ≫ SSet.toDiagSet.map (SSet.yonedaEquiv.symm v)) ≫ ψ) :
      (grayTensorToDiagSetHomEquiv T _ Y φ).app _ v =
        (grayTensorToDiagSetHomEquiv T _ Y ψ).app _ v := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, cancel_epi] at h
    rw [grayTensorLeft_map_toDiagSet_map_yonedaEquiv_symm_comp,
      grayTensorLeft_map_toDiagSet_map_yonedaEquiv_symm_comp] at h
    exact SSet.yonedaEquiv.symm.injective ((grayTensorToDiagSetHomEquiv T _ Y).symm.injective h)
  refine (grayTensorToDiagSetHomEquiv T _ Y).injective
    ((SSet.spineSubcomplexHomEquiv p _).injective ?_)
  rw [SSet.spineSubcomplexHomEquiv_apply, SSet.spineSubcomplexHomEquiv_apply]
  refine SSet.Path.ext (funext fun k => ?_) (funext fun i => ?_)
  · refine key _ (toDiagSetObjStdSimplexIso.{u} 0).hom ?_
    have hk := hv k
    rw [ι_graySpineVerticesι] at hk
    rw [IsIso.Iso.inv_hom]
    exact hk
  · refine key _ (toDiagSetObjStdSimplexIso.{u} 1).hom ?_
    rw [IsIso.Iso.inv_hom]
    exact he i

section Desc

variable {X : DiagSet.{u}} {p : ℕ} (x : Fin (p + 1) → X.Vertex)
  (F : Fin p → (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ X))
  (hF : ∀ i, IsFixedEnds (x i.castSucc) (x i.succ) (F i))

private noncomputable def graySpinePath :
    SSet.Path (DiagSet.toSSet.obj ((grayHomLeft T).obj X)) p where
  vertex k := SSet.yonedaEquiv (grayTensorToDiagSetHomEquiv T _ X
    ((grayTensorLeft T).map (toDiagSetObjStdSimplexIso.{u} 0).hom ≫
      grayTensorSnd T _ ≫ vertexHom (x k)))
  arrow i := SSet.yonedaEquiv (grayTensorToDiagSetHomEquiv T _ X
    ((grayTensorLeft T).map (toDiagSetObjStdSimplexIso.{u} 1).hom ≫ F i))
  arrow_src i := by
    have h : (grayTensorLeft T).map (SSet.toDiagSet.map (SSet.stdSimplex.map
        (SimplexCategory.δ (1 : Fin 2)))) ≫ (grayTensorLeft T).map
          (toDiagSetObjStdSimplexIso.{u} 1).hom ≫ F i = (grayTensorLeft T).map
          (toDiagSetObjStdSimplexIso.{u} 0).hom ≫ grayTensorSnd T _ ≫
            vertexHom (x i.castSucc) := by
      rw [← Category.assoc, ← Functor.map_comp, toDiagSet_map_stdSimplex_map_comp_hom,
        Functor.map_comp, Category.assoc]
      exact congrArg _ (hF i).1
    exact (SSet.yonedaEquiv_naturality (X := DiagSet.toSSet.obj ((grayHomLeft T).obj X))
      (SimplexCategory.δ (1 : Fin 2)) _).trans (congrArg SSet.yonedaEquiv
        ((grayTensorToDiagSetHomEquiv_comp _ _).symm.trans (congrArg _ h)))
  arrow_tgt i := by
    have h : (grayTensorLeft T).map (SSet.toDiagSet.map (SSet.stdSimplex.map
        (SimplexCategory.δ (0 : Fin 2)))) ≫ (grayTensorLeft T).map
          (toDiagSetObjStdSimplexIso.{u} 1).hom ≫ F i = (grayTensorLeft T).map
          (toDiagSetObjStdSimplexIso.{u} 0).hom ≫ grayTensorSnd T _ ≫
            vertexHom (x i.succ) := by
      rw [← Category.assoc, ← Functor.map_comp, toDiagSet_map_stdSimplex_map_comp_hom,
        Functor.map_comp, Category.assoc]
      exact congrArg _ (hF i).2
    exact (SSet.yonedaEquiv_naturality (X := DiagSet.toSSet.obj ((grayHomLeft T).obj X))
      (SimplexCategory.δ (0 : Fin 2)) _).trans (congrArg SSet.yonedaEquiv
        ((grayTensorToDiagSetHomEquiv_comp _ _).symm.trans (congrArg _ h)))

noncomputable def legacyGraySpineSubcomplexDesc :
    grayTensor T (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet)) ⟶ X :=
  (grayTensorToDiagSetHomEquiv T _ X).symm
    ((SSet.spineSubcomplexHomEquiv p _).symm (graySpinePath x F hF))

private theorem spineId_map_legacyGraySpineSubcomplexDesc :
    (SSet.spineSubcomplex.spineId.{u} p).map
        (grayTensorToDiagSetHomEquiv T _ X (legacyGraySpineSubcomplexDesc x F hF)) =
      graySpinePath x F hF := by
  rw [← SSet.spineSubcomplexHomEquiv_apply, legacyGraySpineSubcomplexDesc, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

theorem grayTensorLeft_map_ι_graySpineVerticesι_legacyGraySpineSubcomplexDesc (k : Fin (p + 1)) :
    (grayTensorLeft T).map
        (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySpineVerticesι p) ≫
      legacyGraySpineSubcomplexDesc x F hF = grayTensorSnd T _ ≫ vertexHom (x k) := by
  rw [ι_graySpineVerticesι, Functor.map_comp, Category.assoc,
    grayTensorLeft_map_toDiagSet_map_yonedaEquiv_symm_comp]
  have h := congrArg (fun γ => γ.vertex k) (spineId_map_legacyGraySpineSubcomplexDesc x F hF)
  dsimp only [SSet.Path.map_vertex] at h
  rw [h]
  dsimp only [graySpinePath]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Category.assoc, ← Functor.map_comp]
  exact (congrArg (· ≫ grayTensorSnd T (ball.{u} atomPoint) ≫ vertexHom (x k))
    ((congrArg (grayTensorLeft T).map toDiagSetObjStdSimplexZeroIso.{u}.inv_hom_id).trans
      ((grayTensorLeft T).map_id _))).trans (Category.id_comp _)

theorem grayTensorLeft_map_legacyGraySpineEdge_legacyGraySpineSubcomplexDesc (i : Fin p) :
    (grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ legacyGraySpineSubcomplexDesc x F hF = F i
      := by
  rw [legacyGraySpineEdge, Functor.map_comp, Category.assoc,
    grayTensorLeft_map_toDiagSet_map_yonedaEquiv_symm_comp]
  have h := congrArg (fun γ => γ.arrow i) (spineId_map_legacyGraySpineSubcomplexDesc x F hF)
  dsimp only [SSet.Path.map_arrow] at h
  rw [h]
  dsimp only [graySpinePath]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end Desc

end SpineHom

section SpineFibre

variable (X : DiagSet.{u}) {p : ℕ} (x : Fin (p + 1) → X.Vertex)

private noncomputable def graySpineFibreHom {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X x) :
    T ⟶ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor :=
  Pi.lift fun i => (X.mappingSpaceHomEquiv _ _ T).symm
    ⟨(grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ (relativeMappingSpaceHomEquiv _ _ T t).1,
      isFixedEnds_grayTensorLeft_map_comp _ x (relativeMappingSpaceHomEquiv _ _ T t).2
        (intervalSource_comp_legacyGraySpineEdge p i) (intervalTarget_comp_legacyGraySpineEdge p i)⟩

private theorem graySpineFibreHom_π {T : DiagSet.{u}} (t : T ⟶ legacyGraySpineFibre X x) (i : Fin
  p) :
    (X.mappingSpaceHomEquiv _ _ T (graySpineFibreHom X x t ≫ Pi.π _ i)).1 =
      (grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ (relativeMappingSpaceHomEquiv _ _ T t).1
        := by
  rw [graySpineFibreHom, Pi.lift_π, Equiv.apply_symm_apply]

private noncomputable def graySpineFibreInv {T : DiagSet.{u}}
    (s : T ⟶ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor) :
    T ⟶ legacyGraySpineFibre X x :=
  (relativeMappingSpaceHomEquiv _ _ T).symm
    ⟨legacyGraySpineSubcomplexDesc x (fun i => (X.mappingSpaceHomEquiv _ _ T (s ≫ Pi.π _ i)).1)
      (fun i => (X.mappingSpaceHomEquiv _ _ T (s ≫ Pi.π _ i)).2), by
      refine grayTensor_sigma_hom_ext T _ fun k => ?_
      rw [← Category.assoc, ← Functor.map_comp,
        grayTensorLeft_map_ι_graySpineVerticesι_legacyGraySpineSubcomplexDesc, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, ι_graySimplexVerticesHomEquiv_symm]⟩

private theorem graySpineFibreHom_comp {T T' : DiagSet.{u}} (g : T' ⟶ T)
    (t : T ⟶ legacyGraySpineFibre X x) :
    graySpineFibreHom X x (g ≫ t) = g ≫ graySpineFibreHom X x t :=
  Pi.hom_ext _ _ fun i => (X.mappingSpaceHomEquiv _ _ T').injective (Subtype.ext (by
    rw [graySpineFibreHom_π, Category.assoc, DiagSet.mappingSpaceHomEquiv_comp,
      graySpineFibreHom_π, relativeMappingSpaceHomEquiv_comp, ← Category.assoc,
      ← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map]))

noncomputable def legacyGraySpineFibreIso :
    legacyGraySpineFibre X x ≅ ∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x
      i.succ)).toFunctor :=
  Yoneda.ext _ _ (graySpineFibreHom X x) (graySpineFibreInv X x)
    (fun {T} t => (relativeMappingSpaceHomEquiv _ _ T).injective (Subtype.ext (by
      rw [graySpineFibreInv, Equiv.apply_symm_apply]
      dsimp only
      refine legacyGrayTensor_spineSubcomplex_hom_ext (fun k => ?_) (fun i => ?_)
      · rw [grayTensorLeft_map_ι_graySpineVerticesι_legacyGraySpineSubcomplexDesc,
          grayTensorLeft_map_ι_comp_of_comp_eq _ x (relativeMappingSpaceHomEquiv _ _ T t).2]
      · rw [grayTensorLeft_map_legacyGraySpineEdge_legacyGraySpineSubcomplexDesc,
        graySpineFibreHom_π])))
    (fun {T} s => Pi.hom_ext _ _ fun i => (X.mappingSpaceHomEquiv _ _ T).injective
      (Subtype.ext (by
        rw [graySpineFibreHom_π, graySpineFibreInv, Equiv.apply_symm_apply]
        exact grayTensorLeft_map_legacyGraySpineEdge_legacyGraySpineSubcomplexDesc _ _ _ i)))
    (graySpineFibreHom_comp X x)

theorem mappingSpaceHomEquiv_legacyGraySpineFibreIso (i : Fin p) {T : DiagSet.{u}}
    (t : T ⟶ legacyGraySpineFibre X x) :
    (X.mappingSpaceHomEquiv _ _ T (t ≫ (legacyGraySpineFibreIso X x).hom ≫ Pi.π _ i)).1 =
      (grayTensorLeft T).map (legacyGraySpineEdge p i) ≫ (relativeMappingSpaceHomEquiv _ _ T t).1
        := by
  have e : t ≫ (legacyGraySpineFibreIso X x).hom = graySpineFibreHom X x t :=
    (graySpineFibreHom_comp X x t (𝟙 _)).symm.trans (congrArg _ (Category.comp_id t))
  rw [← Category.assoc, e, graySpineFibreHom_π]

end SpineFibre

theorem graySegalMap_graySpineFibreIso_hom_π (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) (i : Fin p) :
    legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom ≫ Pi.π _ i =
      graySimplexEdge X x i.castSucc i.succ i.castSucc_le_succ := by
  have h : IsEdgeRestriction (legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom ≫ Pi.π _ i)
      (SimplexCategory.mkOfSucc i) := fun T t => by
    rw [← Category.assoc t, mappingSpaceHomEquiv_legacyGraySpineFibreIso,
      relativeMappingSpaceHomEquiv_legacyGraySegalMap, ← Category.assoc, ← Functor.map_comp,
      legacyGraySpineEdge_comp_ι]
  have e : SimplexCategory.mkOfSucc i =
      SimplexCategory.mkOfLe i.castSucc i.succ i.castSucc_le_succ :=
    SimplexCategory.Hom.ext_one_left _ _
  exact h.eq (e ▸ isEdgeRestriction_graySimplexEdge X x _ _ _)

theorem rlp_monomorphisms_graySpineFibreIso {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      (legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom) :=
  (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ (rlp_monomorphisms_legacyGraySegalMap hX x)
    fun _ _ _ _ => inferInstance

noncomputable def graySpineComposition {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    L.obj ((DiagSet.toInfty 0).obj
        (∏ᶜ fun i : Fin p => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor)) ⟶
      L.obj ((DiagSet.toInfty 0).obj (X.mappingSpace (x 0) (x (Fin.last p))).toFunctor) :=
  have := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_graySpineFibreIso hX x)
  (Localization.isoOfHom L (weakEquivalences _)
      ((DiagSet.toInfty 0).map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom))
      ((weakEquivalence_iff _).1 this)).inv ≫
    L.map ((DiagSet.toInfty 0).map (graySimplexEdge X x 0 (Fin.last p) (Fin.zero_le _)))

@[reassoc]
theorem map_graySpineFibreIso_comp_graySpineComposition {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom)) ≫
        graySpineComposition L hX x =
      L.map ((DiagSet.toInfty 0).map (graySimplexEdge X x 0 (Fin.last p) (Fin.zero_le _))) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

private theorem rlp_monomorphisms_prodMap_id {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (monomorphisms DiagSet.{u}).rlp g) (M : DiagSet.{u}) :
    (monomorphisms DiagSet.{u}).rlp (prod.map g (𝟙 M)) :=
  (monomorphisms DiagSet.{u}).rlp.of_isPullback (IsPullback.of_prod_fst_with_id g M) hg

private theorem rlp_monomorphisms_prodMap_id_left {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (monomorphisms DiagSet.{u}).rlp g) (M : DiagSet.{u}) :
    (monomorphisms DiagSet.{u}).rlp (prod.map (𝟙 M) g) := by
  have e : prod.map (𝟙 M) g =
      (prod.braiding M A).hom ≫ prod.map g (𝟙 M) ≫ (prod.braiding B M).hom := by
    refine prod.hom_ext ?_ ?_
    · rw [prod.map_fst, Category.comp_id, Category.assoc, Category.assoc, prod.braiding_hom B M,
        prod.lift_fst, prod.map_snd, Category.comp_id, prod.braiding_hom, prod.lift_snd]
    · rw [prod.map_snd, Category.assoc, Category.assoc, prod.braiding_hom B M, prod.lift_snd,
        prod.map_fst, prod.braiding_hom, prod.lift_fst_assoc]
  rw [e]
  exact (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ (fun _ _ _ _ => inferInstance)
    ((monomorphisms DiagSet.{u}).rlp.comp_mem _ _ (rlp_monomorphisms_prodMap_id hg M)
      fun _ _ _ _ => inferInstance)

section Whisker

variable {H : Type v} [Category.{w} H] (L : DiagSet.Infty.{u} 0 ⥤ H)
  [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))] {X : DiagSet.{u}}
  (hX : IsInftyCategory 1 X)

noncomputable def grayCompositionWhiskerRight (x : Fin 3 → X.Vertex)
    (M : DiagSet.{u}) :
    L.obj ((DiagSet.toInfty 0).obj (((X.mappingSpace (x 0) (x 1)).toFunctor ⨯
        (X.mappingSpace (x 1) (x 2)).toFunctor) ⨯ M)) ⟶
      L.obj ((DiagSet.toInfty 0).obj ((X.mappingSpace (x 0) (x 2)).toFunctor ⨯ M)) :=
  have := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_prodMap_id (rlp_monomorphisms_graySpineFibreTwo hX x) M)
  (Localization.isoOfHom L (weakEquivalences _)
      ((DiagSet.toInfty 0).map
        (prod.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) (𝟙 M)))
      ((weakEquivalence_iff _).1 this)).inv ≫
    L.map ((DiagSet.toInfty 0).map (prod.map (grayLongEdge X x) (𝟙 M)))

@[reassoc]
theorem map_prodMap_graySpineFibreTwo_comp_grayCompositionWhiskerRight
    (x : Fin 3 → X.Vertex) (M : DiagSet.{u}) :
    L.map ((DiagSet.toInfty 0).map
        (prod.map (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) (𝟙 M))) ≫
        grayCompositionWhiskerRight L hX x M =
      L.map ((DiagSet.toInfty 0).map (prod.map (grayLongEdge X x) (𝟙 M))) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

noncomputable def grayCompositionWhiskerLeft (M : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    L.obj ((DiagSet.toInfty 0).obj (M ⨯ ((X.mappingSpace (x 0) (x 1)).toFunctor ⨯
        (X.mappingSpace (x 1) (x 2)).toFunctor))) ⟶
      L.obj ((DiagSet.toInfty 0).obj (M ⨯ (X.mappingSpace (x 0) (x 2)).toFunctor)) :=
  have := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_prodMap_id_left (rlp_monomorphisms_graySpineFibreTwo hX x) M)
  (Localization.isoOfHom L (weakEquivalences _)
      ((DiagSet.toInfty 0).map
        (prod.map (𝟙 M) (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom)))
      ((weakEquivalence_iff _).1 this)).inv ≫
    L.map ((DiagSet.toInfty 0).map (prod.map (𝟙 M) (grayLongEdge X x)))

@[reassoc]
theorem map_prodMap_graySpineFibreTwo_comp_grayCompositionWhiskerLeft (M : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map
        (prod.map (𝟙 M) (legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom))) ≫
        grayCompositionWhiskerLeft L hX M x =
      L.map ((DiagSet.toInfty 0).map (prod.map (𝟙 M) (grayLongEdge X x))) :=
  Localization.isoOfHom_hom_inv_id_assoc L _ _ _ _

end Whisker

theorem IsEdgeRestriction.eq_of_eq {X : DiagSet.{u}} {n : ℕ}
    {x : Fin (n + 1) → X.Vertex} {a b : X.Vertex}
    {g g' : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor} {φ φ' : ⦋1⦌ ⟶ ⦋n⦌}
    (hg : IsEdgeRestriction g φ) (hg' : IsEdgeRestriction g' φ') (h : φ = φ') : g = g' :=
  hg.eq (h ▸ hg')

section EdgeRestriction

variable {X : DiagSet.{u}} {n m : ℕ} {x : Fin (n + 1) → X.Vertex}
  {y : Fin (m + 1) → X.Vertex} {a b : X.Vertex}
  {P Q R : DiagSet.{u}} {φ : ⦋1⦌ ⟶ ⦋m⦌} {ψ : ⦋1⦌ ⟶ ⦋n⦌}

theorem IsEdgeRestriction.comp_assoc {A : legacyGraySimplexFibre X y ⟶ P}
    {c : P ⟶ (X.mappingSpace a b).toFunctor} (hg : IsEdgeRestriction (A ≫ c) φ)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k) :
    IsEdgeRestriction ((graySimplexFibreMap X f x y h ≫ A) ≫ c) (φ ≫ f) := by
  rw [Category.assoc]
  exact hg.comp f h

private theorem IsEdgeRestriction.lift_map_fst
    {A : legacyGraySimplexFibre X y ⟶ (X.mappingSpace a b).toFunctor}
    (hA : IsEdgeRestriction A φ) (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k)
    (g : legacyGraySimplexFibre X x ⟶ Q) (k : Q ⟶ R) :
    IsEdgeRestriction ((prod.lift (graySimplexFibreMap X f x y h) g ≫ prod.map A k) ≫ prod.fst)
      (φ ≫ f) := by
  rw [prod.lift_map, prod.lift_fst]
  exact hA.comp f h

private theorem IsEdgeRestriction.lift_map_fst_comp {A : legacyGraySimplexFibre X y ⟶ P}
    {c : P ⟶ (X.mappingSpace a b).toFunctor} (hA : IsEdgeRestriction (A ≫ c) φ)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k)
    (g : legacyGraySimplexFibre X x ⟶ Q) (k : Q ⟶ R) :
    IsEdgeRestriction
      (((prod.lift (graySimplexFibreMap X f x y h) g ≫ prod.map A k) ≫ prod.fst) ≫ c) (φ ≫ f) := by
  rw [prod.lift_map, prod.lift_fst]
  exact hA.comp_assoc f h

private theorem IsEdgeRestriction.lift_map_snd
    {A : legacyGraySimplexFibre X y ⟶ (X.mappingSpace a b).toFunctor}
    (hA : IsEdgeRestriction A φ) (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k)
    (g : legacyGraySimplexFibre X x ⟶ Q) (k : Q ⟶ R) :
    IsEdgeRestriction ((prod.lift g (graySimplexFibreMap X f x y h) ≫ prod.map k A) ≫ prod.snd)
      (φ ≫ f) := by
  rw [prod.lift_map, prod.lift_snd]
  exact hA.comp f h

private theorem IsEdgeRestriction.lift_map_snd_comp {A : legacyGraySimplexFibre X y ⟶ P}
    {c : P ⟶ (X.mappingSpace a b).toFunctor} (hA : IsEdgeRestriction (A ≫ c) φ)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (h : ∀ k, x (f.toOrderHom k) = y k)
    (g : legacyGraySimplexFibre X x ⟶ Q) (k : Q ⟶ R) :
    IsEdgeRestriction
      (((prod.lift g (graySimplexFibreMap X f x y h) ≫ prod.map k A) ≫ prod.snd) ≫ c) (φ ≫ f) := by
  rw [prod.lift_map, prod.lift_snd]
  exact hA.comp_assoc f h

private theorem IsEdgeRestriction.lift_map_id_fst
    {g : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor} (hg : IsEdgeRestriction g ψ)
    (g' : legacyGraySimplexFibre X x ⟶ Q) (A : Q ⟶ R) :
    IsEdgeRestriction ((prod.lift g g' ≫ prod.map (𝟙 _) A) ≫ prod.fst) ψ := by
  rw [prod.lift_map, prod.lift_fst, Category.comp_id]
  exact hg

private theorem IsEdgeRestriction.lift_map_id_snd
    {g : legacyGraySimplexFibre X x ⟶ (X.mappingSpace a b).toFunctor} (hg : IsEdgeRestriction g ψ)
    (g' : legacyGraySimplexFibre X x ⟶ Q) (A : Q ⟶ R) :
    IsEdgeRestriction ((prod.lift g' g ≫ prod.map A (𝟙 _)) ≫ prod.snd) ψ := by
  rw [prod.lift_map, prod.lift_snd, Category.comp_id]
  exact hg

end EdgeRestriction

theorem isEdgeRestriction_graySpineFibreTwoIso_fst (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    IsEdgeRestriction ((legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) ≫ prod.fst)
      (SimplexCategory.δ 2) := fun _ t => by
  rw [Category.assoc]
  exact mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_fst x t

theorem isEdgeRestriction_graySpineFibreTwoIso_snd (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    IsEdgeRestriction ((legacyGraySegalMap X x ≫ (legacyGraySpineFibreTwoIso X x).hom) ≫ prod.snd)
      (SimplexCategory.δ 0) := fun _ t => by
  rw [Category.assoc]
  exact mappingSpaceHomEquiv_graySegalMap_graySpineFibreTwoIso_snd x t

section Assoc

variable (X : DiagSet.{u}) (x : Fin 4 → X.Vertex)

private noncomputable def graySpineProductThreeIso :
    (∏ᶜ fun i : Fin 3 => (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor) ≅
      (X.mappingSpace (x 0) (x 1)).toFunctor ⨯
        ((X.mappingSpace (x 1) (x 2)).toFunctor ⨯ (X.mappingSpace (x 2) (x 3)).toFunctor) where
  hom := prod.lift (Pi.π _ 0) (prod.lift (Pi.π _ 1) (Pi.π _ 2))
  inv := Pi.lift fun i => match i with
    | 0 => prod.fst
    | 1 => prod.snd ≫ prod.fst
    | 2 => prod.snd ≫ prod.snd
  hom_inv_id := Pi.hom_ext _ _ fun i => by
    rw [Category.assoc, Pi.lift_π, Category.id_comp]
    fin_cases i
    · exact prod.lift_fst _ _
    · exact (prod.lift_snd_assoc _ _ _).trans (prod.lift_fst _ _)
    · exact (prod.lift_snd_assoc _ _ _).trans (prod.lift_snd _ _)
  inv_hom_id := prod.hom_ext (by rw [Category.assoc, prod.lift_fst, Pi.lift_π, Category.id_comp])
    (prod.hom_ext
      (by rw [Category.assoc, Category.assoc, prod.lift_snd_assoc, prod.lift_fst, Pi.lift_π,
        Category.id_comp])
      (by rw [Category.assoc, Category.assoc, prod.lift_snd_assoc, prod.lift_snd, Pi.lift_π,
        Category.id_comp]))

private theorem graySpineProductThreeIso_hom :
    (graySpineProductThreeIso X x).hom =
      prod.lift (Pi.π _ 0 : _ ⟶ (X.mappingSpace (x 0) (x 1)).toFunctor)
        (prod.lift (Pi.π _ 1 : _ ⟶ (X.mappingSpace (x 1) (x 2)).toFunctor)
          (Pi.π _ 2 : _ ⟶ (X.mappingSpace (x 2) (x 3)).toFunctor)) :=
  rfl

private noncomputable abbrev graySegalMapThree :
    legacyGraySimplexFibre X x ⟶ (X.mappingSpace (x 0) (x 1)).toFunctor ⨯
      ((X.mappingSpace (x 1) (x 2)).toFunctor ⨯ (X.mappingSpace (x 2) (x 3)).toFunctor) :=
  prod.lift (graySimplexEdge X x 0 1 (by decide))
    (prod.lift (graySimplexEdge X x 1 2 (by decide)) (graySimplexEdge X x 2 3 (by decide)))

private theorem rlp_monomorphisms_graySegalMapThree {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    (x : Fin 4 → X.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (graySegalMapThree X x) := by
  have e : graySegalMapThree X x = (legacyGraySegalMap X x ≫ (legacyGraySpineFibreIso X x).hom) ≫
      (graySpineProductThreeIso X x).hom := by
    refine prod.hom_ext ?_ (prod.hom_ext ?_ ?_)
    · rw [prod.lift_fst, Category.assoc, Category.assoc, graySpineProductThreeIso_hom,
        prod.lift_fst]
      exact (graySegalMap_graySpineFibreIso_hom_π X x 0).symm
    · rw [Category.assoc, prod.lift_snd_assoc, prod.lift_fst, Category.assoc, Category.assoc,
        Category.assoc, graySpineProductThreeIso_hom, prod.lift_snd_assoc, prod.lift_fst]
      exact (graySegalMap_graySpineFibreIso_hom_π X x 1).symm
    · rw [Category.assoc, prod.lift_snd_assoc, prod.lift_snd, Category.assoc, Category.assoc,
        Category.assoc, graySpineProductThreeIso_hom, prod.lift_snd_assoc, prod.lift_snd]
      exact (graySegalMap_graySpineFibreIso_hom_π X x 2).symm
  rw [e]
  exact (monomorphisms DiagSet.{u}).rlp.comp_mem _ _ (rlp_monomorphisms_graySpineFibreIso hX x)
    fun _ _ _ _ => inferInstance

private noncomputable abbrev grayFaceThreeRight :
    legacyGraySimplexFibre X x ⟶ legacyGraySimplexFibre X ![x 0, x 1, x 2] ⨯
      (X.mappingSpace (x 2) (x 3)).toFunctor :=
  prod.lift (graySimplexFibreMap X (SimplexCategory.δ 3) x ![x 0, x 1, x 2]
    (fun k => by fin_cases k <;> rfl)) (graySimplexEdge X x 2 3 (by decide))

private noncomputable abbrev grayFaceThreeLeft :
    legacyGraySimplexFibre X x ⟶ (X.mappingSpace (x 0) (x 1)).toFunctor ⨯
      legacyGraySimplexFibre X ![x 1, x 2, x 3] :=
  prod.lift (graySimplexEdge X x 0 1 (by decide))
    (graySimplexFibreMap X (SimplexCategory.δ 0) x ![x 1, x 2, x 3]
      (fun k => by fin_cases k <;> rfl))

private theorem graySegalMapThree_comp_associator_inv :
    graySegalMapThree X x ≫ (Limits.prod.associator _ _ _).inv =
      grayFaceThreeRight X x ≫ prod.map
        (legacyGraySegalMap X ![x 0, x 1, x 2] ≫ (legacyGraySpineFibreTwoIso X ![x 0, x 1, x
          2]).hom)
        (𝟙 (X.mappingSpace (x 2) (x 3)).toFunctor) := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_
  · rw [Category.assoc, Category.assoc, Limits.prod.associator_inv, prod.lift_fst_assoc,
      prod.lift_fst, prod.lift_fst]
    exact (isEdgeRestriction_graySimplexEdge X x 0 1 _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_fst X _).lift_map_fst_comp _ _ _ _) (by decide)
  · rw [Category.assoc, Category.assoc, Limits.prod.associator_inv, prod.lift_fst_assoc,
      prod.lift_snd, prod.lift_snd_assoc, prod.lift_fst]
    exact (isEdgeRestriction_graySimplexEdge X x 1 2 _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_snd X _).lift_map_fst_comp _ _ _ _) (by decide)
  · rw [Category.assoc, Limits.prod.associator_inv, prod.lift_snd, prod.lift_snd_assoc,
      prod.lift_snd]
    exact (isEdgeRestriction_graySimplexEdge X x 2 3 _).eq
      ((isEdgeRestriction_graySimplexEdge X x 2 3 _).lift_map_id_snd _ _)

private theorem graySegalMapThree_eq_grayFaceThreeLeft :
    graySegalMapThree X x = grayFaceThreeLeft X x ≫ prod.map
        (𝟙 (X.mappingSpace (x 0) (x 1)).toFunctor)
        (legacyGraySegalMap X ![x 1, x 2, x 3] ≫ (legacyGraySpineFibreTwoIso X ![x 1, x 2, x
          3]).hom) := by
  refine prod.hom_ext ?_ (prod.hom_ext ?_ ?_)
  · rw [prod.lift_fst]
    exact (isEdgeRestriction_graySimplexEdge X x 0 1 _).eq
      ((isEdgeRestriction_graySimplexEdge X x 0 1 _).lift_map_id_fst _ _)
  · rw [prod.lift_snd, prod.lift_fst]
    exact (isEdgeRestriction_graySimplexEdge X x 1 2 _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_fst X _).lift_map_snd_comp _ _ _ _) (by decide)
  · rw [prod.lift_snd, prod.lift_snd]
    exact (isEdgeRestriction_graySimplexEdge X x 2 3 _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_snd X _).lift_map_snd_comp _ _ _ _) (by decide)

private theorem grayFaceThreeRight_comp_grayLongEdge :
    grayFaceThreeRight X x ≫ prod.map (grayLongEdge X ![x 0, x 1, x 2])
        (𝟙 (X.mappingSpace (x 2) (x 3)).toFunctor) =
      graySimplexFibreMap X (SimplexCategory.δ 1) x ![x 0, x 2, x 3]
          (fun k => by fin_cases k <;> rfl) ≫
        legacyGraySegalMap X ![x 0, x 2, x 3] ≫ (legacyGraySpineFibreTwoIso X ![x 0, x 2, x
          3]).hom := by
  refine prod.hom_ext ?_ ?_
  · exact ((isEdgeRestriction_grayLongEdge X _).lift_map_fst _ _ _ _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_fst X _).comp_assoc _ _) (by decide)
  · exact ((isEdgeRestriction_graySimplexEdge X x 2 3 _).lift_map_id_snd _ _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_snd X _).comp_assoc _ _) (by decide)

private theorem grayFaceThreeLeft_comp_grayLongEdge :
    grayFaceThreeLeft X x ≫ prod.map (𝟙 (X.mappingSpace (x 0) (x 1)).toFunctor)
        (grayLongEdge X ![x 1, x 2, x 3]) =
      graySimplexFibreMap X (SimplexCategory.δ 2) x ![x 0, x 1, x 3]
          (fun k => by fin_cases k <;> rfl) ≫
        legacyGraySegalMap X ![x 0, x 1, x 3] ≫ (legacyGraySpineFibreTwoIso X ![x 0, x 1, x
          3]).hom := by
  refine prod.hom_ext ?_ ?_
  · exact ((isEdgeRestriction_graySimplexEdge X x 0 1 _).lift_map_id_fst _ _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_fst X _).comp_assoc _ _) (by decide)
  · exact ((isEdgeRestriction_grayLongEdge X _).lift_map_snd _ _ _ _).eq_of_eq
      ((isEdgeRestriction_graySpineFibreTwoIso_snd X _).comp_assoc _ _) (by decide)

private theorem grayFaceThree_comp_grayLongEdge :
    graySimplexFibreMap X (SimplexCategory.δ 1) x ![x 0, x 2, x 3]
        (fun k => by fin_cases k <;> rfl) ≫ grayLongEdge X ![x 0, x 2, x 3] =
      graySimplexFibreMap X (SimplexCategory.δ 2) x ![x 0, x 1, x 3]
        (fun k => by fin_cases k <;> rfl) ≫ grayLongEdge X ![x 0, x 1, x 3] :=
  ((isEdgeRestriction_grayLongEdge X _).comp _ _).eq_of_eq
    ((isEdgeRestriction_grayLongEdge X _).comp _ _) (by decide)

end Assoc

theorem grayComposition_assoc {H : Type v} [Category.{w} H]
    (L : DiagSet.Infty.{u} 0 ⥤ H) [L.IsLocalization (weakEquivalences (DiagSet.Infty.{u} 0))]
    {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) (x : Fin 4 → X.Vertex) :
    L.map ((DiagSet.toInfty 0).map
        (Limits.prod.associator (X.mappingSpace (x 0) (x 1)).toFunctor
          (X.mappingSpace (x 1) (x 2)).toFunctor (X.mappingSpace (x 2) (x 3)).toFunctor).inv) ≫
      grayCompositionWhiskerRight L hX ![x 0, x 1, x 2] (X.mappingSpace (x 2) (x 3)).toFunctor ≫
        grayComposition L hX ![x 0, x 2, x 3] =
    grayCompositionWhiskerLeft L hX (X.mappingSpace (x 0) (x 1)).toFunctor ![x 1, x 2, x 3] ≫
      grayComposition L hX ![x 0, x 1, x 3] := by
  have hs := weakEquivalence_toInfty_map_of_rlp_monomorphisms 0
    (rlp_monomorphisms_graySegalMapThree hX x)
  have : IsIso (L.map ((DiagSet.toInfty 0).map (graySegalMapThree X x))) :=
    Localization.inverts L (weakEquivalences _) _ ((weakEquivalence_iff _).1 hs)
  refine (cancel_epi (L.map ((DiagSet.toInfty 0).map (graySegalMapThree X x)))).1 ?_
  have hm : ∀ {A B C : DiagSet.{u}} (f : A ⟶ B) (g : B ⟶ C) {Z : H}
      (h : L.obj ((DiagSet.toInfty 0).obj C) ⟶ Z),
      L.map ((DiagSet.toInfty 0).map (f ≫ g)) ≫ h =
        L.map ((DiagSet.toInfty 0).map f) ≫ L.map ((DiagSet.toInfty 0).map g) ≫ h := by
    intro A B C f g Z h
    rw [Functor.map_comp, Functor.map_comp, Category.assoc]
  have hm' : ∀ {A B C : DiagSet.{u}} (f : A ⟶ B) (g : B ⟶ C),
      L.map ((DiagSet.toInfty 0).map f) ≫ L.map ((DiagSet.toInfty 0).map g) =
        L.map ((DiagSet.toInfty 0).map (f ≫ g)) := by
    intro A B C f g
    rw [Functor.map_comp, Functor.map_comp]
  refine (hm _ _ _).symm.trans ?_
  refine (congrArg (fun t => L.map ((DiagSet.toInfty 0).map t) ≫ _)
    (graySegalMapThree_comp_associator_inv X x)).trans ?_
  refine (hm _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (map_prodMap_graySpineFibreTwo_comp_grayCompositionWhiskerRight_assoc L hX _ _ _)).trans ?_
  refine (hm _ _ _).symm.trans ?_
  refine (congrArg (fun t => L.map ((DiagSet.toInfty 0).map t) ≫ _)
    (grayFaceThreeRight_comp_grayLongEdge X x)).trans ?_
  refine (hm _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (map_graySpineFibreTwo_comp_grayComposition L hX _)).trans ?_
  refine ((hm' _ _).trans ((congrArg (fun t => L.map ((DiagSet.toInfty 0).map t))
    (grayFaceThree_comp_grayLongEdge X x)).trans (hm' _ _).symm)).trans ?_
  refine Eq.symm ?_
  refine (congrArg (fun t => L.map ((DiagSet.toInfty 0).map t) ≫ _)
    (graySegalMapThree_eq_grayFaceThreeLeft X x)).trans ?_
  refine (hm _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (map_prodMap_graySpineFibreTwo_comp_grayCompositionWhiskerLeft_assoc L hX _ _ _)).trans ?_
  refine (hm _ _ _).symm.trans ?_
  refine (congrArg (fun t => L.map ((DiagSet.toInfty 0).map t) ≫ _)
    (grayFaceThreeLeft_comp_grayLongEdge X x)).trans ?_
  refine (hm _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (map_graySpineFibreTwo_comp_grayComposition L hX _)

end Atoms.Diagrammatic
