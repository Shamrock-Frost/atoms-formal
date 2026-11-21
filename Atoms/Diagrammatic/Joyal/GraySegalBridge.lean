import Atoms.Diagrammatic.Joyal.Quillen
import Atoms.Diagrammatic.Joyal.RelativeCylinder
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Spine
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open Atoms.Homotopical Atoms.Shape Simplicial

universe u

namespace Atoms.Diagrammatic

noncomputable abbrev graySimplexVertices (p : ℕ) : DiagSet.{u} :=
  ∐ fun _ : Fin (p + 1) => ball.{u} atomPoint

noncomputable def graySimplexVerticesHomEquiv (p : ℕ) (X : DiagSet.{u}) :
    (graySimplexVertices.{u} p ⟶ X) ≃ (Fin (p + 1) → X.Vertex) where
  toFun φ k := uliftYonedaEquiv (X := atomPoint) (F := X)
    (Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ φ)
  invFun x := Sigma.desc fun k => vertexHom (x k)
  left_inv φ := Sigma.hom_ext _ _ fun k => by
    rw [Sigma.ι_desc]
    exact uliftYonedaEquiv.symm_apply_apply _
  right_inv x := funext fun k => by
    dsimp only
    rw [Sigma.ι_desc]
    exact uliftYonedaEquiv_vertexHom (x k)

@[reassoc]
theorem ι_graySimplexVerticesHomEquiv_symm (p : ℕ) {X : DiagSet.{u}}
    (x : Fin (p + 1) → X.Vertex) (k : Fin (p + 1)) :
    Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫
      (graySimplexVerticesHomEquiv p X).symm x = vertexHom (x k) :=
  Sigma.ι_desc (fun k => vertexHom (x k)) k

private noncomputable def spineVertex (p : ℕ) (k : Fin (p + 1)) :
    (SSet.spineSubcomplex.{u} p : SSet.{u}) _⦋0⦌ :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm k, by
    rw [SSet.mem_spineSubcomplex_iff]
    intro j
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    omega⟩

private noncomputable def toDiagSetSpineVertex (p : ℕ) (k : Fin (p + 1)) :
    (SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet.{u})).Vertex :=
  (sSetDiagSetAdj.unit.app _).app _ (spineVertex p k)

noncomputable def legacyGraySpineVerticesι (p : ℕ) :
    graySimplexVertices.{u} p ⟶ SSet.toDiagSet.obj (SSet.spineSubcomplex.{u} p : SSet) :=
  (graySimplexVerticesHomEquiv p _).symm (toDiagSetSpineVertex p)

noncomputable def legacyGraySimplexVerticesι (p : ℕ) :
    graySimplexVertices.{u} p ⟶ SSet.toDiagSet.obj Δ[p] :=
  legacyGraySpineVerticesι p ≫ SSet.toDiagSet.map (SSet.spineSubcomplex p).ι

private theorem toDiagSetObjStdSimplexIso_hom_app_vertex (p : ℕ) (k : Fin (p + 1)) :
    (toDiagSetObjStdSimplexIso.{u} p).hom.app (op (atomSimplex 0))
        ((toDiagSetSpineVertex p k).map (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι)) =
      ULift.up (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom) := by
  have hu := ConcreteCategory.congr_hom (NatTrans.congr_app
    (sSetDiagSetAdj.unit.naturality (SSet.spineSubcomplex.{u} p).ι) (op ⦋0⦌)) (spineVertex p k)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.id_map] at hu
  refine (congrArg _ hu.symm).trans ?_
  exact toDiagSetObjStdSimplexIso_hom_app_unit (SimplexCategory.const ⦋0⦌ ⦋p⦌ k)

theorem ι_graySimplexVerticesι_comp_hom (p : ℕ) (k : Fin (p + 1)) :
    Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) k ≫ legacyGraySimplexVerticesι p ≫
        (toDiagSetObjStdSimplexIso.{u} p).hom =
      uliftYoneda.{u}.map (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom) := by
  rw [legacyGraySimplexVerticesι, legacyGraySpineVerticesι, Category.assoc,
    ι_graySimplexVerticesHomEquiv_symm_assoc,
    vertexHom_comp_assoc, vertexHom_comp]
  refine (congrArg vertexHom (toDiagSetObjStdSimplexIso_hom_app_vertex p k)).trans ?_
  exact uliftYonedaEquiv.symm_apply_eq.2 (uliftYonedaEquiv_uliftYoneda_map _).symm

instance mono_graySimplexVerticesι (p : ℕ) : Mono (legacyGraySimplexVerticesι.{u} p) := by
  suffices Mono (legacyGraySimplexVerticesι.{u} p ≫ (toDiagSetObjStdSimplexIso.{u} p).hom) from
    mono_of_mono _ (toDiagSetObjStdSimplexIso p).hom
  have e : legacyGraySimplexVerticesι.{u} p ≫ (toDiagSetObjStdSimplexIso.{u} p).hom =
      Sigma.desc fun k =>
        uliftYoneda.{u}.map (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom) :=
    Sigma.hom_ext _ _ fun k => (ι_graySimplexVerticesι_comp_hom p k).trans
      (Sigma.ι_desc (fun k =>
        uliftYoneda.{u}.map (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom)) k).symm
  rw [e]
  have (k : Fin (p + 1)) : Mono (uliftYoneda.{u}.map
      (simplexHom (SimplexCategory.const ⦋0⦌ ⦋p⦌ k).toOrderHom)) :=
    isTerminalBallAtomPoint.mono_from _
  refine FunctorToTypes.mono_sigmaDesc_of_disjoint _ fun U k l t t' h => ?_
  have h' := congrArg (fun c : ULift (U.unop ⟶ atomSimplex p) =>
    atomSimplexVertices p (c.down U.unop.top)) h
  simp only [uliftYoneda_map_app, TypeCat.ofHom_apply, ConcreteCategory.comp_apply] at h'
  rw [eq_top_atomSimplex_zero (ConcreteCategory.hom t.down _),
    eq_top_atomSimplex_zero (ConcreteCategory.hom t'.down _), atomSimplexVertices_simplexHom,
    atomSimplexVertices_simplexHom, atomSimplexVertices_top] at h'
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (h' ▸ Finset.mem_image_of_mem _ (Finset.mem_univ 0))
  exact hj.symm

theorem exists_graySimplexVerticesι_app_eq (p : ℕ)
    (a : (SSet.toDiagSet.obj (Δ[p] : SSet.{u})).Vertex) :
    ∃ v : (graySimplexVertices.{u} p).Vertex, v.map (legacyGraySimplexVerticesι p) = a := by
  let e := toDiagSetObjStdSimplexIso.{u} p
  let σ : ⦋0⦌ ⟶ ⦋p⦌ := simplexFunctor.preimage (e.hom.app (op (atomSimplex 0)) a).down
  have hσ : σ = SimplexCategory.const ⦋0⦌ ⦋p⦌ (σ.toOrderHom 0) := by
    ext j
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    rfl
  let pt : (ball.{u} atomPoint).obj (op (atomSimplex 0)) := ⟨𝟙 _⟩
  refine ⟨(Sigma.ι (fun _ : Fin (p + 1) => ball.{u} atomPoint) (σ.toOrderHom 0)).app _
    pt, (mono_iff_injective (e.hom.app (op (atomSimplex 0)))).1 inferInstance ?_⟩
  have h := congrArg (fun φ : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex p) =>
    φ.app (op (atomSimplex 0)) pt) (ι_graySimplexVerticesι_comp_hom p (σ.toOrderHom 0))
  refine h.trans (ULift.ext _ _ ?_)
  refine (Category.id_comp (obj := Atom) _).trans ?_
  rw [← hσ]
  exact simplexFunctor.map_preimage _

noncomputable abbrev legacyGraySimplexFibre (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : DiagSet.{u} :=
  relativeMappingSpace (legacyGraySimplexVerticesι p) ((graySimplexVerticesHomEquiv p X).symm x)

noncomputable abbrev legacyGraySpineFibre (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : DiagSet.{u} :=
  relativeMappingSpace (legacyGraySpineVerticesι p) ((graySimplexVerticesHomEquiv p X).symm x)

theorem isInftyCategory_zero_legacyGraySimplexFibre {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    IsInftyCategory 0 (legacyGraySimplexFibre X x) :=
  isInftyCategory_zero_relativeMappingSpace _ (exists_graySimplexVerticesι_app_eq p) _ hX

noncomputable def legacyGraySegalMap (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) : legacyGraySimplexFibre X x ⟶ legacyGraySpineFibre X x :=
  relativeMappingSpaceRestrict (legacyGraySpineVerticesι p)
    (SSet.toDiagSet.map (SSet.spineSubcomplex p).ι) _

open SSet.modelCategoryJoyal in
theorem rlp_monomorphisms_legacyGraySegalMap {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (legacyGraySegalMap X x) := by
  have : Mono (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι) := SSet.toDiagSet.map_mono _
  have : WeakEquivalence ((DiagSet.toInfty 1).map
      (SSet.toDiagSet.map (SSet.spineSubcomplex.{u} p).ι)) :=
    (weakEquivalence_iff _).2 (trivialCofibration_map_spineSubcomplex_ι
      DiagSet.Infty.sSetDiagSetAdj isQuillen_sSetDiagSetAdj p).2
  exact rlp_monomorphisms_relativeMappingSpaceRestrict _ _ _ hX

end Atoms.Diagrammatic
