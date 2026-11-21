import Atoms.Diagrammatic.Fibration.SliceFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {E S : DiagSet.{u}} {x y : E.Vertex}

theorem DiagSet.edgeEquivSSet_edge_eq_iff {X : DiagSet.{u}} {x y x' y' : X.Vertex}
    (e : X.Edge x y) (e' : X.Edge x' y') :
    (X.edgeEquivSSet e).edge = (X.edgeEquivSSet e').edge ↔ e.cell = e'.cell := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [DiagSet.edgeEquivSSet_edge, DiagSet.edgeEquivSSet_edge, h]⟩
  have h' := congrArg (X.map atomSimplexOneIsoGlobe.inv.op) h
  rwa [DiagSet.edgeEquivSSet_edge, DiagSet.edgeEquivSSet_edge, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply,
    Functor.map_id_apply] at h'

theorem DiagSet.exists_edgeEquivSSet_edge_eq {X : DiagSet.{u}}
    (s : (DiagSet.toSSet.obj X) _⦋1⦌) :
    ∃ (x y : X.Vertex) (e : X.Edge x y), (X.edgeEquivSSet e).edge = s :=
  ⟨X.vertexEquivSSet.symm ((DiagSet.toSSet.obj X).δ 1 s),
    X.vertexEquivSSet.symm ((DiagSet.toSSet.obj X).δ 0 s),
    X.edgeEquivSSet.symm (SSet.Edge.mk s (Equiv.apply_symm_apply _ _).symm
      (Equiv.apply_symm_apply _ _).symm),
    congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)⟩

theorem DiagSet.isCartesianEdge_congr (p : E ⟶ S) {x' y' : E.Vertex} {e : E.Edge x y}
    {e' : E.Edge x' y'} (h : e.cell = e'.cell) :
    DiagSet.IsCartesianEdge p e ↔ DiagSet.IsCartesianEdge p e' := by
  obtain rfl : x = x' := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : y = y' := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := DiagSet.Edge.ext h
  rfl

class DiagSet.IsCartesianFibration (p : E ⟶ S) : Prop where
  fibration : Fibration ((DiagSet.toInfty 1).map p)
  exists_isCartesianEdge : ∀ (y : E.Vertex) {b : S.Vertex} (f : S.Edge b (y.map p)),
    ∃ (x : E.Vertex) (e : E.Edge x y), (e.map p).cell = f.cell ∧ DiagSet.IsCartesianEdge p e

instance DiagSet.IsCartesianFibration.fibration_toInfty_one_map (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] : Fibration ((DiagSet.toInfty 1).map p) :=
  DiagSet.IsCartesianFibration.fibration

def DiagSet.IsCartesianFunctor {F : DiagSet.{u}} (p : E ⟶ S) (q : F ⟶ S) (f : E ⟶ F) : Prop :=
  f ≫ q = p ∧ ∀ ⦃x y : E.Vertex⦄ (e : E.Edge x y),
    DiagSet.IsCartesianEdge p e → DiagSet.IsCartesianEdge q (e.map f)

theorem DiagSet.yonedaEquiv_symm_edgeEquivSSet_map {X Y : DiagSet.{u}} {x y : X.Vertex}
    (e : X.Edge x y) (f : X ⟶ Y) :
    SSet.yonedaEquiv.symm (Y.edgeEquivSSet (e.map f)).edge =
      SSet.yonedaEquiv.symm (X.edgeEquivSSet e).edge ≫ DiagSet.toSSet.map f :=
  (congrArg (fun t : SSet.Edge _ _ ↦ SSet.yonedaEquiv.symm t.edge)
    (DiagSet.edgeEquivSSet_map e f)).trans
      (SSet.yonedaEquiv_symm_comp (X.edgeEquivSSet e).edge (DiagSet.toSSet.map f)).symm

theorem DiagSet.isCartesianFibration_iff_toSSet (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsCartesianFibration p ↔ SSet.IsCartesianFibration (DiagSet.toSSet.map p) := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ ⟨inferInstance, fun y b f ↦ ?_⟩⟩
  · have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
      innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
    refine ⟨fun y f hf ↦ ?_⟩
    obtain ⟨s, rfl⟩ := SSet.yonedaEquiv.symm.surjective f
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm] at hf
    let f₀ : S.Edge (S.vertexEquivSSet.symm ((DiagSet.toSSet.obj S).δ 1 s))
        (DiagSet.Vertex.map p (E.vertexEquivSSet.symm y)) :=
      S.edgeEquivSSet.symm (SSet.Edge.mk s (Equiv.apply_symm_apply _ _).symm
        (SSet.yonedaEquiv.symm.injective hf))
    have hf₀ : (S.edgeEquivSSet f₀).edge = s := congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)
    obtain ⟨x, e, hcell, he⟩ := hp.exists_isCartesianEdge (E.vertexEquivSSet.symm y) f₀
    refine ⟨SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge, ?_, ?_,
      (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration p e).1 he⟩
    · rw [← DiagSet.yonedaEquiv_symm_edgeEquivSSet_map,
        (DiagSet.edgeEquivSSet_edge_eq_iff (e.map p) f₀).2 hcell, hf₀]
    · rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg _ (E.edgeEquivSSet e).tgt_eq
  · obtain ⟨g', hg'p, hg'y, hg'⟩ := hp.exists_isCartesianEdge (E.vertexEquivSSet y)
      (SSet.yonedaEquiv.symm (S.edgeEquivSSet f).edge) (by
        rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
        exact congrArg _ (S.edgeEquivSSet f).tgt_eq)
    obtain ⟨t, rfl⟩ := SSet.yonedaEquiv.symm.surjective g'
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm] at hg'y
    let e : E.Edge (E.vertexEquivSSet.symm ((DiagSet.toSSet.obj E).δ 1 t)) y :=
      E.edgeEquivSSet.symm (SSet.Edge.mk t (Equiv.apply_symm_apply _ _).symm
        (SSet.yonedaEquiv.symm.injective hg'y))
    have he : (E.edgeEquivSSet e).edge = t := congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)
    refine ⟨_, e, (DiagSet.edgeEquivSSet_edge_eq_iff (e.map p) f).1 ?_,
      (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration p e).2 (by rwa [he])⟩
    apply SSet.yonedaEquiv.symm.injective
    rw [DiagSet.yonedaEquiv_symm_edgeEquivSSet_map, he, hg'p]

theorem DiagSet.isCartesianFunctor_iff_toSSet {F : DiagSet.{u}} (p : E ⟶ S) (q : F ⟶ S)
    (f : E ⟶ F) [Fibration ((DiagSet.toInfty 1).map p)] [Fibration ((DiagSet.toInfty 1).map q)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsCartesianFunctor p q f ↔ f ≫ q = p ∧ ∀ g : Δ[1] ⟶ DiagSet.toSSet.obj E,
      SSet.IsCartesianEdge (DiagSet.toSSet.map p) g →
        SSet.IsCartesianEdge (DiagSet.toSSet.map q) (g ≫ DiagSet.toSSet.map f) := by
  refine and_congr_right fun _ ↦ ⟨fun h g hg ↦ ?_, fun h x y e he ↦ ?_⟩
  · obtain ⟨x, y, e, he⟩ := DiagSet.exists_edgeEquivSSet_edge_eq (SSet.yonedaEquiv g)
    obtain rfl : SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge = g := by
      rw [he, Equiv.symm_apply_apply]
    rw [← DiagSet.yonedaEquiv_symm_edgeEquivSSet_map]
    exact (h e ((DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration p e).2
      hg)).isCartesianEdge_toSSet
  · refine (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration q (e.map f)).2 ?_
    rw [DiagSet.yonedaEquiv_symm_edgeEquivSSet_map]
    exact h _ he.isCartesianEdge_toSSet

instance DiagSet.isCartesianFibration_of_isIso (p : E ⟶ S) [IsIso p] :
    DiagSet.IsCartesianFibration p where
  fibration := inferInstance
  exists_isCartesianEdge y b f := by
    have hy : (y.map p).map (inv p) = y := by
      rw [← DiagSet.Vertex.map_comp, IsIso.hom_inv_id, DiagSet.Vertex.map_id]
    refine ⟨b.map (inv p), ⟨(f.map (inv p)).cell, (f.map (inv p)).src_eq,
      (f.map (inv p)).tgt_eq.trans hy⟩,
      congrArg (fun k : S ⟶ S ↦ k.app _ f.cell) (IsIso.inv_hom_id p),
      DiagSet.isCartesianEdge_of_isIso p _⟩

theorem DiagSet.IsCartesianFibration.of_isPullback {E' S' : DiagSet.{u}} {p : E ⟶ S}
    {p' : E' ⟶ S'} {q : E' ⟶ E} {g : S' ⟶ S} (h : IsPullback q p' p g)
    [DiagSet.IsCartesianFibration p] : DiagSet.IsCartesianFibration p' where
  fibration := (fibration_toInfty_one_map_iff _).2
    (MorphismProperty.of_isPullback h ((fibration_toInfty_one_map_iff p).1 inferInstance))
  exists_isCartesianEdge y' b' f := by
    have hy : (y'.map p').map g = (y'.map q).map p := congrArg (fun k ↦ y'.map k) h.w.symm
    obtain ⟨x, e, hcell, he⟩ := DiagSet.IsCartesianFibration.exists_isCartesianEdge (p := p)
      (y'.map q) ⟨(f.map g).cell, (f.map g).src_eq, (f.map g).tgt_eq.trans hy⟩
    have hw : uliftYonedaEquiv.symm e.cell ≫ p = uliftYonedaEquiv.symm f.cell ≫ g := by
      rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
      exact congrArg _ hcell
    let c : diagram E' (atomGlobe 1) := uliftYonedaEquiv (h.lift _ _ hw)
    have hcq : q.app _ c = e.cell := by
      rw [← uliftYonedaEquiv_comp, h.lift_fst, Equiv.apply_symm_apply]
    have hcp : p'.app _ c = f.cell := by
      rw [← uliftYonedaEquiv_comp, h.lift_snd, Equiv.apply_symm_apply]
    have hext (v v' : E'.Vertex) (h₁ : v.map q = v'.map q) (h₂ : v.map p' = v'.map p') :
        v = v' := by
      apply uliftYonedaEquiv.symm.injective
      refine h.hom_ext ?_ ?_
      · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
        exact congrArg _ h₁
      · rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp]
        exact congrArg _ h₂
    let e' : E'.Edge (E'.map (atomGlobeVertex false).op c) y' :=
      { cell := c
        src_eq := rfl
        tgt_eq := hext _ _
          ((NatTrans.naturality_apply q _ c).trans ((congrArg _ hcq).trans e.tgt_eq))
          ((NatTrans.naturality_apply p' _ c).trans ((congrArg _ hcp).trans f.tgt_eq)) }
    exact ⟨_, e', hcp, DiagSet.IsCartesianEdge.of_isPullback h
      ((DiagSet.isCartesianEdge_congr p (e := e'.map q) (e' := e) hcq).2 he)⟩

instance DiagSet.IsCartesianFibration.comp {T : DiagSet.{u}} (p : E ⟶ S) (q : S ⟶ T)
    [DiagSet.IsCartesianFibration p] [DiagSet.IsCartesianFibration q] :
    DiagSet.IsCartesianFibration (p ≫ q) where
  fibration := by
    rw [Functor.map_comp]
    infer_instance
  exists_isCartesianEdge y b f := by
    obtain ⟨z, g, hgcell, hg⟩ := DiagSet.IsCartesianFibration.exists_isCartesianEdge (p := q)
      (y.map p) f
    obtain ⟨x, e, hecell, he⟩ := DiagSet.IsCartesianFibration.exists_isCartesianEdge (p := p) y g
    refine ⟨x, e, ?_, he.comp ((DiagSet.isCartesianEdge_congr q hecell).2 hg)⟩
    exact (congrArg (q.app _) hecell).trans hgcell

end Atoms.Diagrammatic
