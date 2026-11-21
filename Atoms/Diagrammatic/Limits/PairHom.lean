import Atoms.Diagrammatic.Limits.ProductPullback

open CategoryTheory Limits Opposite Simplicial Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {K K' X : DiagSet.{u}}

noncomputable def DiagSet.bipointMapOfEq {Y : DiagSet.{u}} (F : X ⟶ Y)
    {x y : X.Vertex} {x' y' : Y.Vertex}
    (hx : DiagSet.Vertex.map F x = x') (hy : DiagSet.Vertex.map F y = y') :
    X.bipoint x y ⟶ Y.bipoint x' y' :=
  Under.homMk F (coprod.hom_ext
    (by
      simp only [DiagSet.bipoint, Under.mk_hom, coprod.inl_desc_assoc, coprod.inl_desc]
      exact (vertexHom_comp x F).trans (congrArg vertexHom hx))
    (by
      simp only [DiagSet.bipoint, Under.mk_hom, coprod.inr_desc_assoc, coprod.inr_desc]
      exact (vertexHom_comp y F).trans (congrArg vertexHom hy)))

@[simp] theorem DiagSet.bipointMapOfEq_right {Y : DiagSet.{u}} (F : X ⟶ Y)
    {x y : X.Vertex} {x' y' : Y.Vertex}
    (hx : DiagSet.Vertex.map F x = x') (hy : DiagSet.Vertex.map F y = y') :
    (DiagSet.bipointMapOfEq F hx hy).right = F :=
  rfl

theorem coneObjectπ_coneObjectRestrict_apply (α : Bool) (k : K' ⟶ K) {d : K ⟶ X} {d' : K' ⟶ X}
    (h : k ≫ d = d') (v : (coneObject α d).Vertex) :
    DiagSet.Vertex.map (coneObjectπ α d')
        (DiagSet.Vertex.map (coneObjectRestrict α k h) v) =
      DiagSet.Vertex.map (coneObjectπ α d) v := by
  exact (DiagSet.Vertex.map_comp _ _ _).symm.trans
    (congrArg (fun F => v.map F) (coneObjectRestrict_π α k h))

@[simp]
theorem coneObjectπ_coneObjectRestrict_inl_apply (α : Bool) (x y : X.Vertex)
    (v : (coneObject α (pairDiagram x y)).Vertex) :
    DiagSet.Vertex.map (coneObjectπ α (vertexHom x))
        (DiagSet.Vertex.map (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inl
          (d := pairDiagram x y) (coprod.inl_desc _ _)) v) =
      DiagSet.Vertex.map (coneObjectπ α (pairDiagram x y)) v :=
  coneObjectπ_coneObjectRestrict_apply α _ _ v

@[simp]
theorem coneObjectπ_coneObjectRestrict_inr_apply (α : Bool) (x y : X.Vertex)
    (v : (coneObject α (pairDiagram x y)).Vertex) :
    DiagSet.Vertex.map (coneObjectπ α (vertexHom y))
        (DiagSet.Vertex.map (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inr
          (d := pairDiagram x y) (coprod.inr_desc _ _)) v) =
      DiagSet.Vertex.map (coneObjectπ α (pairDiagram x y)) v :=
  coneObjectπ_coneObjectRestrict_apply α _ _ v

theorem isPullback_bipointedHom_coneObject_pairDiagram (α : Bool)
    (x y : X.Vertex)
    (v w : (coneObject α (pairDiagram x y)).Vertex) :
    IsPullback
      (bipointedHom.map (DiagSet.bipointMap (coneObjectRestrict α (K := intervalBoundary.{u})
        coprod.inl (d := pairDiagram x y) (coprod.inl_desc _ _)) v w))
      (bipointedHom.map (DiagSet.bipointMap (coneObjectRestrict α (K := intervalBoundary.{u})
        coprod.inr (d := pairDiagram x y) (coprod.inr_desc _ _)) v w))
      (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α (vertexHom x)) _ _))
      (bipointedHom.map
        (DiagSet.bipointMapOfEq (coneObjectπ α (vertexHom y)) (by simp) (by simp))) :=
  isPullback_bipointedHom_map (Under.UnderMorphism.ext (isPullback_coneObject_pairDiagram α x y).w)
    (isPullback_coneObject_pairDiagram α x y)

noncomputable def pairHomFibreProduct (α : Bool) (x y : X.Vertex)
    (v w : (coneObject α (pairDiagram x y)).Vertex) : DiagSet.{u} :=
  pullback
    (bipointedHom.map (DiagSet.bipointMap (coneObjectπ α (vertexHom x))
      (DiagSet.Vertex.map (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inl
        (d := pairDiagram x y) (coprod.inl_desc _ _)) v)
      (DiagSet.Vertex.map (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inl
        (d := pairDiagram x y) (coprod.inl_desc _ _)) w)))
    (bipointedHom.map
      (DiagSet.bipointMapOfEq (coneObjectπ α (vertexHom y))
        ((coneObjectπ_coneObjectRestrict_inr_apply α x y v).trans
          (coneObjectπ_coneObjectRestrict_inl_apply α x y v).symm)
        ((coneObjectπ_coneObjectRestrict_inr_apply α x y w).trans
          (coneObjectπ_coneObjectRestrict_inl_apply α x y w).symm)))

theorem isProductCone_iff_isContractible_pairHomFibreProduct (α : Bool)
    (x y : X.Vertex)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    IsProductCone α x y c ↔
      ∀ v, (pairHomFibreProduct α x y (cond α v c) (cond α c v)).IsContractible :=
  forall_congr' fun v =>
    let e := (isPullback_bipointedHom_coneObject_pairDiagram α x y (cond α v c)
      (cond α c v)).isoPullback
    @DiagSet.isContractible_iff_of_weakEquivalence _ _ e.hom
      ((weakEquivalence_iff _).2
        ((weakEquivalences _).of_isIso (f := (DiagSet.toInfty 0).map e.hom)))

end Atoms.Diagrammatic
