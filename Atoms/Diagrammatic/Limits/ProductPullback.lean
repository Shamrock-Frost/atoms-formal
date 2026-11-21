import Atoms.Diagrammatic.Limits.ConeRestrict
import Atoms.Diagrammatic.Limits.ConeHom

open CategoryTheory Limits Opposite Simplicial Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

@[reassoc]
theorem constDiagram_comp_grayHomRightPointIso_hom_app (X : DiagSet.{u}) :
    constDiagram (ball.{u} atomPoint) X ≫ grayHomRightPointIso.hom.app X = 𝟙 X := by
  rw [constDiagram, homEquiv_comp_grayHomRightPointIso_hom_app, IsIso.inv_hom_id]

@[reassoc]
theorem diagramPoint_comp_grayHomRightPointIso_hom_app (d : ball.{u} atomPoint ⟶ X) :
    diagramPoint d ≫ grayHomRightPointIso.hom.app X =
      isTerminalBallAtomPoint.from _ ≫ d := by
  rw [diagramPoint, homEquiv_comp_grayHomRightPointIso_hom_app, ← Category.assoc]
  exact congrArg (· ≫ d) (isTerminalBallAtomPoint.hom_ext _ _)

noncomputable def pairDiagram (x y : X.Vertex) : intervalBoundary.{u} ⟶ X :=
  coprod.desc (vertexHom x) (vertexHom y)

def IsProductCone (α : Bool) (x y : X.Vertex)
    (c : (coneObject α (pairDiagram x y)).Vertex) : Prop :=
  IsLimitCone α (pairDiagram x y) c

noncomputable def cornerShape (α : Bool) : DiagSet.{u} :=
  pushout (cond α intervalTarget intervalSource) (cond α intervalTarget intervalSource)

noncomputable def cornerDiagram (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g) :
    cornerShape.{u} α ⟶ X :=
  pushout.desc f g h

def IsPullbackCone (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g)
    (c : (coneObject α (cornerDiagram α f g h)).Vertex) : Prop :=
  IsLimitCone α (cornerDiagram α f g h) c

theorem isPullback_coneObject_pairDiagram (α : Bool) (x y : X.Vertex) :
    IsPullback (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inl (d := pairDiagram x y)
        (coprod.inl_desc _ _))
      (coneObjectRestrict α (K := intervalBoundary.{u}) coprod.inr (coprod.inr_desc _ _))
      (coneObjectπ α (vertexHom x)) (coneObjectπ α (vertexHom y)) :=
  isPullback_coneObjectRestrict_coprod α (vertexHom x) (vertexHom y)

theorem isPullback_coneObject_cornerDiagram (α : Bool) (f g : ball.{u} (atomSimplex 1) ⟶ X)
    (h : cond α intervalTarget intervalSource ≫ f = cond α intervalTarget intervalSource ≫ g) :
    IsPullback (coneObjectRestrict α (pushout.inl _ _) (d := cornerDiagram α f g h)
        (pushout.inl_desc f g h))
      (coneObjectRestrict α (pushout.inr _ _) (pushout.inr_desc f g h))
      (coneObjectRestrict α (cond α intervalTarget intervalSource) (d' := _ ≫ f) rfl)
      (coneObjectRestrict α (cond α intervalTarget intervalSource) h.symm) :=
  isPullback_coneObjectRestrict_of_eq α (IsPushout.of_hasPushout _ _) (pushout.inl_desc f g h)
    (pushout.inr_desc f g h) rfl h.symm

theorem isPullback_coneObject_vertexHom (α : Bool) (x : X.Vertex) :
    IsPullback (coneObjectι α (vertexHom x) ≫
        (grayHomRight (ball.{u} (atomSimplex 1))).map (grayHomRightPointIso.hom.app X))
      (coneObjectπ α (vertexHom x)) ((grayHomRestrict intervalBoundaryι).app X)
      (boundaryHom (cond α (𝟙 X) (isTerminalBallAtomPoint.from X ≫ vertexHom x))
        (cond α (isTerminalBallAtomPoint.from X ≫ vertexHom x) (𝟙 X))) := by
  have ht : isTerminalBallAtomPoint.from X ≫ isTerminalBallAtomPoint.from _ =
      isTerminalBallAtomPoint.from X :=
    isTerminalBallAtomPoint.hom_ext _ _
  refine (isPullback_coneObject α (vertexHom x)).of_iso (Iso.refl _)
    ((grayHomRight (ball.{u} (atomSimplex 1))).mapIso (grayHomRightPointIso.app X)) (Iso.refl _)
    ((grayHomRight intervalBoundary.{u}).mapIso (grayHomRightPointIso.app X)) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact ((grayHomRestrict intervalBoundaryι).naturality _).symm
  · rw [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Iso.app_hom, coneObjectBase,
      boundaryHom_comp]
    cases α <;> simp only [cond, constDiagram_comp_grayHomRightPointIso_hom_app, Category.assoc,
      diagramPoint_comp_grayHomRightPointIso_hom_app, reassoc_of% ht]

private theorem isLimitCone_map_iff_of_isIso (α : Bool) {K K' : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) {d : K ⟶ X} {d' : K' ⟶ X} (F : coneObject α d ⟶ coneObject α d')
    [IsIso F] (c : (coneObject α d).Vertex) :
    IsLimitCone α d' (DiagSet.Vertex.map F c) ↔ IsLimitCone α d c :=
  have : WeakEquivalence ((DiagSet.toInfty 1).map F) :=
    (weakEquivalence_iff _).2 ((weakEquivalences _).of_isIso _)
  DiagSet.hasContractibleHoms_map_iff (isInftyCategory_coneObject α d hX)
    (isInftyCategory_coneObject α d' hX) F α c

theorem isProductCone_swap_iff (α : Bool) (hX : IsInftyCategory 1 X)
    (x y : X.Vertex)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    IsProductCone α y x (DiagSet.Vertex.map (coneObjectRestrict α
      (coprod.braiding (ball.{u} atomPoint) (ball atomPoint)).hom
      (coprod.hom_ext ((coprod.inl_desc_assoc _ _ _).trans
          ((coprod.inr_desc _ _).trans (coprod.inl_desc _ _).symm))
        ((coprod.inr_desc_assoc _ _ _).trans
          ((coprod.inl_desc _ _).trans (coprod.inr_desc _ _).symm)))) c) ↔
    IsProductCone α x y c :=
  @isLimitCone_map_iff_of_isIso _ α _ _ hX _ _ _ (isIso_coneObjectRestrict α _ _) c

end Atoms.Diagrammatic
