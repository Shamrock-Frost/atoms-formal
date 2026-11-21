import Atoms.Diagrammatic.SimplicialAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Simplicial Atoms.Shape Opposite

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}}

abbrev DiagSet.Vertex (X : DiagSet.{u}) : Type u := diagram X atomPoint

def DiagSet.Vertex.map (f : X ⟶ Y) (x : X.Vertex) : Y.Vertex := f.app _ x

@[simp] theorem DiagSet.Vertex.map_id (x : X.Vertex) : x.map (𝟙 X) = x := rfl

@[simp] theorem DiagSet.Vertex.map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.Vertex) :
    x.map (f ≫ g) = (x.map f).map g :=
  rfl

@[ext]
structure DiagSet.Edge (X : DiagSet.{u}) (x y : X.Vertex) where
  cell : diagram X (atomGlobe 1)
  src_eq : X.map (atomGlobeVertex false).op cell = x
  tgt_eq : X.map (atomGlobeVertex true).op cell = y

namespace DiagSet.Edge

variable {x y : X.Vertex}

def map (e : X.Edge x y) (f : X ⟶ Y) : Y.Edge (x.map f) (y.map f) where
  cell := f.app _ e.cell
  src_eq := (NatTrans.naturality_apply f _ e.cell).symm.trans (congrArg (f.app _) e.src_eq)
  tgt_eq := (NatTrans.naturality_apply f _ e.cell).symm.trans (congrArg (f.app _) e.tgt_eq)

@[simp] theorem map_cell (e : X.Edge x y) (f : X ⟶ Y) : (e.map f).cell = f.app _ e.cell := rfl

def id (x : X.Vertex) : X.Edge x x where
  cell := X.map (toAtomPoint (atomGlobe 1)).op x
  src_eq := by
    rw [← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim (atomGlobeVertex false ≫ toAtomPoint (atomGlobe 1)) (𝟙 _), op_id,
      Functor.map_id_apply]
  tgt_eq := by
    rw [← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim (atomGlobeVertex true ≫ toAtomPoint (atomGlobe 1)) (𝟙 _), op_id,
      Functor.map_id_apply]

@[simp] theorem id_cell (x : X.Vertex) :
    (Edge.id x).cell = X.map (toAtomPoint (atomGlobe 1)).op x :=
  rfl

@[simp] theorem map_id (x : X.Vertex) (f : X ⟶ Y) : (Edge.id x).map f = Edge.id (x.map f) :=
  Edge.ext (by
    rw [map_cell, id_cell, id_cell]
    exact NatTrans.naturality_apply f _ x)

end DiagSet.Edge

def DiagSet.vertexEquivSSet (X : DiagSet.{u}) : X.Vertex ≃ (DiagSet.toSSet.obj X) _⦋0⦌ :=
  Equiv.refl _

theorem DiagSet.vertexEquivSSet_map (f : X ⟶ Y) (x : X.Vertex) :
    Y.vertexEquivSSet (x.map f) = (DiagSet.toSSet.map f).app _ (X.vertexEquivSSet x) :=
  rfl

private theorem simplexHom_δ_eq (ε : Bool) :
    simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom =
      atomGlobeVertex ε ≫ atomSimplexOneIsoGlobe.inv :=
  (Iso.eq_comp_inv _).2 (simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom ε)

private theorem δ_map_atomSimplexOneIsoGlobe (ε : Bool) (c : diagram X (atomGlobe 1)) :
    X.map (simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom).op
        (X.map atomSimplexOneIsoGlobe.hom.op c) =
      X.map (atomGlobeVertex ε).op c := by
  rw [← Functor.map_comp_apply, ← op_comp, simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom ε]
  rfl

private theorem map_atomGlobeVertex_atomSimplexOneIsoGlobe (ε : Bool)
    (s : diagram X (atomSimplex 1)) :
    X.map (atomGlobeVertex ε).op (X.map atomSimplexOneIsoGlobe.inv.op s) =
      X.map (simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom).op s := by
  rw [← Functor.map_comp_apply, ← op_comp, ← simplexHom_δ_eq]
  rfl

private theorem map_hom_map_inv_atomSimplexOneIsoGlobe (s : diagram X (atomSimplex 1)) :
    X.map atomSimplexOneIsoGlobe.hom.op (X.map atomSimplexOneIsoGlobe.inv.op s) = s :=
  (X.map_comp_apply _ _ s).symm.trans <| by
    rw [← op_comp, Iso.hom_inv_id, op_id, X.map_id_apply]

noncomputable def DiagSet.edgeEquivSSet {x y : X.Vertex} :
    X.Edge x y ≃ SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y) where
  toFun e := SSet.Edge.mk (X.map atomSimplexOneIsoGlobe.hom.op e.cell)
    ((δ_map_atomSimplexOneIsoGlobe false e.cell).trans e.src_eq)
    ((δ_map_atomSimplexOneIsoGlobe true e.cell).trans e.tgt_eq)
  invFun s :=
    { cell := X.map atomSimplexOneIsoGlobe.inv.op s.edge
      src_eq := (map_atomGlobeVertex_atomSimplexOneIsoGlobe false s.edge).trans s.src_eq
      tgt_eq := (map_atomGlobeVertex_atomSimplexOneIsoGlobe true s.edge).trans s.tgt_eq }
  left_inv e := DiagSet.Edge.ext <| (X.map_comp_apply _ _ e.cell).symm.trans <| by
    rw [← op_comp, Iso.inv_hom_id, op_id, X.map_id_apply]
  right_inv s := SSet.Edge.ext <| map_hom_map_inv_atomSimplexOneIsoGlobe s.edge

@[simp] theorem DiagSet.edgeEquivSSet_edge {x y : X.Vertex} (e : X.Edge x y) :
    (X.edgeEquivSSet e).edge = X.map atomSimplexOneIsoGlobe.hom.op e.cell :=
  rfl

theorem DiagSet.edgeEquivSSet_map {x y : X.Vertex} (e : X.Edge x y) (f : X ⟶ Y) :
    Y.edgeEquivSSet (e.map f) = (X.edgeEquivSSet e).map (DiagSet.toSSet.map f) :=
  SSet.Edge.ext (NatTrans.naturality_apply f _ e.cell).symm

@[simp] theorem DiagSet.edgeEquivSSet_id (x : X.Vertex) :
    X.edgeEquivSSet (DiagSet.Edge.id x) = SSet.Edge.id (X.vertexEquivSSet x) :=
  SSet.Edge.ext ((X.map_comp_apply _ _ x).symm.trans
    (congrArg (fun f : atomSimplex 1 ⟶ atomPoint ↦ X.map f.op x) (Subsingleton.elim _ _)))

@[simp] theorem DiagSet.edgeEquivSSet_symm_id (x : X.Vertex) :
    X.edgeEquivSSet.symm (SSet.Edge.id (X.vertexEquivSSet x)) = DiagSet.Edge.id x :=
  (Equiv.symm_apply_eq _).2 (DiagSet.edgeEquivSSet_id x).symm

theorem DiagSet.edgeEquivSSet_symm_map {x y : X.Vertex}
    (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) (f : X ⟶ Y) :
    (Y.edgeEquivSSet (x := x.map f) (y := y.map f)).symm (e.map (DiagSet.toSSet.map f)) =
      (X.edgeEquivSSet.symm e).map f :=
  (Equiv.symm_apply_eq _).2 ((DiagSet.edgeEquivSSet_map _ f).trans
    (congrArg (·.map (DiagSet.toSSet.map f)) (Equiv.apply_symm_apply _ e))).symm

noncomputable def vertexHom (x : X.Vertex) : ball.{u} atomPoint ⟶ X :=
  (uliftYonedaEquiv (X := atomPoint) (F := X)).symm x

@[simp]
theorem uliftYonedaEquiv_vertexHom (x : X.Vertex) : uliftYonedaEquiv (vertexHom x) = x :=
  Equiv.apply_symm_apply _ _

@[reassoc]
theorem vertexHom_comp (x : X.Vertex) (f : X ⟶ Y) : vertexHom x ≫ f = vertexHom (x.map f) :=
  uliftYonedaEquiv_symm_comp (C := Atom) (X := op atomPoint) x f

noncomputable def toSSetPoint : Δ[0] ⟶ DiagSet.toSSet.obj (ball.{u} atomPoint) :=
  toSSetObjBallPointIso.inv

@[reassoc]
theorem toSSetPoint_comp_toSSet_map_vertexHom {Y : DiagSet.{u}} (y : Y.Vertex) :
    toSSetPoint ≫ DiagSet.toSSet.map (vertexHom y) =
      SSet.yonedaEquiv.symm (Y.vertexEquivSSet y) := by
  have h : toSSetPoint.{u} = SSet.yonedaEquiv.symm
      ((ball.{u} atomPoint).vertexEquivSSet (uliftYonedaEquiv (𝟙 _))) :=
    (isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _).hom_ext _ _
  rw [h]
  exact (SSet.yonedaEquiv_symm_comp _ _).trans (congrArg SSet.yonedaEquiv.symm
    ((uliftYonedaEquiv_comp _ _).symm.trans ((congrArg uliftYonedaEquiv (Category.id_comp _)).trans
      (uliftYonedaEquiv_vertexHom y))))

end Atoms.Diagrammatic
