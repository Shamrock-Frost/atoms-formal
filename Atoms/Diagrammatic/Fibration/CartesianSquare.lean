import Atoms.Diagrammatic.Marked.CylinderTensor
import Atoms.Diagrammatic.Fibration.CartesianMarking
import Atoms.Diagrammatic.Fibration.SliceFibration
import Atoms.Diagrammatic.Limits.GrayHomBoundary
import Atoms.Diagrammatic.Adjunction.Transformation

open CategoryTheory Opposite Atoms.Shape Simplicial HomotopicalAlgebra Atoms.Homotopical
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

noncomputable def DiagSet.graySquareLeftEdge {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :=
  DiagSet.Edge.ofCell (uliftYonedaEquiv ((GrayDiagSet.leftUnitor (ball.{u} (atomGlobe 1))).inv ≫
    (grayTensorRight (ball.{u} (atomGlobe 1))).map (uliftYoneda.map (atomGlobeVertex ε)) ≫ σ))

noncomputable def DiagSet.graySquareRightEdge {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :=
  DiagSet.Edge.ofCell (uliftYonedaEquiv ((GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv ≫
    (grayTensorLeft (ball.{u} (atomGlobe 1))).map (uliftYoneda.map (atomGlobeVertex ε)) ≫ σ))

theorem DiagSet.graySquareLeftEdge_cell_eq {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :
    (DiagSet.graySquareLeftEdge σ ε).cell =
      uliftYonedaEquiv ((GrayDiagSet.leftUnitor (ball.{u} (atomGlobe 1))).inv ≫
        (grayTensorRight (ball.{u} (atomGlobe 1))).map
          (uliftYoneda.map (atomGlobeVertex ε)) ≫ σ) := rfl

theorem DiagSet.graySquareRightEdge_cell_eq {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :
    (DiagSet.graySquareRightEdge σ ε).cell =
      uliftYonedaEquiv ((GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv ≫
        (grayTensorLeft (ball.{u} (atomGlobe 1))).map
          (uliftYoneda.map (atomGlobeVertex ε)) ≫ σ) := rfl

theorem DiagSet.graySquareLeftEdge_cell {E : DiagSet.{u}}
    (c : diagram ((grayHomRight (ball.{u} (atomGlobe 1))).obj E) (atomGlobe 1)) (ε : Bool) :
    (DiagSet.graySquareLeftEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1) c)
      ε).cell =
      uliftYonedaEquiv ((GrayDiagSet.leftUnitor (ball.{u} (atomGlobe 1))).inv ≫
        grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E atomPoint
          (((grayHomRight (ball.{u} (atomGlobe 1))).obj E).map (atomGlobeVertex ε).op c)) := by
  rw [grayHomRightCellEquiv_map]
  rfl

theorem DiagSet.graySquareLeftEdge_cell_src {E : DiagSet.{u}}
    {x y : ((grayHomRight (ball.{u} (atomGlobe 1))).obj E).Vertex} (e : ((grayHomRight (ball.{u}
      (atomGlobe 1))).obj E).Edge x y) :
    (DiagSet.graySquareLeftEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1)
      e.cell) false).cell =
      uliftYonedaEquiv ((GrayDiagSet.leftUnitor (ball.{u} (atomGlobe 1))).inv ≫
        grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E atomPoint x) := by
  rw [DiagSet.graySquareLeftEdge_cell, e.src_eq]

theorem DiagSet.graySquareLeftEdge_cell_tgt {E : DiagSet.{u}}
    {x y : ((grayHomRight (ball.{u} (atomGlobe 1))).obj E).Vertex} (e : ((grayHomRight (ball.{u}
      (atomGlobe 1))).obj E).Edge x y) :
    (DiagSet.graySquareLeftEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1)
      e.cell) true).cell =
      uliftYonedaEquiv ((GrayDiagSet.leftUnitor (ball.{u} (atomGlobe 1))).inv ≫
        grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E atomPoint y) := by
  rw [DiagSet.graySquareLeftEdge_cell, e.tgt_eq]

theorem DiagSet.grayHomRightCellEquiv_eval {K E : DiagSet.{u}}
    (f : ball.{u} atomPoint ⟶ K)
    (c : diagram ((grayHomRight K).obj E) (atomGlobe 1)) :
    uliftYonedaEquiv ((GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv ≫
      (grayTensorLeft (ball.{u} (atomGlobe 1))).map f ≫
      grayHomRightCellEquiv K E (atomGlobe 1) c) =
      (((grayHomRestrict f).app E ≫ grayHomRightPointIso.hom.app E).app
        (op (atomGlobe 1))) c := by
  have h := homEquiv_comp_grayHomRightPointIso_hom_app
    ((grayTensorLeft (ball.{u} (atomGlobe 1))).map f ≫
      grayHomRightCellEquiv K E (atomGlobe 1) c)
  rw [← homEquiv_comp_grayHomRestrict, homEquiv_ball, Equiv.symm_apply_apply] at h
  have hi : inv (grayTensorFst (ball.{u} (atomGlobe 1)) (ball.{u} atomPoint)) =
      (GrayDiagSet.rightUnitor (ball.{u} (atomGlobe 1))).inv := by
    apply (cancel_epi (grayTensorFst (ball.{u} (atomGlobe 1)) (ball.{u} atomPoint))).1
    rw [IsIso.hom_inv_id, grayTensorFst_point, Iso.hom_inv_id]
  rw [hi] at h
  exact (congrArg uliftYonedaEquiv h).symm.trans (by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl)

theorem DiagSet.graySquareRightEdge_cell {E : DiagSet.{u}}
    (c : diagram ((grayHomRight (ball.{u} (atomGlobe 1))).obj E) (atomGlobe 1)) (ε : Bool) :
    (DiagSet.graySquareRightEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1)
      c) ε).cell =
      (((grayHomRestrict (uliftYoneda.map (atomGlobeVertex ε))).app E ≫
        grayHomRightPointIso.hom.app E).app (op (atomGlobe 1))) c :=
  DiagSet.grayHomRightCellEquiv_eval _ c

theorem DiagSet.graySquareRightEdge_cell_src {E : DiagSet.{u}}
    {x y : ((grayHomRight (ball.{u} (atomGlobe 1))).obj E).Vertex} (e : ((grayHomRight (ball.{u}
      (atomGlobe 1))).obj E).Edge x y) :
    (DiagSet.graySquareRightEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1)
      e.cell) false).cell =
      (e.map ((grayHomRestrict (uliftYoneda.map (atomGlobeVertex false))).app E ≫
        grayHomRightPointIso.hom.app E)).cell :=
  DiagSet.graySquareRightEdge_cell e.cell false

theorem DiagSet.graySquareRightEdge_cell_tgt {E : DiagSet.{u}}
    {x y : ((grayHomRight (ball.{u} (atomGlobe 1))).obj E).Vertex} (e : ((grayHomRight (ball.{u}
      (atomGlobe 1))).obj E).Edge x y) :
    (DiagSet.graySquareRightEdge (grayHomRightCellEquiv (ball.{u} (atomGlobe 1)) E (atomGlobe 1)
      e.cell) true).cell =
      (e.map ((grayHomRestrict (uliftYoneda.map (atomGlobeVertex true))).app E ≫
        grayHomRightPointIso.hom.app E)).cell :=
  DiagSet.graySquareRightEdge_cell e.cell true

theorem DiagSet.graySquareLeftEdge_cell_iso {J E : DiagSet.{u}}
    (i : ball.{u} (atomGlobe 1) ≅ J)
    (c : diagram ((grayHomRight J).obj E) (atomGlobe 1)) (ε : Bool) :
    (DiagSet.graySquareLeftEdge ((grayTensorLeft (ball.{u} (atomGlobe 1))).map i.hom ≫
      grayHomRightCellEquiv J E (atomGlobe 1) c) ε).cell =
      uliftYonedaEquiv (i.hom ≫ (GrayDiagSet.leftUnitor J).inv ≫
        grayHomRightCellEquiv J E atomPoint
          (((grayHomRight J).obj E).map (atomGlobeVertex ε).op c)) := by
  rw [grayHomRightCellEquiv_map, DiagSet.graySquareLeftEdge_cell_eq]
  congr 1
  simp only [grayTensorLeft_map_eq, grayTensorRight_map_eq]
  rw [grayTensor_leftSide_map_assoc, Category.comp_id]

theorem DiagSet.graySquareRightEdge_cell_iso {J E : DiagSet.{u}}
    (i : ball.{u} (atomGlobe 1) ≅ J)
    (c : diagram ((grayHomRight J).obj E) (atomGlobe 1)) (ε : Bool) :
    (DiagSet.graySquareRightEdge ((grayTensorLeft (ball.{u} (atomGlobe 1))).map i.hom ≫
      grayHomRightCellEquiv J E (atomGlobe 1) c) ε).cell =
      (((grayHomRestrict (uliftYoneda.map (atomGlobeVertex ε) ≫ i.hom)).app E ≫
        grayHomRightPointIso.hom.app E).app (op (atomGlobe 1))) c := by
  rw [DiagSet.graySquareRightEdge_cell_eq,
    ← (grayTensorLeft (ball.{u} (atomGlobe 1))).map_comp_assoc]
  exact DiagSet.grayHomRightCellEquiv_eval _ c

noncomputable def DiagSet.graySquareOfIntervalHom {E : DiagSet.{u}}
    (c : diagram ((grayHomRight markedInterval.{u}.underlying).obj E) (atomGlobe 1)) :
    grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E :=
  (grayTensorLeft (ball.{u} (atomGlobe 1))).map intervalBallIso.hom ≫
    grayHomRightCellEquiv markedInterval.underlying E (atomGlobe 1) c

noncomputable def DiagSet.intervalHomVertexCell {E : DiagSet.{u}}
    (z : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex) :
    diagram E (atomGlobe 1) :=
  uliftYonedaEquiv (intervalBallIso.hom ≫
    (GrayDiagSet.leftUnitor markedInterval.underlying).inv ≫
    grayHomRightCellEquiv markedInterval.underlying E atomPoint z)

noncomputable def DiagSet.intervalHomEval (E : DiagSet.{u}) (ε : Bool) :
    (grayHomRight markedInterval.{u}.underlying).obj E ⟶ E :=
  (grayHomRestrict (MarkedPresheaf.forget.map (markedIntervalVertex ε))).app E ≫
    grayHomRightPointIso.hom.app E

theorem DiagSet.graySquareOfIntervalHom_left_src {E : DiagSet.{u}}
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.{u}.underlying).obj E).Edge x y) :
    (DiagSet.graySquareLeftEdge (DiagSet.graySquareOfIntervalHom e.cell) false).cell =
      DiagSet.intervalHomVertexCell x := by
  rw [DiagSet.graySquareOfIntervalHom, DiagSet.graySquareLeftEdge_cell_iso, e.src_eq]
  rfl

theorem DiagSet.graySquareOfIntervalHom_left_tgt {E : DiagSet.{u}}
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.{u}.underlying).obj E).Edge x y) :
    (DiagSet.graySquareLeftEdge (DiagSet.graySquareOfIntervalHom e.cell) true).cell =
      DiagSet.intervalHomVertexCell y := by
  rw [DiagSet.graySquareOfIntervalHom, DiagSet.graySquareLeftEdge_cell_iso, e.tgt_eq]
  rfl

theorem DiagSet.graySquareOfIntervalHom_right_src {E : DiagSet.{u}}
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.{u}.underlying).obj E).Edge x y) :
    (DiagSet.graySquareRightEdge (DiagSet.graySquareOfIntervalHom e.cell) false).cell =
      (e.map (DiagSet.intervalHomEval E false)).cell := by
  simp only [DiagSet.graySquareOfIntervalHom, DiagSet.intervalHomEval,
    forget_map_markedIntervalVertex]
  exact DiagSet.graySquareRightEdge_cell_iso intervalBallIso e.cell false

theorem DiagSet.graySquareOfIntervalHom_right_tgt {E : DiagSet.{u}}
    {x y : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex}
    (e : ((grayHomRight markedInterval.{u}.underlying).obj E).Edge x y) :
    (DiagSet.graySquareRightEdge (DiagSet.graySquareOfIntervalHom e.cell) true).cell =
      (e.map (DiagSet.intervalHomEval E true)).cell := by
  simp only [DiagSet.graySquareOfIntervalHom, DiagSet.intervalHomEval,
    forget_map_markedIntervalVertex]
  exact DiagSet.graySquareRightEdge_cell_iso intervalBallIso e.cell true

theorem DiagSet.graySquare_corner {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E)
    (ε α : Bool) :
    E.map (atomGlobeVertex α).op (DiagSet.graySquareLeftEdge σ ε).cell =
      E.map (atomGlobeVertex ε).op (DiagSet.graySquareRightEdge σ α).cell := by
  have hu : (GrayDiagSet.leftUnitor (ball.{u} atomPoint)).inv =
      (GrayDiagSet.rightUnitor (ball.{u} atomPoint)).inv :=
    (Iso.inv_eq_inv _ _).2 (isTerminalBallAtomPoint.hom_ext _ _)
  have hli := (GrayDiagSet.leftUnitor_inv_naturality (uliftYoneda.{u}.map
    (atomGlobeVertex α))).symm
  have hri := (GrayDiagSet.rightUnitor_inv_naturality (uliftYoneda.{u}.map
    (atomGlobeVertex ε))).symm
  change E.map (atomGlobeVertex α).op (uliftYonedaEquiv _) =
    E.map (atomGlobeVertex ε).op (uliftYonedaEquiv _)
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  apply congrArg uliftYonedaEquiv
  simp only [← Category.assoc, Quiver.Hom.unop_op]
  rw [hli, hri, hu]
  simp only [Category.assoc, grayTensorRight_map_eq, grayTensorLeft_map_eq,
    ← grayTensorBifunctor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Category.comp_id]

private theorem inv_grayTensorSnd_point (T : DiagSet.{u}) :
    inv (grayTensorSnd (ball.{u} atomPoint) T) = (GrayDiagSet.leftUnitor T).inv := by
  exact IsIso.inv_eq_of_hom_inv_id (by rw [grayTensorSnd_unit, Iso.hom_inv_id])

private theorem inv_grayTensorFst_point (T : DiagSet.{u}) :
    inv (grayTensorFst T (ball.{u} atomPoint)) = (GrayDiagSet.rightUnitor T).inv := by
  exact IsIso.inv_eq_of_hom_inv_id (by rw [grayTensorFst_point, Iso.hom_inv_id])

private theorem simplex_vertex_map (ε : Bool) :
    uliftYoneda.{u}.map (simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom) ≫
      uliftYoneda.map atomSimplexOneIsoGlobe.hom = uliftYoneda.map (atomGlobeVertex ε) :=
  (uliftYoneda.map_comp _ _).symm.trans
    (congrArg (fun f : atomPoint ⟶ atomGlobe 1 => uliftYoneda.{u}.map f)
      (simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom ε))

private theorem simplex_leftSide {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :
    uliftYonedaEquiv (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
      (grayTensorRight (ball.{u} (atomSimplex 1))).map
        (uliftYoneda.map (simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom)) ≫
      grayTensorBifunctor.map (uliftYoneda.map atomSimplexOneIsoGlobe.hom,
        uliftYoneda.map atomSimplexOneIsoGlobe.hom) ≫ σ) =
      E.map atomSimplexOneIsoGlobe.hom.op (DiagSet.graySquareLeftEdge σ ε).cell := by
  rw [inv_grayTensorSnd_point, DiagSet.graySquareLeftEdge_cell_eq, uliftYonedaEquiv_naturality]
  simp only [grayTensorRight_map_eq, Quiver.Hom.unop_op]
  rw [grayTensor_leftSide_map_assoc, ← simplex_vertex_map]
  rfl

private theorem simplex_rightSide {E : DiagSet.{u}}
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E) (ε : Bool) :
    uliftYonedaEquiv (inv (grayTensorFst (ball.{u} (atomSimplex 1)) (ball atomPoint)) ≫
      (grayTensorLeft (ball.{u} (atomSimplex 1))).map
        (uliftYoneda.map (simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom)) ≫
      grayTensorBifunctor.map (uliftYoneda.map atomSimplexOneIsoGlobe.hom,
        uliftYoneda.map atomSimplexOneIsoGlobe.hom) ≫ σ) =
      E.map atomSimplexOneIsoGlobe.hom.op (DiagSet.graySquareRightEdge σ ε).cell := by
  rw [inv_grayTensorFst_point, DiagSet.graySquareRightEdge_cell_eq, uliftYonedaEquiv_naturality]
  simp only [grayTensorLeft_map_eq, Quiver.Hom.unop_op]
  rw [grayTensor_rightSide_map_assoc, ← simplex_vertex_map]
  rfl

theorem DiagSet.homMk_comp_homMk_eq_of_graySquare {E : DiagSet.{u}}
    (hE : IsInftyCategory 1 E)
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E)
    {u v w z : E.Vertex} (a : E.Edge u v) (b : E.Edge v z)
    (c : E.Edge u w) (d : E.Edge w z)
    (ha : a.cell = (DiagSet.graySquareLeftEdge σ false).cell)
    (hb : b.cell = (DiagSet.graySquareRightEdge σ true).cell)
    (hc : c.cell = (DiagSet.graySquareRightEdge σ false).cell)
    (hd : d.cell = (DiagSet.graySquareLeftEdge σ true).cell) :
    HomotopyCategory.homMk hE.1 a ≫ HomotopyCategory.homMk hE.1 b =
      HomotopyCategory.homMk hE.1 c ≫ HomotopyCategory.homMk hE.1 d := by
  let G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ E :=
    grayTensorBifunctor.map (X := (_, _)) (Y := (_, _))
      (uliftYoneda.{u}.map atomSimplexOneIsoGlobe.hom,
    uliftYoneda.map atomSimplexOneIsoGlobe.hom) ≫ σ
  have ht := OneTruncation.globeHomMk_comp_globeHomMk_eq_of_square G a b c d
    ((Equiv.symm_apply_eq _).2 ((DiagSet.edgeEquivSSet_edge a).trans
      ((congrArg _ ha).trans (simplex_leftSide σ false).symm)))
    ((Equiv.symm_apply_eq _).2 ((DiagSet.edgeEquivSSet_edge b).trans
      ((congrArg _ hb).trans (simplex_rightSide σ true).symm)))
    ((Equiv.symm_apply_eq _).2 ((DiagSet.edgeEquivSSet_edge c).trans
      ((congrArg _ hc).trans (simplex_rightSide σ false).symm)))
    ((Equiv.symm_apply_eq _).2 ((DiagSet.edgeEquivSSet_edge d).trans
      ((congrArg _ hd).trans (simplex_leftSide σ true).symm)))
  have ht' := congrArg (OneTruncation.toHomotopyCategory hE).map ht
  simp only [Functor.map_comp, OneTruncation.toHomotopyCategory_map_globeHomMk] at ht'
  exact ht'

theorem DiagSet.nonempty_compStruct_of_equivalent_pasteEdges {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) {x y z : X.Vertex}
    (f : X.Edge x y) (g : X.Edge y z) (h : X.Edge x z)
    (hh : Equivalent (cellRound h.cell) (pasteEdges f g)) :
    Nonempty (SSet.Edge.CompStruct (X.edgeEquivSSet f) (X.edgeEquivSSet g)
      (X.edgeEquivSSet h)) := by
  obtain ⟨U, c, -, hU, hc₁, hc₂⟩ := exists_equivalence_cell_side hX.1 false _ _ hh
  have hd : (cellRound h.cell).dim = 1 := dimension_atomGlobe 1
  rw [hd] at hU hc₁ hc₂
  have hhcell := equiv_ofCell_edgeEquivSSet_symm (X.edgeEquivSSet h)
  rw [Equiv.symm_apply_apply] at hhcell
  have hc₁' := hc₁.trans hhcell.symm
  have hc₂' := hc₂.trans (equiv_pasteEdges_edgeEquivSSet f g)
  let a := X.edgeEquivSSet f
  let b := X.edgeEquivSSet g
  let d := X.edgeEquivSSet h
  let τ : diagram X (atomSimplex 2) := (DiagSet.toSSet.obj X).σ 0 d.edge
  have hτ₁ := equiv_boundary_false_ofCell_atomSimplex_two τ
  have hτ₂ := equiv_boundary_true_ofCell_atomSimplex_two τ
  have hsh : ((ofCell (a.edge : diagram X (atomSimplex 1))).paste
        (ofCell (b.edge : diagram X (atomSimplex 1))) 0
        (pastable_ofCell_simplexEdge a b)).shape.ogp =
      ((ofCell ((DiagSet.toSSet.obj X).δ 2 τ : diagram X (atomSimplex 1))).paste
        (ofCell ((DiagSet.toSSet.obj X).δ 0 τ : diagram X (atomSimplex 1))) 0
        (pastable_ofCell_atomSimplex_two τ)).shape.ogp := by
    have : Subsingleton (((atomSimplex 1).toMoleculeShape.boundary 0 true).ogp ≅
        ((atomSimplex 1).toMoleculeShape.boundary 0 false).ogp) :=
      ((atomSimplex 1).toMoleculeShape.boundary 0 true).isMolecule.subsingleton_iso
    exact congrArg (fun ψ => ((atomSimplex 1).toMoleculeShape.paste
      (atomSimplex 1).toMoleculeShape 0 ψ).ogp) (Subsingleton.elim _ _)
  obtain ⟨φ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso U.toMoleculeShape
    (atomSimplex 2).toMoleculeShape (n := 1)
    (fun α => by
      cases α
      · exact hc₁'.iso ≪≫ hτ₁.iso.symm
      · exact hc₂'.iso ≪≫ eqToIso hsh ≪≫ hτ₂.iso.symm)
    U.isAtom (atomSimplex 2).isAtom hU (dimension_atomSimplex 2)
  let Φ : atomSimplex 2 ≅ U := (Atom.isoOfOGPIso φ).symm
  let s : diagram X (atomSimplex 2) := X.map Φ.hom.op c
  have hs := equiv_ofCell_map_iso Φ c
  have d₁ : (DiagSet.toSSet.obj X).δ 1 s = d.edge :=
    ofCell_equiv_ofCell_iff.1 ((equiv_boundary_false_ofCell_atomSimplex_two s).symm.trans
      ((hs.boundary 1 false).trans hc₁'))
  have d₂₀ := eq_of_equiv_paste (pastable_ofCell_atomSimplex_two s)
    (pastable_ofCell_simplexEdge a b)
    ((equiv_boundary_true_ofCell_atomSimplex_two s).symm.trans
      ((hs.boundary 1 true).trans hc₂'))
  exact ⟨SSet.Edge.CompStruct.mk s (ofCell_map_injective d₂₀.1)
    (ofCell_map_injective d₂₀.2) d₁⟩

noncomputable def DiagSet.compStructOfSimplex {E : DiagSet.{u}} {x y z : E.Vertex}
    (s : diagram E (atomSimplex 2)) (a : E.Edge x y) (b : E.Edge y z) (c : E.Edge x z)
    (ha : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op s = a.cell)
    (hb : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op s = b.cell)
    (hc : E.map (atomSimplexOneIsoGlobe.inv ≫
      simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op s = c.cell) :
    SSet.Edge.CompStruct (E.edgeEquivSSet a) (E.edgeEquivSSet b) (E.edgeEquivSSet c) := by
  have face (i : Fin 3) {u v : E.Vertex} (e : E.Edge u v)
      (he : E.map (atomSimplexOneIsoGlobe.inv ≫
        simplexHom (SimplexCategory.δ i).toOrderHom).op s = e.cell) :
      (DiagSet.toSSet.obj E).δ i s = (E.edgeEquivSSet e).edge := by
    rw [DiagSet.edgeEquivSSet_edge, ← he, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id_assoc]
    rfl
  exact ⟨s, face 2 a ha, face 0 b hb, face 1 c hc⟩

theorem DiagSet.IsCartesianEdge.of_compStruct {E S : DiagSet.{u}} {p : E ⟶ S}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {x y z : E.Vertex} {a : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
    (s : SSet.Edge.CompStruct (E.edgeEquivSSet a) (E.edgeEquivSSet b) (E.edgeEquivSSet c))
    (hb : DiagSet.IsCartesianEdge p b) (hc : DiagSet.IsCartesianEdge p c) :
    DiagSet.IsCartesianEdge p a := by
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  have face (i : Fin 3) {u v : E.Vertex} (e : E.Edge u v)
      (he : (DiagSet.toSSet.obj E).δ i s.simplex = (E.edgeEquivSSet e).edge) :
      SSet.stdSimplex.δ i ≫ SSet.yonedaEquiv.symm s.simplex =
        SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge :=
    (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ i) s.simplex).trans
      (congrArg SSet.yonedaEquiv.symm he)
  have hb' := hb.isCartesianEdge_toSSet
  have hc' := hc.isCartesianEdge_toSSet
  rw [← face 0 b s.d₀] at hb'
  rw [← face 1 c s.d₁] at hc'
  apply (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration p a).2
  rw [← face 2 a s.d₂]
  exact (SSet.isCartesianEdge_δ_two_iff_δ_one (DiagSet.toSSet.map p) _ hb').2 hc'

theorem DiagSet.nonempty_compStruct_of_graySquare {E : DiagSet.{u}}
    (hE : IsInftyCategory 1 E)
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E)
    {u v w z : E.Vertex} (a : E.Edge u v) (b : E.Edge v z)
    (c : E.Edge u w) (d : E.Edge w z) (e : E.Edge u z)
    (ha : a.cell = (DiagSet.graySquareLeftEdge σ false).cell)
    (hb : b.cell = (DiagSet.graySquareRightEdge σ true).cell)
    (hc : c.cell = (DiagSet.graySquareRightEdge σ false).cell)
    (hd : d.cell = (DiagSet.graySquareLeftEdge σ true).cell)
    (s : SSet.Edge.CompStruct (E.edgeEquivSSet a) (E.edgeEquivSSet b) (E.edgeEquivSSet e)) :
    Nonempty (SSet.Edge.CompStruct (E.edgeEquivSSet c) (E.edgeEquivSSet d)
      (E.edgeEquivSSet e)) := by
  apply DiagSet.nonempty_compStruct_of_equivalent_pasteEdges hE
  apply equivalent_symm
  apply (HomotopyCategory.homMk_comp_homMk_iff hE.1 c d e).1
  exact (DiagSet.homMk_comp_homMk_eq_of_graySquare hE σ a b c d ha hb hc hd).symm.trans
    (homMk_comp_homMk_of_compStruct hE s)

theorem DiagSet.IsCartesianEdge.of_homMk_comp_homMk_eq {E S : DiagSet.{u}} {p : E ⟶ S}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (hE : IsInftyCategory 1 E) {u v w z : E.Vertex}
    {a : E.Edge u v} {b : E.Edge v z} {c : E.Edge u w} {d : E.Edge w z}
    (h : HomotopyCategory.homMk hE.1 a ≫ HomotopyCategory.homMk hE.1 b =
      HomotopyCategory.homMk hE.1 c ≫ HomotopyCategory.homMk hE.1 d)
    (ha : DiagSet.IsCartesianEdge p a) (hb : DiagSet.IsCartesianEdge p b)
    (hd : DiagSet.IsCartesianEdge p d) : DiagSet.IsCartesianEdge p c := by
  obtain ⟨s, e, hs₂, hs₀, hs₁, he⟩ := DiagSet.IsCartesianEdge.exists_comp ha hb
  let t := DiagSet.compStructOfSimplex s a b e hs₂ hs₀ hs₁
  have hh := h.symm.trans (homMk_comp_homMk_of_compStruct hE t)
  obtain ⟨t'⟩ := DiagSet.nonempty_compStruct_of_equivalent_pasteEdges hE c d e
    (equivalent_symm ((HomotopyCategory.homMk_comp_homMk_iff hE.1 c d e).1 hh))
  exact DiagSet.IsCartesianEdge.of_compStruct t' hd he

theorem DiagSet.IsCartesianEdge.of_graySquare {E S : DiagSet.{u}} {p : E ⟶ S}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E)
    (hu : DiagSet.IsCartesianEdge p (DiagSet.graySquareLeftEdge σ false))
    (hv : DiagSet.IsCartesianEdge p (DiagSet.graySquareLeftEdge σ true))
    (h₁ : DiagSet.IsCartesianEdge p (DiagSet.graySquareRightEdge σ true)) :
    DiagSet.IsCartesianEdge p (DiagSet.graySquareRightEdge σ false) := by
  let a := DiagSet.graySquareLeftEdge σ false
  let b : E.Edge _ _ := ⟨(DiagSet.graySquareRightEdge σ true).cell,
    (DiagSet.graySquare_corner σ false true).symm, rfl⟩
  let c : E.Edge _ _ := ⟨(DiagSet.graySquareRightEdge σ false).cell,
    (DiagSet.graySquare_corner σ false false).symm, rfl⟩
  let d : E.Edge _ _ := ⟨(DiagSet.graySquareLeftEdge σ true).cell,
    DiagSet.graySquare_corner σ true false, DiagSet.graySquare_corner σ true true⟩
  have hE := isInftyCategory_of_isFibrant 1 ((DiagSet.toInfty 1).obj E)
    (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have hb : DiagSet.IsCartesianEdge p b :=
    (DiagSet.isCartesianEdge_congr p (e := b) (e' := DiagSet.graySquareRightEdge σ true) rfl).2 h₁
  have hd : DiagSet.IsCartesianEdge p d :=
    (DiagSet.isCartesianEdge_congr p (e := d) (e' := DiagSet.graySquareLeftEdge σ true) rfl).2 hv
  obtain ⟨s, e, hs₂, hs₀, hs₁, he⟩ := DiagSet.IsCartesianEdge.exists_comp hu hb
  obtain ⟨t⟩ := DiagSet.nonempty_compStruct_of_graySquare hE σ a b c d e
    rfl rfl rfl rfl (DiagSet.compStructOfSimplex s a b e hs₂ hs₀ hs₁)
  exact (DiagSet.isCartesianEdge_congr p (e := c) (e' := DiagSet.graySquareRightEdge σ false)
    rfl).1
    (DiagSet.IsCartesianEdge.of_compStruct (p := p) (a := c) (b := d) (c := e) t hd he)

theorem DiagSet.IsCartesianEdge.of_graySquare_left {E S : DiagSet.{u}} {p : E ⟶ S}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (σ : grayTensor (ball.{u} (atomGlobe 1)) (ball.{u} (atomGlobe 1)) ⟶ E)
    (h₀ : DiagSet.IsCartesianEdge p (DiagSet.graySquareRightEdge σ false))
    (h₁ : DiagSet.IsCartesianEdge p (DiagSet.graySquareRightEdge σ true))
    (hy : DiagSet.IsCartesianEdge p (DiagSet.graySquareLeftEdge σ true)) :
    DiagSet.IsCartesianEdge p (DiagSet.graySquareLeftEdge σ false) := by
  let a := DiagSet.graySquareLeftEdge σ false
  let b : E.Edge _ _ := ⟨(DiagSet.graySquareRightEdge σ true).cell,
    (DiagSet.graySquare_corner σ false true).symm, rfl⟩
  let c : E.Edge _ _ := ⟨(DiagSet.graySquareRightEdge σ false).cell,
    (DiagSet.graySquare_corner σ false false).symm, rfl⟩
  let d : E.Edge _ _ := ⟨(DiagSet.graySquareLeftEdge σ true).cell,
    DiagSet.graySquare_corner σ true false, DiagSet.graySquare_corner σ true true⟩
  have hE := isInftyCategory_of_isFibrant 1 ((DiagSet.toInfty 1).obj E)
    (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have h := DiagSet.homMk_comp_homMk_eq_of_graySquare hE σ a b c d rfl rfl rfl rfl
  have hc : DiagSet.IsCartesianEdge p c :=
    (DiagSet.isCartesianEdge_congr p (e := c) (e' := DiagSet.graySquareRightEdge σ false) rfl).2 h₀
  have hd : DiagSet.IsCartesianEdge p d :=
    (DiagSet.isCartesianEdge_congr p (e := d) (e' := DiagSet.graySquareLeftEdge σ true) rfl).2 hy
  have hb : DiagSet.IsCartesianEdge p b :=
    (DiagSet.isCartesianEdge_congr p (e := b) (e' := DiagSet.graySquareRightEdge σ true) rfl).2 h₁
  exact DiagSet.IsCartesianEdge.of_homMk_comp_homMk_eq (p := p) hE h.symm hc hd hb

end Atoms.Diagrammatic
