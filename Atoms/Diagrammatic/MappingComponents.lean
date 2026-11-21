import Atoms.Diagrammatic.MappingSpace
import Atoms.Diagrammatic.HomotopyCategory
import Atoms.Diagrammatic.Suspension.Hom
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

open CategoryTheory Limits Opposite Simplicial Atoms.Shape
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section Square

private abbrev face (i : Fin 2) : atomSimplex 0 ⟶ atomSimplex 1 :=
  simplexHom (SimplexCategory.δ i).toOrderHom

private theorem isInclusionHom_face (i : Fin 2) : IsInclusionHom (face i) :=
  isInclusionHom_simplexHom_of_injective _ (SimplexCategory.mono_iff_injective.1 inferInstance)

private abbrev square : Atom := Atom.grayTensor (atomSimplex 1) (atomSimplex 1)

private abbrev sideL (i : Fin 2) : Atom.grayTensor (atomSimplex 0) (atomSimplex 1) ⟶ square :=
  Atom.grayTensorMap (face i) (𝟙 _)

private abbrev sideR (i : Fin 2) : Atom.grayTensor (atomSimplex 1) (atomSimplex 0) ⟶ square :=
  Atom.grayTensorMap (𝟙 _) (face i)

private def atomIncl {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f) : V.ogp ⟶ U.ogp :=
  ConcreteCategory.ofHom ⟨f, Atom.isMorphism_of_isInclusionHom f hf⟩

private instance {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f) :
    IsInclusion (atomIncl f hf) :=
  ⟨hf⟩

private theorem map_atomIncl_top {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f) :
    OGP.map (atomIncl f hf) ⊤ = LowerSet.Iic (f V.top) :=
  Atom.map_top f

private theorem realize_map_atomIncl {V U : Atom} (f : V ⟶ U) (hf : IsInclusionHom f)
    (z : diagram X U) :
    realize.map (RDCpx.ofInclusion (P := V.toMoleculeShape.rdc) (Q := U.toMoleculeShape.rdc)
      (atomIncl f hf)) ≫ (ofCell z).map = (ofCell (X.map f.op z)).map := by
  have hφ : RDCpx.ofInclusion (P := V.toMoleculeShape.rdc) (Q := U.toMoleculeShape.rdc)
      (atomIncl f hf) = atomToRDCpx.map f := by
    ext x
    rfl
  rw [hφ, ofCell_map_op_map]

private theorem isInclusionHom_sideL (i : Fin 2) : IsInclusionHom (sideL i) :=
  Atom.isInclusionHom_grayTensorMap _ _ (isInclusionHom_face i) Function.injective_id

private theorem isInclusionHom_sideR (i : Fin 2) : IsInclusionHom (sideR i) :=
  Atom.isInclusionHom_grayTensorMap _ _ Function.injective_id (isInclusionHom_face i)

private abbrev corner (i j : Fin 2) : Atom.grayTensor (atomSimplex 0) (atomSimplex 0) ⟶ square :=
  Atom.grayTensorMap (face i) (face j)

private theorem dimension_grayTensor_zero_one :
    (Atom.grayTensor (atomSimplex 0) (atomSimplex 1)).dimension = 1 := by
  rw [Atom.dimension_grayTensor, dimension_atomSimplex, dimension_atomSimplex]

private theorem dimension_grayTensor_one_zero :
    (Atom.grayTensor (atomSimplex 1) (atomSimplex 0)).dimension = 1 := by
  rw [Atom.dimension_grayTensor, dimension_atomSimplex, dimension_atomSimplex]

private theorem dimension_grayTensor_zero_zero :
    (Atom.grayTensor (atomSimplex 0) (atomSimplex 0)).dimension = 0 := by
  rw [Atom.dimension_grayTensor, dimension_atomSimplex]

private theorem dimension_square : square.dimension = 2 := by
  rw [Atom.dimension_grayTensor, dimension_atomSimplex]

private theorem equiv_boundary_sideL (c : diagram X square) (i : Fin 2) (α : Bool) :
    ((ofCell (X.map (sideL i).op c)).boundary 0 α).Equiv
      (ofCell (X.map (corner i (cond α 0 1)).op c)) := by
  refine (equiv_boundary_ofCell_map (X.map (sideL i).op c) (Atom.grayTensorMap (𝟙 _)
    (face (cond α 0 1))) (Atom.isInclusionHom_grayTensorMap _ _ Function.injective_id
      (isInclusionHom_face _)) dimension_grayTensor_zero_zero.le ?_).trans ?_
  · rw [Atom.map_top, Atom.boundary_grayTensor_atomSimplex_zero_one]
  · rw [← Functor.map_comp_apply, ← op_comp, Atom.grayTensorMap_comp, Category.id_comp,
      Category.comp_id]

private theorem equiv_boundary_sideR (c : diagram X square) (j : Fin 2) (α : Bool) :
    ((ofCell (X.map (sideR j).op c)).boundary 0 α).Equiv
      (ofCell (X.map (corner (cond α 0 1) j).op c)) := by
  refine (equiv_boundary_ofCell_map (X.map (sideR j).op c) (Atom.grayTensorMap
    (face (cond α 0 1)) (𝟙 _)) (Atom.isInclusionHom_grayTensorMap _ _ (isInclusionHom_face _)
      Function.injective_id) dimension_grayTensor_zero_zero.le ?_).trans ?_
  · rw [Atom.map_top, Atom.boundary_grayTensor_atomSimplex_one_zero]
  · rw [← Functor.map_comp_apply, ← op_comp, Atom.grayTensorMap_comp, Category.id_comp,
      Category.comp_id]

private theorem pastable_sideL_sideR (c : diagram X square) :
    (ofCell (X.map (sideL 1).op c)).Pastable (ofCell (X.map (sideR 0).op c)) 0 :=
  ⟨(equiv_boundary_sideL c 1 true).trans (equiv_boundary_sideR c 0 false).symm, by
    change 0 < min (Atom.grayTensor (atomSimplex 0) (atomSimplex 1)).dimension
      (Atom.grayTensor (atomSimplex 1) (atomSimplex 0)).dimension
    rw [dimension_grayTensor_zero_one, dimension_grayTensor_one_zero]
    omega⟩

private theorem pastable_sideR_sideL (c : diagram X square) :
    (ofCell (X.map (sideR 1).op c)).Pastable (ofCell (X.map (sideL 0).op c)) 0 :=
  ⟨(equiv_boundary_sideR c 1 true).trans (equiv_boundary_sideL c 0 false).symm, by
    change 0 < min (Atom.grayTensor (atomSimplex 1) (atomSimplex 0)).dimension
      (Atom.grayTensor (atomSimplex 0) (atomSimplex 1)).dimension
    rw [dimension_grayTensor_zero_one, dimension_grayTensor_one_zero]
    omega⟩

private theorem equiv_boundary_false_square (c : diagram X square) :
    ((ofCell c).boundary 1 false).Equiv
      ((ofCell (X.map (sideL 1).op c)).paste (ofCell (X.map (sideR 0).op c)) 0
        (pastable_sideL_sideR c)) := by
  refine (equiv_paste_of_emb _ _ ((ofCell c).boundary 1 false) 0 (pastable_sideL_sideR c)
    (ofCell c).map ((ofCell c).shape.boundaryIncl 1 false) (atomIncl _ (isInclusionHom_sideL 1))
    (atomIncl _ (isInclusionHom_sideR 0)) (boundary_map _ 1 false)
    (realize_map_atomIncl _ _ c) (realize_map_atomIncl _ _ c) ?_).symm
  rw [map_atomIncl_top, map_atomIncl_top, MoleculeShape.map_boundaryIncl_top]
  exact Atom.isPastingIn_boundary_square false

private theorem equiv_boundary_true_square (c : diagram X square) :
    ((ofCell c).boundary 1 true).Equiv
      ((ofCell (X.map (sideR 1).op c)).paste (ofCell (X.map (sideL 0).op c)) 0
        (pastable_sideR_sideL c)) := by
  refine (equiv_paste_of_emb _ _ ((ofCell c).boundary 1 true) 0 (pastable_sideR_sideL c)
    (ofCell c).map ((ofCell c).shape.boundaryIncl 1 true) (atomIncl _ (isInclusionHom_sideR 1))
    (atomIncl _ (isInclusionHom_sideL 0)) (boundary_map _ 1 true)
    (realize_map_atomIncl _ _ c) (realize_map_atomIncl _ _ c) ?_).symm
  rw [map_atomIncl_top, map_atomIncl_top, MoleculeShape.map_boundaryIncl_top]
  exact Atom.isPastingIn_boundary_square true

private noncomputable abbrev projL :
    Atom.grayTensor (atomSimplex 0) (atomSimplex 1) ⟶ atomSimplex 1 :=
  Atom.grayTensorMap (toAtomPoint _) (𝟙 _) ≫ (Atom.grayTensorLeftUnitor _).hom

private noncomputable abbrev projR :
    Atom.grayTensor (atomSimplex 1) (atomSimplex 0) ⟶ atomSimplex 1 :=
  Atom.grayTensorMap (𝟙 _) (toAtomPoint _) ≫ (Atom.grayTensorRightUnitor _).hom

private instance : IsIso (toAtomPoint (atomSimplex 0)) :=
  isIso_toAtomPoint_of_dimension_eq_zero (dimension_atomSimplex 0)

private instance : IsIso projL := by
  have : IsIso (X := ((atomSimplex 0, atomSimplex 1) : Atom × Atom))
      (Y := (atomPoint, atomSimplex 1))
      (toAtomPoint _, 𝟙 _) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (Atom.grayTensorMap (toAtomPoint (atomSimplex 0)) (𝟙 (atomSimplex 1))) :=
    Functor.map_isIso Atom.grayTensorFunctor
      (X := ((atomSimplex 0, atomSimplex 1) : Atom × Atom)) (Y := (atomPoint, atomSimplex 1))
      (toAtomPoint _, 𝟙 _)
  infer_instance

private instance : IsIso projR := by
  have : IsIso (X := ((atomSimplex 1, atomSimplex 0) : Atom × Atom))
      (Y := (atomSimplex 1, atomPoint))
      (𝟙 _, toAtomPoint _) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (Atom.grayTensorMap (𝟙 (atomSimplex 1)) (toAtomPoint (atomSimplex 0))) :=
    Functor.map_isIso Atom.grayTensorFunctor
      (X := ((atomSimplex 1, atomSimplex 0) : Atom × Atom)) (Y := (atomSimplex 1, atomPoint))
      (𝟙 _, toAtomPoint _)
  infer_instance

private noncomputable def edgeL (i : Fin 2) (c : diagram X square) : diagram X (atomSimplex 1) :=
  X.map (inv projL).op (X.map (sideL i).op c)

private noncomputable def edgeR (j : Fin 2) (c : diagram X square) : diagram X (atomSimplex 1) :=
  X.map (inv projR).op (X.map (sideR j).op c)

private theorem equiv_edgeL (i : Fin 2) (c : diagram X square) :
    (ofCell (edgeL i c)).Equiv (ofCell (X.map (sideL i).op c)) :=
  equiv_ofCell_map_iso (asIso projL).symm _

private theorem equiv_edgeR (j : Fin 2) (c : diagram X square) :
    (ofCell (edgeR j c)).Equiv (ofCell (X.map (sideR j).op c)) :=
  equiv_ofCell_map_iso (asIso projR).symm _

private theorem equiv_boundary_false_square_edges (c : diagram X square)
    {a b : diagram X (atomSimplex 1)} (ha : edgeL 1 c = a) (hb : edgeR 0 c = b)
    (h : (ofCell a).Pastable (ofCell b) 0) :
    ((ofCell c).boundary 1 false).Equiv ((ofCell a).paste (ofCell b) 0 h) := by
  subst ha hb
  exact (equiv_boundary_false_square c).trans
    (Equiv.paste (equiv_edgeL 1 c).symm (equiv_edgeR 0 c).symm _ h)

private theorem equiv_boundary_true_square_edges (c : diagram X square)
    {a b : diagram X (atomSimplex 1)} (ha : edgeR 1 c = a) (hb : edgeL 0 c = b)
    (h : (ofCell a).Pastable (ofCell b) 0) :
    ((ofCell c).boundary 1 true).Equiv ((ofCell a).paste (ofCell b) 0 h) := by
  subst ha hb
  exact (equiv_boundary_true_square c).trans
    (Equiv.paste (equiv_edgeR 1 c).symm (equiv_edgeL 0 c).symm _ h)

private theorem pastable_edgeL_edgeR (c : diagram X square) :
    (ofCell (edgeL 1 c)).Pastable (ofCell (edgeR 0 c)) 0 :=
  (pastable_sideL_sideR c).of_equiv (equiv_edgeL 1 c).symm (equiv_edgeR 0 c).symm

private theorem pastable_edgeR_edgeL (c : diagram X square) :
    (ofCell (edgeR 1 c)).Pastable (ofCell (edgeL 0 c)) 0 :=
  (pastable_sideR_sideL c).of_equiv (equiv_edgeR 1 c).symm (equiv_edgeL 0 c).symm

private theorem shape_paste_intervals {a b a' b' : diagram X (atomSimplex 1)}
    (h : (ofCell a).Pastable (ofCell b) 0) (h' : (ofCell a').Pastable (ofCell b') 0) :
    ((ofCell a).paste (ofCell b) 0 h).shape.ogp =
      ((ofCell a').paste (ofCell b') 0 h').shape.ogp := by
  have : Subsingleton (((atomSimplex 1).toMoleculeShape.boundary 0 true).ogp ≅
      ((atomSimplex 1).toMoleculeShape.boundary 0 false).ogp) :=
    ((atomSimplex 1).toMoleculeShape.boundary 0 true).isMolecule.subsingleton_iso
  exact congrArg (fun ψ => ((atomSimplex 1).toMoleculeShape.paste
    (atomSimplex 1).toMoleculeShape 0 ψ).ogp) (Subsingleton.elim _ _)

end Square

section GrayHom

private abbrev idCell (A : Atom) : diagram (ball.{u} A) A := ULift.up (𝟙 A)

private noncomputable def topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) :
    diagram X square :=
  G.app (op square) (grayTensorCell (idCell.{u} (atomSimplex 1))
    (idCell.{u} (atomSimplex 1)))

private theorem grayTensor_ball_hom_ext {A B : Atom} {Z : DiagSet.{u}}
    {φ ψ : grayTensor (ball.{u} A) (ball.{u} B) ⟶ Z}
    (h : φ.app (op (Atom.grayTensor A B)) (grayTensorCell (idCell.{u} A)
        (idCell.{u} B)) =
      ψ.app (op (Atom.grayTensor A B)) (grayTensorCell (idCell.{u} A)
        (idCell.{u} B))) : φ = ψ :=
  have e (χ : grayTensor (ball.{u} A) (ball.{u} B) ⟶ Z) :
      uliftYonedaEquiv ((grayTensorBallIso A B).inv ≫ χ) =
        χ.app (op (Atom.grayTensor A B)) (grayTensorCell (idCell.{u} A) (idCell.{u} B)) :=
    (uliftYonedaEquiv_comp _ χ).trans (congrArg (χ.app _) (Equiv.apply_symm_apply _ _))
  (cancel_epi (grayTensorBallIso A B).inv).1 (uliftYonedaEquiv.injective
    ((e φ).trans (h.trans (e ψ).symm)))

private theorem map_topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) {A B : Atom}
    (a : A ⟶ atomSimplex 1) (b : B ⟶ atomSimplex 1) :
    X.map (Atom.grayTensorMap a b).op (topCell G) =
      G.app (op (Atom.grayTensor A B)) (grayTensorCell (⟨a⟩ : diagram (ball.{u} _) _)
        (⟨b⟩ : diagram (ball.{u} _) _)) := by
  rw [topCell, ← NatTrans.naturality_apply, ← grayTensorCell_restrict]
  exact congrArg _ (congrArg₂ grayTensorCell (congrArg ULift.up (Category.comp_id a))
    (congrArg ULift.up (Category.comp_id b)))

private noncomputable def ofTopCell (s : diagram X square) :
    grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X :=
  (grayTensorBallIso _ _).hom ≫ uliftYonedaEquiv.symm s

private theorem topCell_ofTopCell (s : diagram X square) : topCell (ofTopCell s) = s := by
  rw [topCell, ofTopCell, NatTrans.comp_app_apply, grayTensorBallIso_hom_app_grayTensorCell,
    uliftYonedaEquiv_symm_apply_app, Atom.grayTensorMap_id]
  exact Functor.map_id_apply X _ s

private theorem edgeL_topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) (i : Fin 2) :
    edgeL i (topCell G) = uliftYonedaEquiv
      (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
        (grayTensorRight (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face i)) ≫ G) := by
  set H := (grayTensorRight (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face i)) ≫ G
  have e₁ : X.map (sideL i).op (topCell G) = H.app _
      (grayTensorCell (idCell.{u} (atomSimplex 0))
        (idCell.{u} (atomSimplex 1))) := by
    rw [map_topCell, NatTrans.comp_app_apply, grayTensorRight_map_eq, grayTensorCell_naturality]
    exact congrArg (G.app _) (congrArg₂ grayTensorCell
      (congrArg ULift.up (Category.id_comp _).symm) rfl)
  have e₂ : H = grayTensorSnd _ _ ≫ inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ H :=
    (IsIso.hom_inv_id_assoc (grayTensorSnd (ball.{u} atomPoint) _) _).symm
  rw [edgeL, e₁]
  conv_lhs => rw [e₂]
  rw [NatTrans.comp_app_apply, grayTensorSnd_app_grayTensorCell,
    NatTrans.naturality_apply, ← Functor.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    Functor.map_id_apply]
  rfl

private theorem hom_atomSimplex_zero_ext {U : Atom} (f g : U ⟶ atomSimplex 0) : f = g :=
  Atom.hom_ext fun _ => (eq_top_atomSimplex_zero _).trans (eq_top_atomSimplex_zero _).symm

variable {x y : X.Vertex}

private theorem fixedEnd_iff
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) (j : Fin 2)
    (z : X.Vertex) :
    (grayTensorLeft (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face j)) ≫ G =
        grayTensorSnd _ (ball (atomSimplex 0)) ≫ vertexHom z ↔
      edgeR j (topCell G) = (SSet.Edge.id (X.vertexEquivSSet z)).edge := by
  have e₁ : ((grayTensorLeft (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face j)) ≫ G).app
      _ (grayTensorCell (idCell.{u} (atomSimplex 1))
        (idCell.{u} (atomSimplex 0))) = X.map (sideR j).op (topCell G) := by
    rw [map_topCell, NatTrans.comp_app_apply, grayTensorLeft_map_eq, grayTensorCell_naturality]
    exact congrArg (G.app _) (congrArg₂ grayTensorCell rfl
      (congrArg ULift.up (by exact Category.id_comp (face j))))
  have e₂ : (grayTensorSnd _ (ball (atomSimplex 0)) ≫ vertexHom z).app
      _ (grayTensorCell (idCell.{u} (atomSimplex 1))
        (idCell.{u} (atomSimplex 0))) =
      X.map (projR ≫ simplexHom (SimplexCategory.σ (0 : Fin 1)).toOrderHom).op
        (z : diagram X (atomSimplex 0)) := by
    refine Eq.trans (congrArg
      ((vertexHom z).app (op (Atom.grayTensor (atomSimplex 1) (atomSimplex 0))))
      (grayTensorSnd_app_grayTensorCell (idCell.{u} (atomSimplex 1)) (idCell.{u} atomPoint))) ?_
    exact congrArg (fun φ : Atom.grayTensor (atomSimplex 1) (atomSimplex 0) ⟶ atomSimplex 0 =>
      X.map φ.op (z : diagram X (atomSimplex 0))) (hom_atomSimplex_zero_ext _ _)
  constructor
  · intro h
    have h' := e₁.symm.trans ((congrArg (fun φ : grayTensor (ball.{u} (atomSimplex 1))
      (ball.{u} (atomSimplex 0)) ⟶ X => φ.app _ (grayTensorCell (idCell.{u} (atomSimplex 1))
        (idCell.{u} (atomSimplex 0)))) h).trans e₂)
    rw [edgeR, h']
    exact (Functor.map_comp_apply X _ (inv projR).op (z : diagram X (atomSimplex 0))).symm.trans
      (congrArg (fun φ : atomSimplex 1 ⟶ atomSimplex 0 => X.map φ.op (z : diagram X _))
        (hom_atomSimplex_zero_ext _ _))
  · intro h
    refine grayTensor_ball_hom_ext (e₁.trans (Eq.trans ?_ e₂.symm))
    have h₂ : X.map (sideR j).op (topCell G) = X.map projR.op (edgeR j (topCell G)) := by
      rw [edgeR, ← Functor.map_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id,
        Functor.map_id_apply]
    rw [h₂, h]
    exact (Functor.map_comp_apply X _ _ (z : diagram X (atomSimplex 0))).symm

private theorem isFixedEnds_iff_edgeR
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) :
    IsFixedEnds x y G ↔
      edgeR 1 (topCell G) = (SSet.Edge.id (X.vertexEquivSSet x)).edge ∧
        edgeR 0 (topCell G) = (SSet.Edge.id (X.vertexEquivSSet y)).edge :=
  and_congr (fixedEnd_iff G 1 x) (fixedEnd_iff G 0 y)

end GrayHom

section Edges

variable {x y : X.Vertex}

private noncomputable abbrev edgeMap
    (e : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) _⦋1⦌) :
    grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X :=
  grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 1) e.1

private theorem edge_mappingSpaceVerticesEquiv_δ
    (e : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) _⦋1⦌) (i : Fin 2) :
    (X.edgeEquivSSet (X.mappingSpaceVerticesEquiv x y
        ((DiagSet.vertexEquivSSet _).symm ((DiagSet.toSSet.obj _).δ i e)))).edge =
      edgeL i (topCell (edgeMap e)) :=
  (DiagSet.mappingSpaceVerticesEquiv_edge _ _ _).trans (edgeL_topCell _ i).symm

private theorem dim_pasteEdges {z w : X.Vertex} (f : X.Edge x z) (g : X.Edge z w) :
    (pasteEdges f g).dim = 1 :=
  (hasBdry_pasteEdges f g).dim_h

theorem DiagSet.nonempty_edge_mappingSpace_iff (hX : IsInftyCategory 1 X) (f g : X.Edge x y) :
    Nonempty (DiagSet.Edge (X.mappingSpace x y).toFunctor ((X.mappingSpaceVerticesEquiv x y).symm f)
        ((X.mappingSpaceVerticesEquiv x y).symm g)) ↔
      Equivalent (cellRound f.cell) (cellRound g.cell) := by
  have hid (z : X.Vertex) : (SSet.Edge.id (X.vertexEquivSSet z)).edge =
      (X.edgeEquivSSet (DiagSet.Edge.id z)).edge := by rw [DiagSet.edgeEquivSSet_id]
  constructor
  · rintro ⟨E⟩
    set e := DiagSet.edgeEquivSSet E
    set c := topCell (edgeMap e.edge)
    obtain ⟨hx, hy⟩ := (isFixedEnds_iff_edgeR (edgeMap e.edge)).1 e.edge.2
    have hf : edgeL 1 c = (X.edgeEquivSSet f).edge := by
      rw [← edge_mappingSpaceVerticesEquiv_δ, e.src_eq, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    have hg : edgeL 0 c = (X.edgeEquivSSet g).edge := by
      rw [← edge_mappingSpaceVerticesEquiv_δ, e.tgt_eq, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    have hs : cellRound c ∈ equivalences X :=
      hX.2 square c (by rw [dimension_square]; exact_mod_cast (by omega : 1 < 2))
    have huv := equivalent_of_mem_equivalences_cond false hs
      (dim_pasteEdges f (DiagSet.Edge.id y)) (dim_pasteEdges (DiagSet.Edge.id x) g)
      dimension_square
      ((equiv_boundary_false_square_edges c hf (hy.trans (hid y)) _).trans
        (equiv_pasteEdges_edgeEquivSSet f (DiagSet.Edge.id y)).symm)
      ((equiv_boundary_true_square_edges c (hx.trans (hid x)) hg _).trans
        (equiv_pasteEdges_edgeEquivSSet (DiagSet.Edge.id x) g).symm)
    exact equivalent_trans (equivalent_symm (equivalent_pasteEdges_id_right f))
      (equivalent_trans huv (equivalent_pasteEdges_id_left g))
  · intro hfg
    have huv : Equivalent (pasteEdges f (DiagSet.Edge.id y)) (pasteEdges (DiagSet.Edge.id x) g) :=
      equivalent_trans (equivalent_pasteEdges_id_right f)
        (equivalent_trans hfg (equivalent_symm (equivalent_pasteEdges_id_left g)))
    obtain ⟨U, c, -, hU, hc₁, hc₂⟩ := exists_equivalence_cell_side hX.1 false _ _ huv
    rw [dim_pasteEdges] at hU hc₁ hc₂
    have hc₁' := hc₁.trans (equiv_pasteEdges_edgeEquivSSet f (DiagSet.Edge.id y))
    have hc₂' := hc₂.trans (equiv_pasteEdges_edgeEquivSSet (DiagSet.Edge.id x) g)
    let τ : diagram X square :=
      X.map (toAtomPoint square ≫ inv (toAtomPoint (atomSimplex 0))).op
        (x : diagram X (atomSimplex 0))
    have hτ₁ := equiv_boundary_false_square_edges τ rfl rfl (pastable_edgeL_edgeR τ)
    have hτ₂ := equiv_boundary_true_square_edges τ rfl rfl (pastable_edgeR_edgeL τ)
    obtain ⟨φ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso U.toMoleculeShape
      square.toMoleculeShape (n := 1)
      (fun α => by
        cases α
        · exact hc₁'.iso ≪≫ eqToIso (shape_paste_intervals
            (pastable_ofCell_simplexEdge _ _) (pastable_edgeL_edgeR τ)) ≪≫ hτ₁.iso.symm
        · exact hc₂'.iso ≪≫ eqToIso (shape_paste_intervals
            (pastable_ofCell_simplexEdge _ _) (pastable_edgeR_edgeL τ)) ≪≫ hτ₂.iso.symm)
      U.isAtom square.isAtom hU dimension_square
    let Φ : square ≅ U := (Atom.isoOfOGPIso φ).symm
    let s : diagram X square := X.map Φ.hom.op c
    have hs := equiv_ofCell_map_iso Φ c
    have h₁ := eq_of_equiv_paste (pastable_edgeL_edgeR s) (pastable_ofCell_simplexEdge _ _)
      ((equiv_boundary_false_square_edges s rfl rfl (pastable_edgeL_edgeR s)).symm.trans
        ((hs.boundary 1 false).trans hc₁'))
    have h₂ := eq_of_equiv_paste (pastable_edgeR_edgeL s) (pastable_ofCell_simplexEdge _ _)
      ((equiv_boundary_true_square_edges s rfl rfl (pastable_edgeR_edgeL s)).symm.trans
        ((hs.boundary 1 true).trans hc₂'))
    have hG : IsFixedEnds x y (ofTopCell s) := by
      rw [isFixedEnds_iff_edgeR, topCell_ofTopCell]
      exact ⟨(ofCell_map_injective h₂.1).trans (hid x).symm,
        (ofCell_map_injective h₁.2).trans (hid y).symm⟩
    let e : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) _⦋1⦌ :=
      ⟨(grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 1)).symm (ofTopCell s),
        (congrArg (IsFixedEnds x y) (Equiv.apply_symm_apply
          (grayHomRightCellEquiv (ball.{u} (atomSimplex 1)) X (atomSimplex 1)) _)).mpr hG⟩
    have he : edgeMap e = ofTopCell s := Equiv.apply_symm_apply _ _
    refine ⟨DiagSet.edgeEquivSSet.symm (SSet.Edge.mk e ?_ ?_)⟩
    · refine (Equiv.symm_apply_eq _).1 ((Equiv.eq_symm_apply _).2
        (X.edgeEquivSSet.injective (SSet.Edge.ext ?_)))
      rw [edge_mappingSpaceVerticesEquiv_δ, he, topCell_ofTopCell]
      exact ofCell_map_injective h₁.1
    · refine (Equiv.symm_apply_eq _).1 ((Equiv.eq_symm_apply _).2
        (X.edgeEquivSSet.injective (SSet.Edge.ext ?_)))
      rw [edge_mappingSpaceVerticesEquiv_δ, he, topCell_ofTopCell]
      exact ofCell_map_injective h₂.2

private theorem nonempty_edge_iff_homMk_eq (hX : IsInftyCategory 1 X)
    (v w : DiagSet.Vertex (X.mappingSpace x y).toFunctor) :
    Nonempty (DiagSet.Edge (X.mappingSpace x y).toFunctor v w) ↔
      HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv x y v) =
        HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv x y w) := by
  rw [HomotopyCategory.homMk_eq_homMk_iff, ← DiagSet.nonempty_edge_mappingSpace_iff hX]
  simp only [Equiv.symm_apply_apply]

private noncomputable def vertexClass (hX : IsInftyCategory 1 X)
    (v : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) _⦋0⦌) :
    (⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩ :=
  HomotopyCategory.homMk hX.1 (X.mappingSpaceVerticesEquiv x y ((DiagSet.vertexEquivSSet _).symm v))

private theorem vertexClass_eq_of_edge (hX : IsInftyCategory 1 X)
    {v w : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) _⦋0⦌} (e : SSet.Edge v w) :
    vertexClass hX v = vertexClass hX w :=
  (nonempty_edge_iff_homMk_eq hX ((DiagSet.vertexEquivSSet _).symm v)
    ((DiagSet.vertexEquivSSet _).symm w)).1 ⟨DiagSet.edgeEquivSSet.symm e⟩

noncomputable def DiagSet.mappingSpaceπ₀Equiv (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    SSet.π₀ (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor) ≃
      ((⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩) :=
  Equiv.ofBijective (SSet.π₀.lift (vertexClass hX) fun _ _ e => vertexClass_eq_of_edge hX e)
    ⟨fun a b hab => by
      induction a with | mk v => ?_
      induction b with | mk w => ?_
      rw [SSet.π₀.lift_mk, SSet.π₀.lift_mk] at hab
      obtain ⟨e⟩ := (nonempty_edge_iff_homMk_eq hX _ _).2 hab
      exact SSet.π₀.sound (DiagSet.edgeEquivSSet e),
    fun φ => by
      obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 φ
      exact ⟨SSet.π₀.mk (DiagSet.vertexEquivSSet _ ((X.mappingSpaceVerticesEquiv x y).symm f)), by
        rw [SSet.π₀.lift_mk, vertexClass, Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩⟩

theorem DiagSet.mappingSpaceπ₀Equiv_mk (hX : IsInftyCategory 1 X) (x y : X.Vertex)
    (e : X.Edge x y) :
    X.mappingSpaceπ₀Equiv hX x y (SSet.π₀.mk (DiagSet.vertexEquivSSet _
        ((X.mappingSpaceVerticesEquiv x y).symm e))) = HomotopyCategory.homMk hX.1 e := by
  refine (SSet.π₀.lift_mk (vertexClass hX) (fun _ _ e => vertexClass_eq_of_edge hX e) _).trans ?_
  rw [vertexClass, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem DiagSet.mappingSpaceπ₀Equiv_mappingSpaceId (hX : IsInftyCategory 1 X) (x : X.Vertex) :
    X.mappingSpaceπ₀Equiv hX x x (SSet.π₀.mk (DiagSet.vertexEquivSSet _
        ((X.mappingSpaceVerticesEquiv x x).symm (DiagSet.Edge.id x)))) = 𝟙 _ := by
  rw [DiagSet.mappingSpaceπ₀Equiv_mk]
  exact HomotopyCategory.homMk_id hX.1 x

theorem DiagSet.bipointedHomπ₀Equiv_symm_mappingSpaceπ₀Equiv_mk (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) (e : X.Edge x y) :
    (X.bipointedHomπ₀Equiv hX x y).symm
        (X.mappingSpaceπ₀Equiv hX x y (SSet.π₀.mk (DiagSet.vertexEquivSSet _
          ((X.mappingSpaceVerticesEquiv x y).symm e)))) =
      SSet.π₀.mk (DiagSet.vertexEquivSSet _ ((X.bipointedHomVerticesEquiv x y).symm e)) := by
  rw [DiagSet.mappingSpaceπ₀Equiv_mk, Equiv.symm_apply_eq, DiagSet.bipointedHomπ₀Equiv_mk]

theorem DiagSet.mappingSpaceπ₀Equiv_mapπ₀ {Y : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) (x y : X.Vertex)
    (v : SSet.π₀ (DiagSet.toSSet.obj ((X.mappingSpace x y).toFunctor))) :
    Y.mappingSpaceπ₀Equiv hY _ _
        (SSet.mapπ₀ (DiagSet.toSSet.map (X.mappingSpaceMap F x y)) v) =
      (homotopyFunctor hX.1 hY.1 F).map (X.mappingSpaceπ₀Equiv hX x y v) := by
  induction v with | mk w => ?_
  obtain ⟨e, rfl⟩ :=
    ((DiagSet.vertexEquivSSet _).symm.trans (X.mappingSpaceVerticesEquiv x y)).symm.surjective w
  rw [SSet.mapπ₀_mk]
  have h : (DiagSet.toSSet.map (X.mappingSpaceMap F x y)).app _
      (DiagSet.vertexEquivSSet _ ((X.mappingSpaceVerticesEquiv x y).symm e)) =
        DiagSet.vertexEquivSSet _ ((Y.mappingSpaceVerticesEquiv (x.map F) (y.map F)).symm
          (e.map F)) := by
    refine ((DiagSet.vertexEquivSSet _).symm.trans
      (Y.mappingSpaceVerticesEquiv _ _)).injective ?_
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rw [← DiagSet.vertexEquivSSet_map, Equiv.symm_apply_apply]
    refine Y.edgeEquivSSet.injective ?_
    rw [DiagSet.mappingSpaceVerticesEquiv_map, Equiv.apply_symm_apply, DiagSet.edgeEquivSSet_map]
  refine Eq.trans (congrArg _ (congrArg SSet.π₀.mk h)) ?_
  exact (DiagSet.mappingSpaceπ₀Equiv_mk hY _ _ _).trans
    (congrArg (homotopyFunctor hX.1 hY.1 F).map (DiagSet.mappingSpaceπ₀Equiv_mk hX x y e)).symm

end Edges

end Atoms.Diagrammatic
