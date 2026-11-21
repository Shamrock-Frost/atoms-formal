import Atoms.Diagrammatic.OneTruncation
import Atoms.Diagrammatic.Limits.GrayHomBoundary

open CategoryTheory Limits Opposite Simplicial Atoms.Shape
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {W X Y Z : DiagSet.{u}}

private theorem vertexHom_app (x : X.Vertex) (f : X ⟶ Y) :
    vertexHom (x.map f) = vertexHom x ≫ f :=
  (vertexHom_comp x f).symm

private theorem eq_of_vertexHom_eq {x y : X.Vertex}
    (h : vertexHom x = vertexHom y) : x = y :=
  vertexHom_injective h

theorem vertexHom_diagramVertex (F : X ⟶ Y) :
    vertexHom (diagramVertex F) = (grayTensorRightAdjunction X).homEquiv _ Y
      (grayTensorSnd (ball.{u} atomPoint) X ≫ F) :=
  (vertexHom_uliftYonedaEquiv _).trans (comp_diagramPoint _ F)

noncomputable def diagramVertexEquiv (X Y : DiagSet.{u}) :
    (X ⟶ Y) ≃ ((grayHomRight X).obj Y).Vertex where
  toFun F := diagramVertex F
  invFun v := inv (grayTensorSnd (ball.{u} atomPoint) X) ≫
    ((grayTensorRightAdjunction X).homEquiv _ Y).symm
      (vertexHom v)
  left_inv F := by
    simp only [vertexHom_diagramVertex, Equiv.symm_apply_apply, IsIso.inv_hom_id_assoc]
  right_inv v := vertexHom_injective (by
    rw [vertexHom_diagramVertex, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply])

theorem diagramVertexEquiv_apply (F : X ⟶ Y) :
    diagramVertexEquiv X Y F = diagramVertex F :=
  rfl

noncomputable def grayHomEval (x : X.Vertex) (Y : DiagSet.{u}) :
    (grayHomRight X).obj Y ⟶ Y :=
  (grayHomRestrict (vertexHom x)).app Y ≫ grayHomRightPointIso.hom.app Y

theorem homEquiv_comp_grayHomEval {T : DiagSet.{u}} (x : X.Vertex)
    (φ : grayTensor T X ⟶ Y) :
    (grayTensorRightAdjunction X).homEquiv T Y φ ≫ grayHomEval x Y =
      inv (grayTensorFst T (ball.{u} atomPoint)) ≫
        (grayTensorLeft T).map (vertexHom x) ≫ φ := by
  rw [grayHomEval, ← Category.assoc, homEquiv_comp_grayHomRestrict,
    homEquiv_comp_grayHomRightPointIso_hom_app]

private theorem inv_grayTensorFst_comp_grayTensorSnd :
    inv (grayTensorFst (ball.{u} atomPoint) (ball.{u} atomPoint)) ≫
      grayTensorSnd _ _ = 𝟙 _ :=
  isTerminalBallAtomPoint.hom_ext _ _

theorem grayHomEval_app_diagramVertex (x : X.Vertex) (F : X ⟶ Y) :
    (diagramVertex F).map (grayHomEval x Y) = x.map F := by
  refine eq_of_vertexHom_eq ?_
  rw [vertexHom_app, vertexHom_diagramVertex, homEquiv_comp_grayHomEval,
    ← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_grayTensorSnd, ← Category.assoc,
    ← Category.assoc, inv_grayTensorFst_comp_grayTensorSnd, Category.id_comp, ← vertexHom_app]

theorem grayHomRight_map_app_diagramVertex (F : X ⟶ Y) (H : Y ⟶ Z) :
    (diagramVertex F).map ((grayHomRight X).map H) = diagramVertex (F ≫ H) :=
  eq_of_vertexHom_eq (by
    rw [vertexHom_app, vertexHom_diagramVertex,
      vertexHom_diagramVertex,
      ← Adjunction.homEquiv_naturality_right, Category.assoc])

theorem grayHomRestrict_app_diagramVertex (K : W ⟶ X) (F : X ⟶ Y) :
    (diagramVertex F).map ((grayHomRestrict K).app Y) = diagramVertex (K ≫ F) :=
  eq_of_vertexHom_eq (by
    rw [vertexHom_app, vertexHom_diagramVertex,
      vertexHom_diagramVertex,
      homEquiv_comp_grayHomRestrict, ← Category.assoc, grayTensorLeft_map_grayTensorSnd,
      Category.assoc])

@[reassoc]
theorem grayHomRight_map_comp_grayHomEval (x : X.Vertex) (H : Y ⟶ Z) :
    (grayHomRight X).map H ≫ grayHomEval x Z = grayHomEval x Y ≫ H := by
  rw [grayHomEval, grayHomEval, ← Category.assoc, NatTrans.naturality, Category.assoc,
    Category.assoc]
  exact congrArg (_ ≫ ·) (grayHomRightPointIso.hom.naturality H)

@[reassoc]
theorem grayHomRestrict_app_comp_grayHomEval (K : W ⟶ X) (w : W.Vertex)
    (Y : DiagSet.{u}) :
    (grayHomRestrict K).app Y ≫ grayHomEval w Y =
      grayHomEval (w.map K) Y := by
  rw [grayHomEval, grayHomEval, ← Category.assoc, ← NatTrans.comp_app, ← grayHomRestrict_comp]
  exact congrArg (fun i => (grayHomRestrict i).app Y ≫ _) (vertexHom_comp w K)

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

private theorem equiv_boundary_edgeL (c : diagram X square) (i j : Fin 2) (α : Bool)
    (h : cond α 0 1 = j) :
    ((ofCell (edgeL i c)).boundary 0 α).Equiv (ofCell (X.map (corner i j).op c)) :=
  h ▸ ((equiv_ofCell_map_iso (asIso projL).symm _).boundary 0 α).trans
    (equiv_boundary_sideL c i α)

private theorem equiv_boundary_edgeR (c : diagram X square) (i j : Fin 2) (α : Bool)
    (h : cond α 0 1 = i) :
    ((ofCell (edgeR j c)).boundary 0 α).Equiv (ofCell (X.map (corner i j).op c)) :=
  h ▸ ((equiv_ofCell_map_iso (asIso projR).symm _).boundary 0 α).trans
    (equiv_boundary_sideR c j α)

private theorem equiv_boundary_false_square_edges (c : diagram X square)
    {a b : diagram X (atomSimplex 1)} (ha : edgeL 1 c = a) (hb : edgeR 0 c = b)
    (h : (ofCell a).Pastable (ofCell b) 0) :
    ((ofCell c).boundary 1 false).Equiv ((ofCell a).paste (ofCell b) 0 h) := by
  subst ha hb
  exact (equiv_boundary_false_square c).trans (Equiv.paste
    (equiv_ofCell_map_iso (asIso projL).symm _).symm
    (equiv_ofCell_map_iso (asIso projR).symm _).symm _ h)

private theorem equiv_boundary_true_square_edges (c : diagram X square)
    {a b : diagram X (atomSimplex 1)} (ha : edgeR 1 c = a) (hb : edgeL 0 c = b)
    (h : (ofCell a).Pastable (ofCell b) 0) :
    ((ofCell c).boundary 1 true).Equiv ((ofCell a).paste (ofCell b) 0 h) := by
  subst ha hb
  exact (equiv_boundary_true_square c).trans (Equiv.paste
    (equiv_ofCell_map_iso (asIso projR).symm _).symm
    (equiv_ofCell_map_iso (asIso projL).symm _).symm _ h)

private theorem vertex_eq_of_equiv {U : Atom} {w : diagram X U}
    {x y x' y' : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) (e' : SSet.Edge x' y')
    (α β : Bool) (h : ((ofCell (e.edge : diagram X (atomSimplex 1))).boundary 0 α).Equiv (ofCell w))
    (h' : ((ofCell (e'.edge : diagram X (atomSimplex 1))).boundary 0 β).Equiv (ofCell w)) :
    cond α y x = cond β y' x' := by
  have hv {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) (α : Bool) :
      ((ofCell (e.edge : diagram X (atomSimplex 1))).boundary 0 α).Equiv
        (ofCell (cond α y x : diagram X (atomSimplex 0))) := by
    cases α
    · exact (hasBdry_ofCell_simplexEdge e).side
    · exact (hasBdry_ofCell_simplexEdge e).other
  exact ofCell_equiv_ofCell_iff.1 ((hv e α).symm.trans (h.trans (h'.symm.trans (hv e' β))))

private theorem edgeL_app (f : X ⟶ Y) (i : Fin 2) (c : diagram X square) :
    edgeL i (f.app _ c) = f.app _ (edgeL i c) := by
  rw [edgeL, edgeL, NatTrans.naturality_apply, NatTrans.naturality_apply]

private theorem edgeR_app (f : X ⟶ Y) (j : Fin 2) (c : diagram X square) :
    edgeR j (f.app _ c) = f.app _ (edgeR j c) := by
  rw [edgeR, edgeR, NatTrans.naturality_apply, NatTrans.naturality_apply]

private theorem homMk_comp_homMk_eq_of_rel (c : diagram Y square)
    {p q r s : (DiagSet.toSSet.obj (ball.{u} square)) _⦋0⦌} (A : SSet.Edge p q)
    (B : SSet.Edge q r) (A' : SSet.Edge p s) (B' : SSet.Edge s r)
    (hA : edgeL 1 (uliftYonedaEquiv (𝟙 (ball.{u} square))) = A.edge)
    (hB : edgeR 0 (uliftYonedaEquiv (𝟙 (ball.{u} square))) = B.edge)
    (hA' : edgeR 1 (uliftYonedaEquiv (𝟙 (ball.{u} square))) = A'.edge)
    (hB' : edgeL 0 (uliftYonedaEquiv (𝟙 (ball.{u} square))) = B'.edge) :
    OneTruncation.homMk (A.map (DiagSet.toSSet.map (uliftYonedaEquiv.symm c))) ≫
        OneTruncation.homMk (B.map (DiagSet.toSSet.map (uliftYonedaEquiv.symm c))) =
      OneTruncation.homMk (A'.map (DiagSet.toSSet.map (uliftYonedaEquiv.symm c))) ≫
        OneTruncation.homMk (B'.map (DiagSet.toSSet.map (uliftYonedaEquiv.symm c))) := by
  have hφ := IsComposite.equiv (equiv_boundary_false_square_edges _ hA hB
    (pastable_ofCell_simplexEdge A B)).symm
    (IsComposite.paste (pastable_ofCell_simplexEdge A B) (OneTruncation.isComposite_simplex_edge A)
      (OneTruncation.isComposite_simplex_edge B))
  have hψ := IsComposite.equiv (equiv_boundary_true_square_edges _ hA' hB'
    (pastable_ofCell_simplexEdge A' B')).symm
    (IsComposite.paste (pastable_ofCell_simplexEdge A' B')
      (OneTruncation.isComposite_simplex_edge A')
      (OneTruncation.isComposite_simplex_edge B'))
  have e : OneTruncation.homMk A ≫ OneTruncation.homMk B =
      OneTruncation.homMk A' ≫ OneTruncation.homMk B' :=
    ((OneTruncation.quotientFunctor _).map_comp _ _).symm.trans
      ((OneTruncation.boundary_eq dimension_square _ hφ hψ).trans
        ((OneTruncation.quotientFunctor _).map_comp _ _))
  let T := (oneTruncation.map (uliftYonedaEquiv.symm c)).toFunctor
  exact (congrArg₂ (· ≫ ·) (oneTruncation_map_map_homMk _ A).symm
    (oneTruncation_map_map_homMk _ B).symm).trans ((T.map_comp _ _).symm.trans
      ((congrArg T.map e).trans ((T.map_comp _ _).trans (congrArg₂ (· ≫ ·)
        (oneTruncation_map_map_homMk _ A') (oneTruncation_map_map_homMk _ B')))))

private abbrev idCell (A : Atom) : diagram (ball.{u} A) A := ULift.up (𝟙 A)

private noncomputable def topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) :
    diagram X square :=
  G.app (op square) (grayTensorCell (idCell.{u} (atomSimplex 1)) (idCell.{u} (atomSimplex 1)))

private theorem map_topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) {A B : Atom}
    (a : A ⟶ atomSimplex 1) (b : B ⟶ atomSimplex 1) :
    X.map (Atom.grayTensorMap a b).op (topCell G) =
      G.app (op (Atom.grayTensor A B)) (grayTensorCell (⟨a⟩ : diagram (ball.{u} _) _)
        (⟨b⟩ : diagram (ball.{u} _) _)) := by
  rw [topCell, ← NatTrans.naturality_apply, ← grayTensorCell_restrict]
  exact congrArg _ (congrArg₂ grayTensorCell (congrArg ULift.up (Category.comp_id a))
    (congrArg ULift.up (Category.comp_id b)))

private theorem edgeL_topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) (i : Fin 2) :
    edgeL i (topCell G) = uliftYonedaEquiv
      (inv (grayTensorSnd (ball.{u} atomPoint) (ball (atomSimplex 1))) ≫
        (grayTensorRight (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face i)) ≫ G) := by
  set H := (grayTensorRight (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face i)) ≫ G
  have e₁ : X.map (sideL i).op (topCell G) = H.app _
      (grayTensorCell (idCell.{u} (atomSimplex 0)) (idCell.{u} (atomSimplex 1))) := by
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

private theorem edgeR_topCell
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X) (j : Fin 2) :
    edgeR j (topCell G) = uliftYonedaEquiv
      (inv (grayTensorFst (ball.{u} (atomSimplex 1)) (ball atomPoint)) ≫
        (grayTensorLeft (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face j)) ≫ G) := by
  set H := (grayTensorLeft (ball.{u} (atomSimplex 1))).map (uliftYoneda.map (face j)) ≫ G
  have e₁ : X.map (sideR j).op (topCell G) = H.app _
      (grayTensorCell (idCell.{u} (atomSimplex 1)) (idCell.{u} (atomSimplex 0))) := by
    rw [map_topCell, NatTrans.comp_app_apply, grayTensorLeft_map_eq, grayTensorCell_naturality]
    exact congrArg (G.app _) (congrArg₂ grayTensorCell rfl
      (congrArg ULift.up (Category.id_comp _).symm))
  have e₂ : H = grayTensorFst _ _ ≫ inv (grayTensorFst _ (ball.{u} atomPoint)) ≫ H :=
    (IsIso.hom_inv_id_assoc (grayTensorFst _ (ball.{u} atomPoint)) _).symm
  rw [edgeR, e₁]
  conv_lhs => rw [e₂]
  rw [NatTrans.comp_app_apply, grayTensorFst_app_grayTensorCell,
    NatTrans.naturality_apply, ← Functor.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    Functor.map_id_apply]
  rfl

private theorem uliftYonedaEquiv_symm_app_taut {U : Atom} (c : diagram X U) :
    (uliftYonedaEquiv.symm c).app _ (uliftYonedaEquiv (𝟙 (ball.{u} U))) = c := by
  rw [← uliftYonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

private theorem OneTruncation.homMk_comp_homMk_eq_of_simplex_square
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ Y)
    {p q r s : (DiagSet.toSSet.obj Y) _⦋0⦌} (a : SSet.Edge p q) (b : SSet.Edge q r)
    (a' : SSet.Edge p s) (b' : SSet.Edge s r)
    (ha : a.edge = uliftYonedaEquiv (inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalSource ≫ G))
    (hb : b.edge = uliftYonedaEquiv (inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalTarget ≫ G))
    (ha' : a'.edge = uliftYonedaEquiv (inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalSource ≫ G))
    (hb' : b'.edge = uliftYonedaEquiv (inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalTarget ≫ G)) :
    homMk a ≫ homMk b = homMk a' ≫ homMk b' := by
  let t : diagram (ball.{u} square) square := uliftYonedaEquiv (𝟙 _)
  let S := DiagSet.toSSet.obj (ball.{u} square)
  let eB (s : diagram (ball.{u} square) (atomSimplex 1)) := SSet.Edge.mk' (X := S) s
  have h₁ : S.δ 0 (edgeL 1 t) = S.δ 1 (edgeR 0 t) :=
    vertex_eq_of_equiv (eB (edgeL 1 t)) (eB (edgeR 0 t)) true false
      (equiv_boundary_edgeL t 1 0 true rfl) (equiv_boundary_edgeR t 1 0 false rfl)
  have h₂ : S.δ 1 (edgeR 1 t) = S.δ 1 (edgeL 1 t) :=
    vertex_eq_of_equiv (eB (edgeR 1 t)) (eB (edgeL 1 t)) false false
      (equiv_boundary_edgeR t 1 1 false rfl) (equiv_boundary_edgeL t 1 1 false rfl)
  have h₃ : S.δ 1 (edgeL 0 t) = S.δ 0 (edgeR 1 t) :=
    vertex_eq_of_equiv (eB (edgeL 0 t)) (eB (edgeR 1 t)) false true
      (equiv_boundary_edgeL t 0 1 false rfl) (equiv_boundary_edgeR t 0 1 true rfl)
  have h₄ : S.δ 0 (edgeL 0 t) = S.δ 0 (edgeR 0 t) :=
    vertex_eq_of_equiv (eB (edgeL 0 t)) (eB (edgeR 0 t)) true true
      (equiv_boundary_edgeL t 0 0 true rfl) (equiv_boundary_edgeR t 0 0 true rfl)
  let f := uliftYonedaEquiv.symm (topCell G)
  let A := eB (edgeL 1 t)
  let B : SSet.Edge (S.δ 0 (edgeL 1 t)) (S.δ 0 (edgeR 0 t)) := SSet.Edge.mk (edgeR 0 t) h₁.symm rfl
  let A' : SSet.Edge (S.δ 1 (edgeL 1 t)) (S.δ 0 (edgeR 1 t)) := SSet.Edge.mk (edgeR 1 t) h₂ rfl
  let B' : SSet.Edge (S.δ 0 (edgeR 1 t)) (S.δ 0 (edgeR 0 t)) := SSet.Edge.mk (edgeL 0 t) h₃ h₄
  have e := homMk_comp_homMk_eq_of_rel (topCell G) A B A' B' rfl rfl rfl rfl
  have hL (i : Fin 2) : f.app (op (atomSimplex 1)) (edgeL i t) = edgeL i (topCell G) :=
    (edgeL_app f i t).symm.trans (congrArg (edgeL i) (uliftYonedaEquiv_symm_app_taut _))
  have hR (j : Fin 2) : f.app (op (atomSimplex 1)) (edgeR j t) = edgeR j (topCell G) :=
    (edgeR_app f j t).symm.trans (congrArg (edgeR j) (uliftYonedaEquiv_symm_app_taut _))
  refine (Arrow.mk_inj _ _).1 ?_
  rw [Arrow.mk_comp_eq_mk_comp (arrowMk_homMk_eq a (A.map (DiagSet.toSSet.map f))
      ((hL 1).trans ((edgeL_topCell G 1).trans ha.symm)).symm)
    (arrowMk_homMk_eq b (B.map (DiagSet.toSSet.map f))
      ((hR 0).trans ((edgeR_topCell G 0).trans hb.symm)).symm), e,
    Arrow.mk_comp_eq_mk_comp (arrowMk_homMk_eq (A'.map (DiagSet.toSSet.map f)) a'
      ((hR 1).trans ((edgeR_topCell G 1).trans ha'.symm)))
    (arrowMk_homMk_eq (B'.map (DiagSet.toSSet.map f)) b'
      ((hL 0).trans ((edgeL_topCell G 0).trans hb'.symm)))]

theorem OneTruncation.globeHomMk_comp_globeHomMk_eq_of_square
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ Y)
    {p q r s : Y.Vertex} (a : Y.Edge p q) (b : Y.Edge q r)
    (a' : Y.Edge p s) (b' : Y.Edge s r)
    (ha : edgeHom a = inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalSource ≫ G)
    (hb : edgeHom b = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalTarget ≫ G)
    (ha' : edgeHom a' = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalSource ≫ G)
    (hb' : edgeHom b' = inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalTarget ≫ G) :
    globeHomMk a ≫ globeHomMk b = globeHomMk a' ≫ globeHomMk b' := by
  have h := homMk_comp_homMk_eq_of_simplex_square G (Y.edgeEquivSSet a) (Y.edgeEquivSSet b)
      (Y.edgeEquivSSet a') (Y.edgeEquivSSet b')
      ((Equiv.symm_apply_eq _).1 ha) ((Equiv.symm_apply_eq _).1 hb)
      ((Equiv.symm_apply_eq _).1 ha') ((Equiv.symm_apply_eq _).1 hb')
  exact (congrArg₂ (· ≫ ·) (homMk_edgeEquivSSet a).symm
    (homMk_edgeEquivSSet b).symm).trans (h.trans
      (congrArg₂ (· ≫ ·) (homMk_edgeEquivSSet a') (homMk_edgeEquivSSet b')))

end Square

abbrev Transformation (F G : X ⟶ Y) : Type u :=
  ((grayHomRight X).obj Y).Edge (diagramVertex F) (diagramVertex G)

namespace Transformation

variable {F G : X ⟶ Y}

noncomputable def toMap (η : Transformation F G) : grayTensor (ball.{u} (atomSimplex 1)) X ⟶ Y :=
  ((grayTensorRightAdjunction X).homEquiv _ Y).symm (edgeHom η)

theorem edgeHom_eq (η : Transformation F G) :
    edgeHom η = (grayTensorRightAdjunction X).homEquiv _ Y η.toMap :=
  (Equiv.apply_symm_apply _ _).symm

theorem source_toMap (η : Transformation F G) :
    (grayTensorRight X).map intervalSource ≫ η.toMap =
      grayTensorSnd (ball.{u} atomPoint) X ≫ F := by
  rw [toMap, ← Adjunction.homEquiv_naturality_left_symm, intervalSource_comp_edgeHom,
    vertexHom_diagramVertex, Equiv.symm_apply_apply]

theorem target_toMap (η : Transformation F G) :
    (grayTensorRight X).map intervalTarget ≫ η.toMap =
      grayTensorSnd (ball.{u} atomPoint) X ≫ G := by
  rw [toMap, ← Adjunction.homEquiv_naturality_left_symm, intervalTarget_comp_edgeHom,
    vertexHom_diagramVertex, Equiv.symm_apply_apply]

noncomputable def ofMap (φ : grayTensor (ball.{u} (atomSimplex 1)) X ⟶ Y)
    (h₀ : (grayTensorRight X).map intervalSource ≫ φ =
      grayTensorSnd (ball.{u} atomPoint) X ≫ F)
    (h₁ : (grayTensorRight X).map intervalTarget ≫ φ =
      grayTensorSnd (ball.{u} atomPoint) X ≫ G) : Transformation F G :=
  edgeOfHom
    ((grayTensorRightAdjunction X).homEquiv _ Y φ)
    (by rw [← Adjunction.homEquiv_naturality_left, h₀, vertexHom_diagramVertex])
    (by rw [← Adjunction.homEquiv_naturality_left, h₁, vertexHom_diagramVertex])

@[simp]
theorem toMap_ofMap (φ : grayTensor (ball.{u} (atomSimplex 1)) X ⟶ Y)
    (h₀ : (grayTensorRight X).map intervalSource ≫ φ =
      grayTensorSnd (ball.{u} atomPoint) X ≫ F)
    (h₁ : (grayTensorRight X).map intervalTarget ≫ φ =
      grayTensorSnd (ball.{u} atomPoint) X ≫ G) :
    (Transformation.ofMap (F := F) (G := G) φ h₀ h₁).toMap = φ := by
  rw [toMap, ofMap, edgeHom_edgeOfHom, Equiv.symm_apply_apply]

theorem ext {η θ : Transformation F G} (h : η.toMap = θ.toMap) : η = θ :=
  edgeHom_injective (by rw [edgeHom_eq, edgeHom_eq, h])

noncomputable def app (η : Transformation F G) (x : X.Vertex) :
    Y.Edge (x.map F) (x.map G) where
  cell := (η.map (grayHomEval x Y)).cell
  src_eq := (η.map (grayHomEval x Y)).src_eq.trans (grayHomEval_app_diagramVertex x F)
  tgt_eq := (η.map (grayHomEval x Y)).tgt_eq.trans (grayHomEval_app_diagramVertex x G)

theorem cell_app (η : Transformation F G) (x : X.Vertex) :
    (η.app x).cell = (η.map (grayHomEval x Y)).cell := rfl

theorem edgeHom_app (η : Transformation F G)
    (x : X.Vertex) :
    edgeHom (η.app x) =
      inv (grayTensorFst (ball.{u} (atomSimplex 1)) (ball.{u} atomPoint)) ≫
        (grayTensorLeft _).map (vertexHom x) ≫ η.toMap := by
  change edgeHom (η.map (grayHomEval x Y)) = _
  rw [edgeHom_map, edgeHom_eq, homEquiv_comp_grayHomEval]

noncomputable def refl (F : X ⟶ Y) : Transformation F F :=
  DiagSet.Edge.id (diagramVertex F)

theorem toMap_refl (F : X ⟶ Y) :
    (refl F).toMap = grayTensorSnd (ball.{u} (atomSimplex 1)) X ≫ F := by
  rw [toMap, refl, edgeHom_id, vertexHom_diagramVertex,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ← Category.assoc,
    grayTensorRight_map_grayTensorSnd]

theorem app_refl (F : X ⟶ Y) (x : X.Vertex) :
    (refl F).app x = DiagSet.Edge.id _ :=
  edgeHom_injective (by
    rw [edgeHom_app, toMap_refl, edgeHom_id,
      ← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_grayTensorSnd,
      vertexHom_app, ← Category.assoc, ← Category.assoc, Category.assoc]
    exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _))

noncomputable def whiskerRight (η : Transformation F G) (H : Y ⟶ Z) :
    Transformation (F ≫ H) (G ≫ H) :=
  ofMap (η.toMap ≫ H) (by rw [← Category.assoc, source_toMap, Category.assoc])
    (by rw [← Category.assoc, target_toMap, Category.assoc])

theorem toMap_whiskerRight (η : Transformation F G) (H : Y ⟶ Z) :
    (η.whiskerRight H).toMap = η.toMap ≫ H :=
  toMap_ofMap _ _ _

theorem app_whiskerRight (η : Transformation F G) (H : Y ⟶ Z) (x : X.Vertex) :
    (η.whiskerRight H).app x = (η.app x).map H := by
  have h : edgeHom ((η.whiskerRight H).app x) =
      edgeHom ((η.app x).map H) := by
    rw [edgeHom_app, toMap_whiskerRight, edgeHom_map,
      edgeHom_app, Category.assoc, Category.assoc]
  exact edgeHom_injective h

noncomputable def whiskerLeft (K : W ⟶ X) (η : Transformation F G) :
    Transformation (K ≫ F) (K ≫ G) :=
  ofMap ((grayTensorLeft _).map K ≫ η.toMap)
    (by rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
      source_toMap, ← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.assoc])
    (by rw [← Category.assoc, ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc,
      target_toMap, ← Category.assoc, grayTensorLeft_map_grayTensorSnd, Category.assoc])

theorem toMap_whiskerLeft (K : W ⟶ X) (η : Transformation F G) :
    (η.whiskerLeft K).toMap = (grayTensorLeft _).map K ≫ η.toMap :=
  toMap_ofMap _ _ _

theorem app_whiskerLeft (K : W ⟶ X) (η : Transformation F G)
    (w : W.Vertex) :
    (η.whiskerLeft K).app w = η.app (w.map K) := by
  have h : edgeHom ((η.whiskerLeft K).app w) =
      edgeHom (η.app (w.map K)) := by
    rw [edgeHom_app, edgeHom_app, toMap_whiskerLeft,
      vertexHom_app, Functor.map_comp, Category.assoc]
  exact edgeHom_injective h

theorem whiskerRight_refl (F : X ⟶ Y) (H : Y ⟶ Z) :
    (refl F).whiskerRight H = refl (F ≫ H) :=
  ext (by rw [toMap_whiskerRight, toMap_refl, toMap_refl, Category.assoc])

theorem whiskerLeft_refl (K : W ⟶ X) (F : X ⟶ Y) :
    (refl F).whiskerLeft K = refl (K ≫ F) :=
  ext (by rw [toMap_whiskerLeft, toMap_refl, toMap_refl, ← Category.assoc,
    grayTensorLeft_map_grayTensorSnd, Category.assoc])

theorem naturality (η : Transformation F G) {x x' : X.Vertex}
    (e : X.Edge x x') :
    OneTruncation.globeHomMk (e.map F) ≫ OneTruncation.globeHomMk (η.app x') =
      OneTruncation.globeHomMk (η.app x) ≫ OneTruncation.globeHomMk (e.map G) :=
  OneTruncation.globeHomMk_comp_globeHomMk_eq_of_square
    ((grayTensorLeft _).map (edgeHom e) ≫ η.toMap) _ _ _ _
    (by
      rw [edgeHom_map, ← Category.assoc ((grayTensorRight _).map _),
        ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, source_toMap,
        ← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_grayTensorSnd,
        Category.assoc, IsIso.inv_hom_id_assoc])
    (by
      rw [edgeHom_app, ← Functor.map_comp_assoc, intervalTarget_comp_edgeHom])
    (by
      rw [edgeHom_app, ← Functor.map_comp_assoc, intervalSource_comp_edgeHom])
    (by
      rw [edgeHom_map, ← Category.assoc ((grayTensorRight _).map _),
        ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, target_toMap,
        ← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_grayTensorSnd,
        Category.assoc, IsIso.inv_hom_id_assoc])

noncomputable def toOneTruncation (η : Transformation F G) :
    (oneTruncation.map F).toFunctor ⟶ (oneTruncation.map G).toFunctor :=
  OneTruncation.mkNatTrans (fun x => OneTruncation.globeHomMk (η.app x)) fun _ _ e => by
    exact ((congrArg (· ≫ _) (oneTruncation_map_map_globeHomMk F
      (X.edgeEquivSSet.symm e))).trans (η.naturality (X.edgeEquivSSet.symm e))).trans
        (congrArg (_ ≫ ·) (oneTruncation_map_map_globeHomMk G
          (X.edgeEquivSSet.symm e)).symm)

@[simp]
theorem toOneTruncation_app_mk (η : Transformation F G) (x : X.Vertex) :
    η.toOneTruncation.app (OneTruncation.mk x) = OneTruncation.globeHomMk (η.app x) :=
  rfl

theorem toOneTruncation_refl (F : X ⟶ Y) : (refl F).toOneTruncation = 𝟙 _ :=
  OneTruncation.natTrans_ext fun x => by
    exact (congrArg OneTruncation.globeHomMk (app_refl F (X.vertexEquivSSet.symm x))).trans
      (OneTruncation.globeHomMk_id _)

noncomputable def homotopy (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Transformation F G) : homotopyFunctor hX.1 hY.1 F ⟶ homotopyFunctor hX.1 hY.1 G where
  app a := HomotopyCategory.homMk hY.1 (η.app a.pt)
  naturality a b φ := by
    obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 (x := a.pt) (y := b.pt) φ
    have h := congrArg (OneTruncation.toHomotopyCategory hY).map (η.naturality f)
    simp only [Functor.map_comp, OneTruncation.toHomotopyCategory_map_globeHomMk] at h
    rw [homotopyFunctor_map_homMk, homotopyFunctor_map_homMk]
    exact h

theorem homotopy_app (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (η : Transformation F G) (x : X.Vertex) :
    (η.homotopy hX hY).app ⟨x⟩ = HomotopyCategory.homMk hY.1 (η.app x) :=
  rfl

end Transformation

namespace Transformation

variable {F G : X ⟶ Y}

theorem cell_whiskerRight (η : Transformation F G) (H : Y ⟶ Z) :
    (η.whiskerRight H).cell = ((grayHomRight X).map H).app _ η.cell := by
  have h : edgeHom (η.whiskerRight H) =
      edgeHom (η.map ((grayHomRight X).map H)) := by
    rw [edgeHom_eq, toMap_whiskerRight, edgeHom_map,
      edgeHom_eq, Adjunction.homEquiv_naturality_right]
  exact cell_eq_of_edgeHom_eq _ _ h

theorem cell_whiskerLeft (K : W ⟶ X) (η : Transformation F G) :
    (η.whiskerLeft K).cell = ((grayHomRestrict K).app Y).app _ η.cell := by
  have h : edgeHom (η.whiskerLeft K) =
      edgeHom (η.map ((grayHomRestrict K).app Y)) := by
    rw [edgeHom_eq, toMap_whiskerLeft, edgeHom_map,
      edgeHom_eq, homEquiv_comp_grayHomRestrict]
  exact cell_eq_of_edgeHom_eq _ _ h

private theorem toOneTruncation_eq_of_edge {F' G' : X ⟶ Y} (η : Transformation F G)
    (η' : Transformation F' G') (hF : F = F') (hG : G = G') (h : η.cell = η'.cell) :
    η.toOneTruncation = eqToHom (by rw [hF]) ≫ η'.toOneTruncation ≫ eqToHom (by rw [hG]) := by
  subst hF hG
  obtain rfl := DiagSet.Edge.ext h
  simp

end Transformation

theorem globeHomMk_whiskerRight {F G : X ⟶ Y} (η : Transformation F G) (H : Y ⟶ Z) :
    OneTruncation.globeHomMk (η.whiskerRight H) =
      eqToHom (((oneTruncation_map_obj_mk ((grayHomRight X).map H) (diagramVertex F)).trans
        (congrArg OneTruncation.mk (grayHomRight_map_app_diagramVertex F H))).symm) ≫
        (oneTruncation.map ((grayHomRight X).map H)).toFunctor.map (OneTruncation.globeHomMk η) ≫
          eqToHom ((oneTruncation_map_obj_mk ((grayHomRight X).map H) (diagramVertex G)).trans
            (congrArg OneTruncation.mk (grayHomRight_map_app_diagramVertex G H))) := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 ((OneTruncation.arrowMk_globeHomMk_eq _
    (η.map ((grayHomRight X).map H)) (η.cell_whiskerRight H)).trans
      (congrArg Arrow.mk (oneTruncation_map_map_globeHomMk _ η).symm))
  exact h

theorem globeHomMk_whiskerLeft (K : W ⟶ X) {F G : X ⟶ Y} (η : Transformation F G) :
    OneTruncation.globeHomMk (η.whiskerLeft K) =
      eqToHom (((oneTruncation_map_obj_mk ((grayHomRestrict K).app Y) (diagramVertex F)).trans
        (congrArg OneTruncation.mk (grayHomRestrict_app_diagramVertex K F))).symm) ≫
        (oneTruncation.map ((grayHomRestrict K).app Y)).toFunctor.map (OneTruncation.globeHomMk η) ≫
          eqToHom ((oneTruncation_map_obj_mk ((grayHomRestrict K).app Y) (diagramVertex G)).trans
            (congrArg OneTruncation.mk (grayHomRestrict_app_diagramVertex K G))) := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 ((OneTruncation.arrowMk_globeHomMk_eq _
    (η.map ((grayHomRestrict K).app Y)) (η.cell_whiskerLeft K)).trans
      (congrArg Arrow.mk (oneTruncation_map_map_globeHomMk _ η).symm))
  exact h

private noncomputable def ofEdge {v w : ((grayHomRight X).obj Y).Vertex}
    (e : ((grayHomRight X).obj Y).Edge v w) :
    Transformation ((diagramVertexEquiv X Y).symm v) ((diagramVertexEquiv X Y).symm w) where
  cell := e.cell
  src_eq := e.src_eq.trans ((diagramVertexEquiv X Y).apply_symm_apply v).symm
  tgt_eq := e.tgt_eq.trans ((diagramVertexEquiv X Y).apply_symm_apply w).symm

private theorem arrowMk_homMk_app_ofEdge
    {v w : ((grayHomRight X).obj Y).Vertex} (e : ((grayHomRight X).obj Y).Edge v w)
    (x : X.Vertex) :
    Arrow.mk (OneTruncation.globeHomMk ((ofEdge e).app x)) =
      Arrow.mk (OneTruncation.globeHomMk (e.map (grayHomEval x Y))) :=
  OneTruncation.arrowMk_globeHomMk_eq _ _ rfl

private theorem toOneTruncation_ofEdge_id (v : ((grayHomRight X).obj Y).Vertex) :
    (ofEdge (DiagSet.Edge.id v)).toOneTruncation = 𝟙 _ := by
  have h : ofEdge (DiagSet.Edge.id v) = Transformation.refl _ := by
    apply DiagSet.Edge.ext
    exact congrArg (((grayHomRight X).obj Y).map (toAtomPoint (atomGlobe 1)).op)
      ((diagramVertexEquiv X Y).apply_symm_apply v).symm
  rw [h, Transformation.toOneTruncation_refl]

private noncomputable def homInterpretation (X Y : DiagSet.{u}) :
    OneTruncation.Interpretation ((grayHomRight X).obj Y) (OneTruncation X ⥤ OneTruncation Y) where
  obj v := (oneTruncation.map ((diagramVertexEquiv X Y).symm v)).toFunctor
  map e := (ofEdge e).toOneTruncation

private theorem homFreeLift_comp_evaluation (X Y : DiagSet.{u})
    (x : X.Vertex) :
    (homInterpretation X Y).freeLift ⋙ (evaluation _ _).obj (OneTruncation.mk x) =
      OneTruncation.quotientFunctor _ ⋙ (oneTruncation.map (grayHomEval x Y)).toFunctor :=
  OneTruncation.Free.functor_ext fun _ _ e =>
    (congrArg (fun α => Arrow.mk (NatTrans.app α (OneTruncation.mk x)))
      ((homInterpretation X Y).freeLift_map_edge e)).trans
      ((arrowMk_homMk_app_ofEdge e x).trans
        (congrArg Arrow.mk (oneTruncation_map_map_globeHomMk _ e).symm))

private theorem homInterpretation_respects (X Y : DiagSet.{u}) :
    (homInterpretation X Y).Respects where
  unit v := toOneTruncation_ofEdge_id v
  boundary hV c _ _ _ _ hf hg := OneTruncation.natTrans_ext fun x =>
    (Functor.congr_hom (homFreeLift_comp_evaluation X Y x) _).trans ((congrArg (_ ≫ · ≫ _)
      (congrArg (oneTruncation.map (grayHomEval x Y)).toFunctor.map
        (OneTruncation.boundary_eq hV c hf hg))).trans
          (Functor.congr_hom (homFreeLift_comp_evaluation X Y x) _).symm)

noncomputable def homFunctor (X Y : DiagSet.{u}) :
    OneTruncation ((grayHomRight X).obj Y) ⥤ (OneTruncation X ⥤ OneTruncation Y) :=
  (homInterpretation X Y).lift (homInterpretation_respects X Y)

theorem homFunctor_comp_evaluation (X Y : DiagSet.{u}) (x : X.Vertex) :
    homFunctor X Y ⋙ (evaluation _ _).obj (OneTruncation.mk x) =
      (oneTruncation.map (grayHomEval x Y)).toFunctor :=
  CategoryTheory.Quotient.lift_unique' _ _ _ ((Functor.assoc _ _ _).symm.trans
    ((congrArg (· ⋙ (evaluation _ _).obj (OneTruncation.mk x))
      ((homInterpretation X Y).quotientFunctor_comp_lift (homInterpretation_respects X Y))).trans
        (homFreeLift_comp_evaluation X Y x)))

private theorem homFunctor_map_globeHomMk_ofEdge
    {v w : ((grayHomRight X).obj Y).Vertex} (e : ((grayHomRight X).obj Y).Edge v w) :
    (homFunctor X Y).map (OneTruncation.globeHomMk e) = (ofEdge e).toOneTruncation :=
  (homInterpretation X Y).lift_map_globeHomMk (homInterpretation_respects X Y) e

theorem homFunctor_obj_mk (F : X ⟶ Y) :
    (homFunctor X Y).obj (OneTruncation.mk (diagramVertex F)) =
      (oneTruncation.map F).toFunctor :=
  congrArg (fun G => (oneTruncation.map G).toFunctor) ((diagramVertexEquiv X Y).symm_apply_apply F)

theorem homFunctor_map_globeHomMk {F G : X ⟶ Y} (η : Transformation F G) :
    (homFunctor X Y).map (OneTruncation.globeHomMk η) =
      eqToHom (homFunctor_obj_mk F) ≫ η.toOneTruncation ≫ eqToHom (homFunctor_obj_mk G).symm :=
  (homFunctor_map_globeHomMk_ofEdge η).trans (Transformation.toOneTruncation_eq_of_edge _ η
    ((diagramVertexEquiv X Y).symm_apply_apply F) ((diagramVertexEquiv X Y).symm_apply_apply G) rfl)

theorem arrowMk_eq_of_app {D : Type*} [Category* D] {F G F' G' : OneTruncation X ⥤ D}
    (α : F ⟶ G) (β : F' ⟶ G') (hF : F = F') (hG : G = G')
    (h : ∀ x, Arrow.mk (α.app (OneTruncation.mk x)) = Arrow.mk (β.app (OneTruncation.mk x))) :
    Arrow.mk α = Arrow.mk β := by
  subst hF hG
  exact congrArg Arrow.mk (OneTruncation.natTrans_ext fun x => (Arrow.mk_inj _ _).1 (h x))

theorem homFunctor_postcomp (X : DiagSet.{u}) (H : Y ⟶ Z) :
    (oneTruncation.map ((grayHomRight X).map H)).toFunctor ⋙ homFunctor X Z =
      homFunctor X Y ⋙ (Functor.whiskeringRight _ _ _).obj (oneTruncation.map H).toFunctor := by
  have hv (v : ((grayHomRight X).obj Y).Vertex) :
      (oneTruncation.map ((diagramVertexEquiv X Z).symm
        (v.map ((grayHomRight X).map H)))).toFunctor =
      (oneTruncation.map ((diagramVertexEquiv X Y).symm v)).toFunctor ⋙
        (oneTruncation.map H).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
    refine congrArg (fun f => (oneTruncation.map f).toFunctor) ?_
    rw [Equiv.symm_apply_eq, diagramVertexEquiv_apply, ← grayHomRight_map_app_diagramVertex,
      ← diagramVertexEquiv_apply, Equiv.apply_symm_apply]
  refine CategoryTheory.Quotient.lift_unique' _ _ _
    (OneTruncation.Free.functor_ext fun v w e => ?_)
  refine (congrArg Arrow.mk
    ((congrArg (homFunctor X Z).map (oneTruncation_map_map_globeHomMk _ e)).trans
      (homFunctor_map_globeHomMk_ofEdge _))).trans ((arrowMk_eq_of_app _
        (Functor.whiskerRight (ofEdge e).toOneTruncation (oneTruncation.map H).toFunctor)
        (hv v) (hv w) fun x => (OneTruncation.arrowMk_globeHomMk_eq
          ((ofEdge (e.map ((grayHomRight X).map H))).app x)
          (((ofEdge e).app x).map H)
          (congrArg (fun f => f.app _ e.cell)
            (grayHomRight_map_comp_grayHomEval x H))).trans
        (congrArg Arrow.mk (oneTruncation_map_map_globeHomMk H _).symm)).trans ?_)
  exact congrArg (fun α => Arrow.mk (Functor.whiskerRight α (oneTruncation.map H).toFunctor))
    (homFunctor_map_globeHomMk_ofEdge e).symm

theorem homFunctor_precomp (K : W ⟶ X) (Y : DiagSet.{u}) :
    (oneTruncation.map ((grayHomRestrict K).app Y)).toFunctor ⋙ homFunctor W Y =
      homFunctor X Y ⋙ (Functor.whiskeringLeft _ _ _).obj (oneTruncation.map K).toFunctor := by
  have hv (v : ((grayHomRight X).obj Y).Vertex) :
      (oneTruncation.map ((diagramVertexEquiv W Y).symm
        (v.map ((grayHomRestrict K).app Y)))).toFunctor =
      (oneTruncation.map K).toFunctor ⋙
        (oneTruncation.map ((diagramVertexEquiv X Y).symm v)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
    refine congrArg (fun f => (oneTruncation.map f).toFunctor) ?_
    rw [Equiv.symm_apply_eq, diagramVertexEquiv_apply, ← grayHomRestrict_app_diagramVertex,
      ← diagramVertexEquiv_apply, Equiv.apply_symm_apply]
  refine CategoryTheory.Quotient.lift_unique' _ _ _
    (OneTruncation.Free.functor_ext fun v w e => ?_)
  refine (congrArg Arrow.mk
    ((congrArg (homFunctor W Y).map (oneTruncation_map_map_globeHomMk _ e)).trans
      (homFunctor_map_globeHomMk_ofEdge _))).trans ((arrowMk_eq_of_app _
        (Functor.whiskerLeft (oneTruncation.map K).toFunctor (ofEdge e).toOneTruncation)
        (hv v) (hv w) fun x => OneTruncation.arrowMk_globeHomMk_eq
          ((ofEdge (e.map ((grayHomRestrict K).app Y))).app x)
          ((ofEdge e).app ((W.vertexEquivSSet.symm x).map K))
          (congrArg (fun f => f.app _ e.cell)
            (grayHomRestrict_app_comp_grayHomEval K x Y))).trans ?_)
  exact congrArg (fun α => Arrow.mk (Functor.whiskerLeft (oneTruncation.map K).toFunctor α))
    (homFunctor_map_globeHomMk_ofEdge e).symm

end Atoms.Diagrammatic
