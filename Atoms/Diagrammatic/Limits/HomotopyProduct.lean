import Atoms.Diagrammatic.Adjunction.Transformation
import Atoms.Diagrammatic.Limits.PairHom

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {K X : DiagSet.{u}}

private noncomputable def coneMap {T : DiagSet.{u}} (α : Bool) (d : K ⟶ X)
    (φ : T ⟶ coneObject α d) :
    grayTensor T (ball.{u} (atomSimplex 1)) ⟶ (grayHomRight K).obj X :=
  (coneObjectHomEquiv α d T φ).1.2

private theorem coneMap_comp {T T' : DiagSet.{u}} (α : Bool) (d : K ⟶ X) (g : T' ⟶ T)
    (φ : T ⟶ coneObject α d) :
    coneMap α d (g ≫ φ) = (grayTensorRight _).map g ≫ coneMap α d φ :=
  (congrArg (((grayTensorRightAdjunction _).homEquiv _ _).symm) (Category.assoc _ _ _)).trans
    ((grayTensorRightAdjunction _).homEquiv_naturality_left_symm _ _)

private theorem grayTensorLeft_map_intervalSource_coneMap {T : DiagSet.{u}} (α : Bool)
    (d : K ⟶ X) (φ : T ⟶ coneObject α d) :
    (grayTensorLeft T).map intervalSource ≫ coneMap α d φ = grayTensorFst T _ ≫
      (φ ≫ coneObjectπ α d) ≫
        cond α (constDiagram K X) (isTerminalBallAtomPoint.from X ≫ diagramPoint d) := by
  have h : intervalSource.{u} = coprod.inl ≫ intervalBoundaryι.{u} := (coprod.inl_desc _ _).symm
  rw [h, Functor.map_comp, Category.assoc]
  exact (congrArg _ (coneObjectHomEquiv α d T φ).2).trans (grayTensorBoundaryDesc_inl _ _ _)

private theorem grayTensorLeft_map_intervalTarget_coneMap {T : DiagSet.{u}} (α : Bool)
    (d : K ⟶ X) (φ : T ⟶ coneObject α d) :
    (grayTensorLeft T).map intervalTarget ≫ coneMap α d φ = grayTensorFst T _ ≫
      (φ ≫ coneObjectπ α d) ≫
        cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint d) (constDiagram K X) := by
  have h : intervalTarget.{u} = coprod.inr ≫ intervalBoundaryι.{u} := (coprod.inr_desc _ _).symm
  rw [h, Functor.map_comp, Category.assoc]
  exact (congrArg _ (coneObjectHomEquiv α d T φ).2).trans (grayTensorBoundaryDesc_inr _ _ _)

variable {x y : X.Vertex}

private noncomputable abbrev ev (X : DiagSet.{u}) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u}) :
    (grayHomRight intervalBoundary.{u}).obj X ⟶ X :=
  (grayHomRestrict i).app X ≫ grayHomRightPointIso.hom.app X

private theorem constDiagram_comp_ev (i : ball.{u} atomPoint ⟶ intervalBoundary.{u}) :
    constDiagram intervalBoundary.{u} X ≫ ev X i = 𝟙 X := by
  rw [constDiagram_comp_grayHomRestrict_assoc, constDiagram_comp_grayHomRightPointIso_hom_app]

private theorem diagramPoint_comp_ev (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z) :
    (isTerminalBallAtomPoint.from X ≫ diagramPoint (pairDiagram x y)) ≫ ev X i =
      isTerminalBallAtomPoint.from X ≫ vertexHom z := by
  rw [Category.assoc, diagramPoint_comp_grayHomRestrict_assoc,
    diagramPoint_comp_grayHomRightPointIso_hom_app, hz, ← Category.assoc]
  exact congrArg (· ≫ vertexHom z) (isTerminalBallAtomPoint.hom_ext _ _)

private theorem cond_comp_ev_source (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z) :
    cond α (constDiagram intervalBoundary.{u} X)
        (isTerminalBallAtomPoint.from X ≫ diagramPoint (pairDiagram x y)) ≫ ev X i =
      cond α (𝟙 X) (isTerminalBallAtomPoint.from X ≫ vertexHom z) := by
  cases α
  · exact diagramPoint_comp_ev i hz
  · exact constDiagram_comp_ev i

private theorem cond_comp_ev_target (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z) :
    cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint (pairDiagram x y))
        (constDiagram intervalBoundary.{u} X) ≫ ev X i =
      cond α (isTerminalBallAtomPoint.from X ≫ vertexHom z) (𝟙 X) := by
  cases α
  · exact constDiagram_comp_ev i
  · exact diagramPoint_comp_ev i hz

private theorem vertexHom_comp_cond (α : Bool) (a z : X.Vertex) :
    vertexHom a ≫ cond α (𝟙 X) (isTerminalBallAtomPoint.from X ≫ vertexHom z) =
      vertexHom (cond α a z) := by
  cases α
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ vertexHom z)
      (isTerminalBallAtomPoint.hom_ext _ (𝟙 _)))).trans (Category.id_comp _)
  · exact Category.comp_id _

private theorem vertexHom_comp_cond' (α : Bool) (a z : X.Vertex) :
    vertexHom a ≫ cond α (isTerminalBallAtomPoint.from X ≫ vertexHom z) (𝟙 X) =
      vertexHom (cond α z a) := by
  cases α
  · exact Category.comp_id _
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ vertexHom z)
      (isTerminalBallAtomPoint.hom_ext _ (𝟙 _)))).trans (Category.id_comp _)

private theorem grayTensorSnd_point :
    grayTensorSnd (ball.{u} atomPoint) (ball.{u} atomPoint) =
      grayTensorFst (ball.{u} atomPoint) (ball.{u} atomPoint) :=
  isTerminalBallAtomPoint.hom_ext _ _

private theorem comp_inv_grayTensorSnd {B : DiagSet.{u}} (g : ball.{u} atomPoint ⟶ B) :
    g ≫ inv (grayTensorSnd (ball.{u} atomPoint) B) =
      inv (grayTensorSnd (ball.{u} atomPoint) (ball.{u} atomPoint)) ≫
        (grayTensorLeft _).map g := by
  rw [IsIso.comp_inv_eq, Category.assoc, grayTensorLeft_map_grayTensorSnd, IsIso.inv_hom_id_assoc]

noncomputable def pairConeApex (α : Bool)
    (c : (coneObject α (pairDiagram x y)).Vertex) : X.Vertex :=
  DiagSet.Vertex.map (coneObjectπ α (pairDiagram x y)) c

private noncomputable def legHom (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    (c : (coneObject α (pairDiagram x y)).Vertex) : ball.{u} (atomSimplex 1) ⟶ X :=
  inv (grayTensorSnd (ball.{u} atomPoint) (ball.{u} (atomSimplex 1))) ≫
    coneMap α (pairDiagram x y) (vertexHom c) ≫ ev X i

private theorem comp_legHom (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    (c : (coneObject α (pairDiagram x y)).Vertex)
    {g : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
    {b : X ⟶ (grayHomRight intervalBoundary.{u}).obj X}
    (hg : (grayTensorLeft _).map g ≫ coneMap α (pairDiagram x y) (vertexHom c) =
      grayTensorFst _ _ ≫ (vertexHom c ≫ coneObjectπ α (pairDiagram x y)) ≫ b) :
    g ≫ legHom α i c = vertexHom (c.map (coneObjectπ α (pairDiagram x y))) ≫ b ≫ ev X i := by
  rw [legHom, ← Category.assoc, comp_inv_grayTensorSnd, Category.assoc, reassoc_of% hg,
    ← grayTensorSnd_point, IsIso.inv_hom_id_assoc, vertexHom_comp_assoc]

private noncomputable def leg (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    X.Edge (cond α (pairConeApex α c) z)
      (cond α z (pairConeApex α c)) :=
  edgeOfHom (legHom α i c)
    ((comp_legHom α i c (grayTensorLeft_map_intervalSource_coneMap α _ _)).trans
      ((congrArg (vertexHom _ ≫ ·) (cond_comp_ev_source α i hz)).trans
        (vertexHom_comp_cond α _ z)))
    ((comp_legHom α i c (grayTensorLeft_map_intervalTarget_coneMap α _ _)).trans
      ((congrArg (vertexHom _ ≫ ·) (cond_comp_ev_target α i hz)).trans
        (vertexHom_comp_cond' α _ z)))

noncomputable def pairConeFst (α : Bool)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    X.Edge (cond α (pairConeApex α c) x)
      (cond α x (pairConeApex α c)) :=
  leg (x := x) (y := y) α coprod.inl (z := x) (coprod.inl_desc _ _) c

noncomputable def pairConeSnd (α : Bool)
    (c : (coneObject α (pairDiagram x y)).Vertex) :
    X.Edge (cond α (pairConeApex α c) y)
      (cond α y (pairConeApex α c)) :=
  leg (x := x) (y := y) α coprod.inr (z := y) (coprod.inr_desc _ _) c

private theorem hom_ext_ev {T : DiagSet.{u}} {φ ψ : T ⟶ (grayHomRight intervalBoundary.{u}).obj X}
    (h₁ : φ ≫ ev X coprod.inl = ψ ≫ ev X coprod.inl)
    (h₂ : φ ≫ ev X coprod.inr = ψ ≫ ev X coprod.inr) : φ = ψ :=
  BinaryFan.IsLimit.hom_ext (isLimitGrayHomBoundaryFan X) h₁ h₂

private noncomputable def pairConeMap (f g : ball.{u} (atomSimplex 1) ⟶ X) :
    grayTensor (ball.{u} atomPoint) (ball.{u} (atomSimplex 1)) ⟶
      (grayHomRight intervalBoundary.{u}).obj X :=
  grayTensorSnd _ _ ≫ boundaryHom f g

private theorem pairConeMap_end {w : X.Vertex}
    {f₁ f₂ : ball.{u} (atomSimplex 1) ⟶ X} {g : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
    {i : ball.{u} atomPoint ⟶ intervalBoundary.{u}}
    {b : X ⟶ (grayHomRight intervalBoundary.{u}).obj X} {v : X.Vertex}
    (hf : g ≫ boundaryHom f₁ f₂ ≫ ev X i = vertexHom v)
    (hb : vertexHom w ≫ b ≫ ev X i = vertexHom v) :
    ((grayTensorLeft _).map g ≫ pairConeMap f₁ f₂) ≫ ev X i =
      (grayTensorFst _ _ ≫ vertexHom w ≫ b) ≫ ev X i := by
  simp only [pairConeMap, Category.assoc]
  rw [reassoc_of% grayTensorLeft_map_grayTensorSnd, grayTensorSnd_point, hf, hb]

private theorem pairConeMap_boundary (α : Bool) {w : X.Vertex}
    (f : X.Edge (cond α w x) (cond α x w))
    (g : X.Edge (cond α w y) (cond α y w)) :
    (grayTensorLeft _).map intervalBoundaryι ≫ pairConeMap (edgeHom f) (edgeHom g) =
      grayTensorBoundaryDesc _
        (grayTensorFst _ _ ≫ vertexHom w ≫ cond α (constDiagram intervalBoundary.{u} X)
          (isTerminalBallAtomPoint.from X ≫ diagramPoint (pairDiagram x y)))
        (grayTensorFst _ _ ≫ vertexHom w ≫ cond α
          (isTerminalBallAtomPoint.from X ≫ diagramPoint (pairDiagram x y))
          (constDiagram intervalBoundary.{u} X)) := by
  have hx : coprod.inl ≫ pairDiagram x y = vertexHom x := coprod.inl_desc _ _
  have hy : coprod.inr ≫ pairDiagram x y = vertexHom y := coprod.inr_desc _ _
  refine grayTensor_coprod_hom_ext _ ?_ ?_
  · rw [grayTensorBoundaryDesc_inl, ← Functor.map_comp_assoc, coprod.inl_desc]
    refine hom_ext_ev (pairConeMap_end (v := cond α w x) ?_ ?_)
      (pairConeMap_end (v := cond α w y) ?_ ?_)
    · exact (congrArg (intervalSource ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_fst _ _)).trans
        (intervalSource_comp_edgeHom f)
    · exact (congrArg (vertexHom w ≫ ·) (cond_comp_ev_source α _ hx)).trans
        (vertexHom_comp_cond α w x)
    · exact (congrArg (intervalSource ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_snd _ _)).trans
        (intervalSource_comp_edgeHom g)
    · exact (congrArg (vertexHom w ≫ ·) (cond_comp_ev_source α _ hy)).trans
        (vertexHom_comp_cond α w y)
  · rw [grayTensorBoundaryDesc_inr, ← Functor.map_comp_assoc, coprod.inr_desc]
    refine hom_ext_ev (pairConeMap_end (v := cond α x w) ?_ ?_)
      (pairConeMap_end (v := cond α y w) ?_ ?_)
    · exact (congrArg (intervalTarget ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_fst _ _)).trans
        (intervalTarget_comp_edgeHom f)
    · exact (congrArg (vertexHom w ≫ ·) (cond_comp_ev_target α _ hx)).trans
        (vertexHom_comp_cond' α w x)
    · exact (congrArg (intervalTarget ≫ ·) (boundaryHom_comp_grayHomBoundaryFan_snd _ _)).trans
        (intervalTarget_comp_edgeHom g)
    · exact (congrArg (vertexHom w ≫ ·) (cond_comp_ev_target α _ hy)).trans
        (vertexHom_comp_cond' α w y)

theorem exists_pairCone_of_edges (α : Bool) {w : X.Vertex}
    (f : X.Edge (cond α w x) (cond α x w))
    (g : X.Edge (cond α w y) (cond α y w)) :
    ∃ c : (coneObject α (pairDiagram x y)).Vertex, ∃ _ : pairConeApex α c = w,
      (pairConeFst α c).cell = f.cell ∧ (pairConeSnd α c).cell = g.cell := by
  set Φ := (coneObjectHomEquiv α (pairDiagram x y) (ball.{u} atomPoint)).symm
    ⟨(vertexHom w, pairConeMap (edgeHom f) (edgeHom g)), pairConeMap_boundary α f g⟩
  have hΦ := Equiv.apply_symm_apply (coneObjectHomEquiv α (pairDiagram x y) (ball.{u} atomPoint))
    ⟨(vertexHom w, pairConeMap (edgeHom f) (edgeHom g)), pairConeMap_boundary α f g⟩
  set t : (coneObject α (pairDiagram x y)).Vertex :=
    uliftYonedaEquiv (X := atomPoint) (F := coneObject α (pairDiagram x y)) Φ
  have hc : vertexHom t = Φ := vertexHom_uliftYonedaEquiv Φ
  have hm : coneMap α (pairDiagram x y) (vertexHom t) =
      pairConeMap (edgeHom f) (edgeHom g) := by
    rw [hc]
    exact congrArg (fun p => p.1.2) hΦ
  have hl (i : ball.{u} atomPoint ⟶ intervalBoundary.{u}) :
      legHom α i t = boundaryHom (edgeHom f) (edgeHom g) ≫ ev X i := by
    rw [legHom, hm, pairConeMap, Category.assoc, IsIso.inv_hom_id_assoc]
  refine ⟨t, vertexHom_injective ?_, ?_, ?_⟩
  · exact (vertexHom_comp t _).symm.trans
      ((congrArg (· ≫ coneObjectπ α _) hc).trans (congrArg (fun p => p.1.1) hΦ))
  · apply cell_eq_of_edgeHom_eq
    simpa only [pairConeFst, leg, edgeHom_edgeOfHom] using
      (hl coprod.inl).trans (boundaryHom_comp_grayHomBoundaryFan_fst _ _)
  · apply cell_eq_of_edgeHom_eq
    simpa only [pairConeSnd, leg, edgeHom_edgeOfHom] using
      (hl coprod.inr).trans (boundaryHom_comp_grayHomBoundaryFan_snd _ _)

private theorem homMk_comp_homMk_eq_of_square (hX : IsInftyCategory 1 X)
    (G : grayTensor (ball.{u} (atomSimplex 1)) (ball.{u} (atomSimplex 1)) ⟶ X)
    {p q r s : X.Vertex} (a : X.Edge p q) (b : X.Edge q r)
    (a' : X.Edge p s) (b' : X.Edge s r)
    (ha : edgeHom a = inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalSource ≫ G)
    (hb : edgeHom b = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalTarget ≫ G)
    (ha' : edgeHom a' = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalSource ≫ G)
    (hb' : edgeHom b' = inv (grayTensorSnd (ball.{u} atomPoint) _) ≫
      (grayTensorRight _).map intervalTarget ≫ G) :
    HomotopyCategory.homMk hX.1 (a) ≫
        HomotopyCategory.homMk hX.1 (b) =
      HomotopyCategory.homMk hX.1 (a') ≫
        HomotopyCategory.homMk hX.1 (b') := by
  have h := congrArg (OneTruncation.toHomotopyCategory hX).map
    (OneTruncation.globeHomMk_comp_globeHomMk_eq_of_square G a b a' b' ha hb ha' hb')
  exact (congrArg₂ (· ≫ ·)
    (OneTruncation.toHomotopyCategory_map_globeHomMk hX a).symm
    (OneTruncation.toHomotopyCategory_map_globeHomMk hX b).symm).trans
      (((OneTruncation.toHomotopyCategory hX).map_comp _ _).symm.trans (h.trans
        (((OneTruncation.toHomotopyCategory hX).map_comp _ _).trans (congrArg₂ (· ≫ ·)
          (OneTruncation.toHomotopyCategory_map_globeHomMk hX a')
          (OneTruncation.toHomotopyCategory_map_globeHomMk hX b')))))

private theorem side_coneMap {α : Bool} (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    (Ψ : ball.{u} (atomSimplex 1) ⟶ coneObject α (pairDiagram x y))
    {e : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)}
    {v : (coneObject α (pairDiagram x y)).Vertex} (hv : e ≫ Ψ = vertexHom v) :
    inv (grayTensorSnd (ball.{u} atomPoint) _) ≫ (grayTensorRight _).map e ≫
      coneMap α (pairDiagram x y) Ψ ≫ ev X i = legHom α i v := by
  rw [← Category.assoc ((grayTensorRight _).map e), ← coneMap_comp, hv, legHom]

private theorem side_coneMap_source (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z)
    (Ψ : ball.{u} (atomSimplex 1) ⟶ coneObject α (pairDiagram x y)) :
    inv (grayTensorFst _ (ball.{u} atomPoint)) ≫ (grayTensorLeft _).map intervalSource ≫
      coneMap α (pairDiagram x y) Ψ ≫ ev X i =
        Ψ ≫ coneObjectπ α _ ≫ cond α (𝟙 X) (isTerminalBallAtomPoint.from X ≫ vertexHom z) := by
  rw [← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_intervalSource_coneMap,
    Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc,
    cond_comp_ev_source α i hz]

private theorem side_coneMap_target (α : Bool) (i : ball.{u} atomPoint ⟶ intervalBoundary.{u})
    {z : X.Vertex} (hz : i ≫ pairDiagram x y = vertexHom z)
    (Ψ : ball.{u} (atomSimplex 1) ⟶ coneObject α (pairDiagram x y)) :
    inv (grayTensorFst _ (ball.{u} atomPoint)) ≫ (grayTensorLeft _).map intervalTarget ≫
      coneMap α (pairDiagram x y) Ψ ≫ ev X i =
        Ψ ≫ coneObjectπ α _ ≫ cond α (isTerminalBallAtomPoint.from X ≫ vertexHom z) (𝟙 X) := by
  rw [← Category.assoc ((grayTensorLeft _).map _), grayTensorLeft_map_intervalTarget_coneMap,
    Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc,
    cond_comp_ev_target α i hz]

private def condEdge (α : Bool) {p q p' q' : X.Vertex} (e : X.Edge p q)
    (e' : X.Edge p' q') : X.Edge (cond α p p') (cond α q q') :=
  match α with | true => e | false => e'

private theorem edgeHom_condEdge (α : Bool) {p q p' q' : X.Vertex} (e : X.Edge p q)
    (e' : X.Edge p' q') :
    edgeHom (condEdge α e e') = cond α (edgeHom e) (edgeHom e') := by
  cases α <;> rfl

private theorem homMk_leg (α : Bool) (hX : IsInftyCategory 1 X)
    (i : ball.{u} atomPoint ⟶ intervalBoundary.{u}) {z : X.Vertex}
    (hz : i ≫ pairDiagram x y = vertexHom z) {v w : (coneObject α (pairDiagram x y)).Vertex}
    (E : (coneObject α (pairDiagram x y)).Edge v w) :
    HomotopyCategory.homMk hX.1 (leg α i hz v) ≫
        HomotopyCategory.homMk hX.1
          (condEdge α (DiagSet.Edge.id z) (E.map (coneObjectπ α _))) =
      HomotopyCategory.homMk hX.1
          (condEdge α (E.map (coneObjectπ α _)) (DiagSet.Edge.id z)) ≫
        HomotopyCategory.homMk hX.1 (leg α i hz w) := by
  let a := condEdge α (E.map (coneObjectπ α _)) (DiagSet.Edge.id z)
  let b := condEdge α (DiagSet.Edge.id z) (E.map (coneObjectπ α _))
  have ha : edgeHom a = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalSource ≫ coneMap α _ (edgeHom E) ≫ ev X i := by
    dsimp only [a]
    rw [edgeHom_condEdge, edgeHom_map, edgeHom_id, side_coneMap_source α i hz]
    clear a b
    cases α
    · simp only [Bool.cond_false, ← Category.assoc]
      exact congrArg (· ≫ vertexHom z) (isTerminalBallAtomPoint.hom_ext _ _)
    · exact (Category.comp_id _).symm
  have hb : edgeHom b = inv (grayTensorFst _ (ball.{u} atomPoint)) ≫
      (grayTensorLeft _).map intervalTarget ≫ coneMap α _ (edgeHom E) ≫ ev X i := by
    dsimp only [b]
    rw [edgeHom_condEdge, edgeHom_id, edgeHom_map, side_coneMap_target α i hz]
    clear ha a b
    cases α
    · exact (Category.comp_id _).symm
    · simp only [Bool.cond_true, ← Category.assoc]
      exact congrArg (· ≫ vertexHom z) (isTerminalBallAtomPoint.hom_ext _ _)
  have h := homMk_comp_homMk_eq_of_square hX (coneMap α _ (edgeHom E) ≫ ev X i)
    (leg α i hz v) b a (leg α i hz w)
    (by
      dsimp only [leg]
      exact (edgeHom_edgeOfHom _ _ _).trans
        (side_coneMap i _ (intervalSource_comp_edgeHom E)).symm)
    hb ha
    (by
      dsimp only [leg]
      exact (edgeHom_edgeOfHom _ _ _).trans
        (side_coneMap i _ (intervalTarget_comp_edgeHom E)).symm)
  exact h

private noncomputable def homEdge {α : Bool} {v w : (coneObject α (pairDiagram x y)).Vertex}
    (φ : (bipointedHom.obj ((coneObject α (pairDiagram x y)).bipoint v w)).Vertex) :
    (coneObject α (pairDiagram x y)).Edge v w :=
  DiagSet.bipointedHomVerticesEquiv _ _ φ

private theorem nonempty_homEdge (α : Bool) (hX : IsInftyCategory 1 X)
    {c : (coneObject α (pairDiagram x y)).Vertex} (hc : IsProductCone α x y c)
    (t : (coneObject α (pairDiagram x y)).Vertex) :
    Nonempty ((coneObject α (pairDiagram x y)).Edge (cond α t c) (cond α c t)) := by
  obtain ⟨φ⟩ := (hc t).nonempty_vertex
    (isFibrant_bipointedHom (isInftyCategory_coneObject α _ hX))
  exact ⟨homEdge φ⟩

private theorem mediator_factor (α : Bool) (hcomp : HasWeakComposites X)
    (hX : IsInftyCategory 1 X)
    (t c : (coneObject α (pairDiagram x y)).Vertex)
    (E : (coneObject α (pairDiagram x y)).Edge (cond α t c) (cond α c t))
    (i : ball.{u} atomPoint ⟶ intervalBoundary.{u}) {z : X.Vertex}
    (hz : i ≫ pairDiagram x y = vertexHom z)
    (e : X.Edge (cond α (pairConeApex α t) z) (cond α z (pairConeApex α t)))
    (he : (leg α i hz t).cell = e.cell) :
    match (generalizing := false) α, c, t, E, e with
    | true, c, _, E, e =>
      HomotopyCategory.homMk hcomp (E.map (coneObjectπ true (pairDiagram x y))) ≫
        HomotopyCategory.homMk hcomp (leg true i hz c) =
        HomotopyCategory.homMk hcomp e
    | false, c, _, E, e =>
      HomotopyCategory.homMk hcomp (leg false i hz c) ≫
        HomotopyCategory.homMk hcomp (E.map (coneObjectπ false (pairDiagram x y))) =
        HomotopyCategory.homMk hcomp e := by
  have heq := DiagSet.Edge.ext he
  subst e
  have hs :
      HomotopyCategory.homMk hcomp (leg α i hz (cond α t c)) ≫
        HomotopyCategory.homMk hcomp
          (condEdge α (DiagSet.Edge.id z) (E.map (coneObjectπ α (pairDiagram x y)))) =
      HomotopyCategory.homMk hcomp
          (condEdge α (E.map (coneObjectπ α (pairDiagram x y))) (DiagSet.Edge.id z)) ≫
        HomotopyCategory.homMk hcomp (leg α i hz (cond α c t)) :=
    homMk_leg α hX i hz E
  cases α
  · exact hs.trans ((congrArg (· ≫ _) (HomotopyCategory.homMk_id hcomp z)).trans
      (Category.id_comp _))
  · exact hs.symm.trans ((congrArg (_ ≫ ·) (HomotopyCategory.homMk_id hcomp z)).trans
      (Category.comp_id _))

private theorem exists_mediator_of_cone_edge (α : Bool) (hX : IsInftyCategory 1 X)
    (t c : (coneObject α (pairDiagram x y)).Vertex)
    (E : (coneObject α (pairDiagram x y)).Edge (cond α t c) (cond α c t))
    (f : X.Edge (cond α (pairConeApex α t) x) (cond α x (pairConeApex α t)))
    (g : X.Edge (cond α (pairConeApex α t) y) (cond α y (pairConeApex α t)))
    (hf : (pairConeFst α t).cell = f.cell)
    (hg : (pairConeSnd α t).cell = g.cell) :
    ∃ h : (⟨cond α (pairConeApex α t) (pairConeApex α c)⟩ : HomotopyCategory X hX.1) ⟶
        ⟨cond α (pairConeApex α c) (pairConeApex α t)⟩,
      match (generalizing := false) α, c, t, f, g, h with
      | true, c, _, f, g, h =>
        h ≫ HomotopyCategory.homMk hX.1 (pairConeFst true c) =
          HomotopyCategory.homMk hX.1 f ∧
        h ≫ HomotopyCategory.homMk hX.1 (pairConeSnd true c) =
          HomotopyCategory.homMk hX.1 g
      | false, c, _, f, g, h =>
        HomotopyCategory.homMk hX.1 (pairConeFst false c) ≫ h =
          HomotopyCategory.homMk hX.1 f ∧
        HomotopyCategory.homMk hX.1 (pairConeSnd false c) ≫ h =
          HomotopyCategory.homMk hX.1 g := by
  have hcomp : HasWeakComposites X := hX.1
  cases α <;> exact ⟨_,
    mediator_factor _ hcomp hX t c E coprod.inl (coprod.inl_desc _ _) f hf,
    mediator_factor _ hcomp hX t c E coprod.inr (coprod.inr_desc _ _) g hg⟩

private theorem exists_mediator_of_edges (α : Bool) (hX : IsInftyCategory 1 X)
    {c : (coneObject α (pairDiagram x y)).Vertex} (hc : IsProductCone α x y c)
    {w : X.Vertex} (f : X.Edge (cond α w x) (cond α x w))
    (g : X.Edge (cond α w y) (cond α y w)) :
    ∃ h : (⟨cond α w (pairConeApex α c)⟩ : HomotopyCategory X hX.1) ⟶
        ⟨cond α (pairConeApex α c) w⟩,
      match (generalizing := false) α, c, w, f, g, h with
      | true, c, _, f, g, h =>
        h ≫ HomotopyCategory.homMk hX.1 (pairConeFst true c) =
          HomotopyCategory.homMk hX.1 f ∧
        h ≫ HomotopyCategory.homMk hX.1 (pairConeSnd true c) =
          HomotopyCategory.homMk hX.1 g
      | false, c, _, f, g, h =>
        HomotopyCategory.homMk hX.1 (pairConeFst false c) ≫ h =
          HomotopyCategory.homMk hX.1 f ∧
        HomotopyCategory.homMk hX.1 (pairConeSnd false c) ≫ h =
          HomotopyCategory.homMk hX.1 g := by
  obtain ⟨t, rfl, hf, hg⟩ := exists_pairCone_of_edges α f g
  obtain ⟨E⟩ := nonempty_homEdge α hX hc t
  cases α <;> exact exists_mediator_of_cone_edge _ hX t c E f g hf hg

theorem DiagSet.exists_lift_of_isProductCone (hX : IsInftyCategory 1 X)
    {c : (coneObject true (pairDiagram x y)).Vertex}
    (hc : IsProductCone true x y c) (w : X.Vertex)
    (f : (⟨w⟩ : HomotopyCategory X hX.1) ⟶ ⟨x⟩)
    (g : (⟨w⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩) :
    ∃ h : (⟨w⟩ : HomotopyCategory X hX.1) ⟶
        ⟨pairConeApex true c⟩,
      h ≫ HomotopyCategory.homMk hX.1 (pairConeFst true c) = f ∧
        h ≫ HomotopyCategory.homMk hX.1 (pairConeSnd true c) = g := by
  obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 f
  obtain ⟨g, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 g
  exact exists_mediator_of_edges true hX hc f g

theorem DiagSet.exists_desc_of_isProductCone (hX : IsInftyCategory 1 X)
    {c : (coneObject false (pairDiagram x y)).Vertex}
    (hc : IsProductCone false x y c) (w : X.Vertex)
    (f : (⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨w⟩)
    (g : (⟨y⟩ : HomotopyCategory X hX.1) ⟶ ⟨w⟩) :
    ∃ h : (⟨pairConeApex false c⟩ : HomotopyCategory X hX.1) ⟶
        ⟨w⟩,
      HomotopyCategory.homMk hX.1 (pairConeFst false c) ≫ h = f ∧
        HomotopyCategory.homMk hX.1 (pairConeSnd false c) ≫ h = g := by
  obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 f
  obtain ⟨g, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 g
  exact exists_mediator_of_edges false hX hc f g

end Atoms.Diagrammatic
