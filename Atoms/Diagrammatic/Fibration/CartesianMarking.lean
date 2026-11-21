import Atoms.Diagrammatic.Fibration.RightFibrationCartesian
import Atoms.Diagrammatic.Marked.Basic
import Atoms.Shape.Rigidity

open CategoryTheory Limits Opposite HomotopicalAlgebra Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

variable {E S : DiagSet.{u}}

abbrev DiagSet.Edge.ofCell (c : diagram E (atomGlobe 1)) :
    E.Edge (E.map (atomGlobeVertex false).op c) (E.map (atomGlobeVertex true).op c) :=
  ⟨c, rfl, rfl⟩

theorem DiagSet.exists_id_cell_eq_of_isDegenerate {X : DiagSet.{u}}
    {c : diagram X (atomGlobe 1)} (hc : IsDegenerate X c) :
    ∃ v : X.Vertex, (DiagSet.Edge.id v).cell = c := by
  obtain ⟨V, q, y, hq, hni, rfl⟩ := hc
  have hle := dimension_le_of_isCollapseHom q hq
  rw [dimension_atomGlobe] at hle
  have hV : V.dimension = 0 := by
    by_contra h
    exact hni (isIso_of_isCollapseHom_of_dimension_eq q hq
      (by rw [dimension_atomGlobe]; omega))
  have := isIso_toAtomPoint_of_dimension_eq_zero hV
  refine ⟨X.map (inv (toAtomPoint V)).op y, ?_⟩
  have hq' : toAtomPoint (atomGlobe 1) ≫ inv (toAtomPoint V) = q :=
    (IsIso.comp_inv_eq _).2 (isTerminalAtomPoint.hom_ext _ _)
  rw [DiagSet.Edge.id_cell, ← X.map_comp_apply, ← op_comp, hq']

def DiagSet.IsCartesianCell (p : E ⟶ S) {U : Atom} (x : diagram E U) : Prop :=
  ∃ e : atomGlobe 1 ≅ U, DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (E.map e.hom.op x))

theorem DiagSet.isCartesianCell_iff_isCartesianEdge (p : E ⟶ S) {x y : E.Vertex}
    (e : E.Edge x y) : DiagSet.IsCartesianCell p e.cell ↔ DiagSet.IsCartesianEdge p e := by
  have h (i : atomGlobe 1 ≅ atomGlobe 1) : E.map i.hom.op e.cell = e.cell := by
    rw [Atom.iso_eq i (Iso.refl _), Iso.refl_hom, op_id, E.map_id_apply]
  exact ⟨fun ⟨i, hi⟩ ↦ (DiagSet.isCartesianEdge_congr p (h i)).1 hi,
    fun he ↦ ⟨Iso.refl _, (DiagSet.isCartesianEdge_congr p (h _)).2 he⟩⟩

theorem DiagSet.isCartesianCell_map_iso_iff (p : E ⟶ S) {U V : Atom} (e : U ≅ V)
    (x : diagram E V) :
    DiagSet.IsCartesianCell p (E.map e.hom.op x) ↔ DiagSet.IsCartesianCell p x := by
  constructor
  · rintro ⟨i, hi⟩
    have h : E.map i.hom.op (E.map e.hom.op x) = E.map (i ≪≫ e).hom.op x :=
      (E.map_comp_apply e.hom.op i.hom.op x).symm
    exact ⟨i ≪≫ e, (DiagSet.isCartesianEdge_congr p h).1 hi⟩
  · rintro ⟨i, hi⟩
    have h : E.map i.hom.op x = E.map (i ≪≫ e.symm).hom.op (E.map e.hom.op x) := by
      rw [← E.map_comp_apply, ← op_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        e.inv_hom_id, Category.comp_id]
    exact ⟨i ≪≫ e.symm, (DiagSet.isCartesianEdge_congr p h).1 hi⟩

def DiagSet.cartesianMarking (p : E ⟶ S) : MarkedPresheaf.Marking atomMarking E where
  marked U := {x | IsDegenerate E x ∨ 1 < U.dimension ∨ DiagSet.IsCartesianCell p x}
  markable U x hx := by
    rcases hx with hx | hx | ⟨e, -⟩
    · exact dimension_pos_of_isDegenerate hx
    · exact lt_trans Nat.zero_lt_one hx
    · exact (congrArg (0 < ·) (Atom.dimension_eq_of_iso e)).mp
        (by rw [dimension_atomGlobe]; exact Nat.one_pos)
  degenerate _ b q hq y := Or.inl ⟨b, q, y, hq.1, hq.2, rfl⟩
  transport _ _ e x := or_congr (isDegenerate_map_iso_iff e x).symm
    (or_congr (Iff.of_eq (congrArg (1 < ·) (Atom.dimension_eq_of_iso e).symm))
      (DiagSet.isCartesianCell_map_iso_iff p e x).symm)

def DiagSet.cartesianMarked (p : E ⟶ S) : MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking E (DiagSet.cartesianMarking p)

@[simp] theorem DiagSet.mem_marked_cartesianMarked (p : E ⟶ S) (U : Atom) (x : diagram E U) :
    x ∈ (DiagSet.cartesianMarked p).marked U ↔
      IsDegenerate E x ∨ 1 < U.dimension ∨ DiagSet.IsCartesianCell p x :=
  MarkedPresheaf.mem_marked_ofMarking _ _ _ _

theorem DiagSet.mem_marked_cartesianMarked_edge_iff (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {x y : E.Vertex} (e : E.Edge x y) :
    e.cell ∈ (DiagSet.cartesianMarked p).marked (atomGlobe 1) ↔
      DiagSet.IsCartesianEdge p e := by
  rw [DiagSet.mem_marked_cartesianMarked, dimension_atomGlobe]
  constructor
  · rintro (hd | hd | hc)
    · obtain ⟨v, hv⟩ := DiagSet.exists_id_cell_eq_of_isDegenerate hd
      exact (DiagSet.isCartesianEdge_congr p hv).1 (DiagSet.isCartesianEdge_id v)
    · omega
    · exact (DiagSet.isCartesianCell_iff_isCartesianEdge p e).1 hc
  · exact fun he ↦ Or.inr (Or.inr ((DiagSet.isCartesianCell_iff_isCartesianEdge p e).2 he))

theorem DiagSet.mem_marked_cartesianMarked_of_isEquivalence (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] {U : Atom}
    {c : diagram E U} (hc : IsEquivalence E c) : c ∈ (DiagSet.cartesianMarked p).marked U := by
  refine (DiagSet.mem_marked_cartesianMarked p U c).2 ?_
  have hU : 0 < U.dimension :=
    Nat.pos_of_ne_zero fun h0 ↦ not_isEquivalence_of_dimension_eq_zero c h0 hc
  rcases Nat.lt_or_ge 1 U.dimension with hlt | hle
  · exact Or.inr (Or.inl hlt)
  obtain ⟨i⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one (le_antisymm hle hU)
  exact Or.inr (Or.inr ⟨i, DiagSet.isCartesianEdge_of_isEquivalence
    (DiagSet.Edge.ofCell (E.map i.hom.op c)) ((isEquivalence_map_iso_iff i c).2 hc)⟩)

noncomputable def DiagSet.cartesianMarkedHom (p : E ⟶ S) :
    DiagSet.cartesianMarked p ⟶ (MarkedPresheaf.sharp atomMarking).obj S :=
  MarkedPresheaf.homMk (X := DiagSet.cartesianMarked p) p fun U x hx ↦
    (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 ((DiagSet.cartesianMarked p).markable U x hx)

@[simp] theorem DiagSet.forget_map_cartesianMarkedHom (p : E ⟶ S) :
    MarkedPresheaf.forget.map (DiagSet.cartesianMarkedHom p) = p :=
  rfl

noncomputable abbrev DiagSet.sliceAt (S : DiagSet.{u}) (b : S.Vertex) : DiagSet.{u} :=
  (WithInitial.slice (ball.{u} atomPoint)).obj (Under.mk (uliftYonedaEquiv.symm b))

noncomputable abbrev DiagSet.sliceAtProj (S : DiagSet.{u}) (b : S.Vertex) : S.sliceAt b ⟶ S :=
  (sliceProj (ball.{u} atomPoint)).app (Under.mk (uliftYonedaEquiv.symm b))

noncomputable def DiagSet.sliceAtId (S : DiagSet.{u}) (b : S.Vertex) :
    ball.{u} atomPoint ⟶ S.sliceAt b :=
  (WithInitial.joinRightUnderAdjunction (ball.{u} atomPoint)).homEquiv (ball.{u} atomPoint)
    (Under.mk (uliftYonedaEquiv.symm b))
    (Under.homMk (isTerminalBallAtomPoint.from _ ≫ uliftYonedaEquiv.symm b)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uliftYonedaEquiv.symm b)
        (isTerminalBallAtomPoint.hom_ext _ (𝟙 _))).trans (Category.id_comp _))))

@[reassoc (attr := simp)]
theorem DiagSet.sliceAtId_comp_sliceAtProj (S : DiagSet.{u}) (b : S.Vertex) :
    S.sliceAtId b ≫ S.sliceAtProj b = uliftYonedaEquiv.symm b := by
  let adj := WithInitial.joinRightUnderAdjunction (ball.{u} atomPoint)
  let g : (WithInitial.joinRightUnder (ball.{u} atomPoint)).obj (ball.{u} atomPoint) ⟶
      Under.mk (uliftYonedaEquiv.symm b) :=
    Under.homMk (isTerminalBallAtomPoint.from _ ≫ uliftYonedaEquiv.symm b)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uliftYonedaEquiv.symm b)
        (isTerminalBallAtomPoint.hom_ext _ (𝟙 _))).trans (Category.id_comp _)))
  have h : (WithInitial.joinRightUnder (ball.{u} atomPoint)).map (adj.homEquiv _ _ g) ≫
      adj.counit.app _ = g :=
    (adj.homEquiv_counit _ _ (adj.homEquiv _ _ g)).symm.trans (Equiv.symm_apply_apply _ g)
  rw [DiagSet.sliceAtProj, sliceProj_app_eq]
  refine (WithInitial.joinInclLeft_comp_joinMap_assoc (adj.homEquiv _ _ g)
    (𝟙 (ball.{u} atomPoint)) _).symm.trans ?_
  refine (congrArg (fun k : _ ⟶ Under.mk (uliftYonedaEquiv.symm b) ↦
    WithInitial.joinInclLeft _ _ ≫ k.right) h).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uliftYonedaEquiv.symm b)
    (isTerminalBallAtomPoint.hom_ext _ (𝟙 _))).trans (Category.id_comp _))

theorem DiagSet.isCartesianEdge_sliceAtProj [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (b : S.Vertex) {x y : (S.sliceAt b).Vertex} (e : (S.sliceAt b).Edge x y) :
    DiagSet.IsCartesianEdge (S.sliceAtProj b) e :=
  have h : DiagSet.IsRightFibration (S.sliceAtProj b) :=
    DiagSet.isRightFibration_sliceProj (uliftYonedaEquiv.symm b)
  have : Fibration ((DiagSet.toInfty 1).map (S.sliceAtProj b)) := h.fibration
  ((DiagSet.isRightFibration_iff_isCartesianFibration_and_forall (S.sliceAtProj b)).1 h).2 e

end Atoms.Diagrammatic
