import Atoms.Diagrammatic.Marked.Composite
import Atoms.Diagrammatic.Marked.HornEquation
import Atoms.Diagrammatic.Context.Division

open Atoms.Molecule Atoms.Molecule.OGP Order
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

variable (m : MarkedHornData) {Y : DiagSet.{u}}

theorem exists_sphere_extension (w : realize.obj m.hornRDC ⟶ Y) (a : diagram Y m.faceAtom)
    (ha : realize.map (m.faceAtom.toMoleculeShape.rdc.restrictIncl (m.faceAtom.ogp.bdryFull ⊤)) ≫
        (ofCell a).map =
      realize.map (RDCpx.ofInclusion
        (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
        (Q := m.hornRDC) m.faceSphere) ≫ w) :
    ∃ σ : realize.obj (m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) ⟶ Y,
      realize.map (RDCpx.inclusion m.atom.toMoleculeShape.rdc m.hornSet_subset_bdryFull) ≫ σ =
        w ∧
      realize.map (RDCpx.ofInclusion (P := m.faceAtom.toMoleculeShape.rdc)
        (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.faceToSphere) ≫
        σ = (ofCell a).map := by
  have hcd : ∀ y, m.hornToSphere (m.faceSphere y) =
      m.faceToSphere (incl (m.faceAtom.ogp.bdryFull ⊤) y) := fun _ => rfl
  have hab : CoverCompatible (R := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤))
      (U := m.hornRDC) (V := m.faceAtom.toMoleculeShape.rdc) m.hornToSphere m.faceToSphere w
      (ofCell a).map :=
    coverCompatible_of_emb (R := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤))
      (U := m.hornRDC) (V := m.faceAtom.toMoleculeShape.rdc)
      m.hornToSphere m.faceToSphere w (ofCell a).map
      (C := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
      m.faceSphere (incl (m.faceAtom.ogp.bdryFull ⊤)) hcd m.image_faceSphere_comp ha.symm
  have hinc : RDCpx.ofInclusion (P := m.hornRDC)
      (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.hornToSphere =
      RDCpx.inclusion m.atom.toMoleculeShape.rdc m.hornSet_subset_bdryFull := by
    ext
    rfl
  refine ⟨coverDesc (R := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤))
      (U := m.hornRDC) (V := m.faceAtom.toMoleculeShape.rdc) m.hornToSphere m.faceToSphere
      m.hornToSphere_cover w (ofCell a).map hab, ?_,
    ofInclusion_coverDesc_right (R := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤))
      (U := m.hornRDC) (V := m.faceAtom.toMoleculeShape.rdc) m.hornToSphere m.faceToSphere
      m.hornToSphere_cover w _ hab⟩
  rw [← hinc]
  exact ofInclusion_coverDesc_left
    (R := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) (U := m.hornRDC)
    (V := m.faceAtom.toMoleculeShape.rdc) m.hornToSphere m.faceToSphere m.hornToSphere_cover w _ hab

theorem frames_inclusion [∀ i, DecidablePred (· ∈ m.left i)]
    [∀ i, DecidablePred (· ∈ m.right i)] {S T : LowerSet m.atom.ogp} (hST : S ≤ T)
    (v : realize.obj (m.atom.toMoleculeShape.rdc.restrict T) ⟶ Y) (hΛS : m.hornSet ≤ S) :
    m.frames (realize.map (RDCpx.inclusion m.atom.toMoleculeShape.rdc hST) ≫ v) hΛS =
      m.frames v (hΛS.trans hST) :=
  congrArg List.ofFn (funext fun i => Prod.ext
    (restrictAlong_inclusion hST v _ _ ((MoleculeShape.map_subIncl_top _ _).le.trans
      ((le_sup_left.trans (m.left_union_right_subset_hornSet i.isLt)).trans hΛS)))
    (restrictAlong_inclusion hST v _ _ ((MoleculeShape.map_subIncl_top _ _).le.trans
      ((le_sup_right.trans (m.left_union_right_subset_hornSet i.isLt)).trans hΛS))))

theorem sphereBoundary_faceSphere (hk : 2 ≤ m.atom.dimension) (w : realize.obj m.hornRDC ⟶ Y)
    (hA : 0 < m.faceAtom.dimension) (β : Bool) :
    (sphereBoundary m.faceAtom hA (realize.map (RDCpx.ofInclusion
        (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
        (Q := m.hornRDC) m.faceSphere) ≫ w) β).Equiv
      (m.faceBoundary hk w β).toPastingDiagram := by
  have hdA := m.dimension_faceAtom_add_one
  have hmem : map (m.faceAtom.toMoleculeShape.boundaryIncl (m.faceAtom.dimension - 1) β ≫
      m.faceEmb) ⊤ ≤ m.hornSet := by
    rintro _ ⟨a, -, rfl⟩
    exact m.faceEmb_mem_hornSet ((m.faceAtom.toMoleculeShape.map_boundaryIncl_eq_bdry
      (by omega : m.faceAtom.dimension = _) β).le.trans (bdry_le_bdryFull ⊤ β)
        ⟨a, LowerSet.mem_top, rfl⟩)
  have e : sphereBoundary m.faceAtom hA (realize.map (RDCpx.ofInclusion
        (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
        (Q := m.hornRDC) m.faceSphere) ≫ w) β =
      restrictAlong w _ (m.faceAtom.toMoleculeShape.boundaryIncl (m.faceAtom.dimension - 1) β ≫
        m.faceEmb) hmem :=
    restrictAlong_realize_map_comp _ w _ _ _ _ _ fun _ => rfl
  rw [e]
  refine equiv_restrictAlong_of_image_eq w _ _ _ ((MoleculeShape.map_subIncl_top _ _).le.trans
    (m.boundary_closure_face_subset_hornSet (by have := m.dim_face_add_one; omega) β)) ?_
  rw [map_comp, MoleculeShape.map_boundaryIncl_top, map_boundary, m.image_faceEmb,
    MoleculeShape.map_subIncl_top, show m.faceAtom.dimension - 1 = m.atom.dimension - 2 by omega]

theorem oppBoundary_mem_equivalences (w : realize.obj m.hornRDC ⟶ Y)
    (hw : m.MarksHorn (MarkedDiagSet.natural.obj Y) w)
    (hsub : m.atom.ogp.faces (!m.side) m.atom.top ⊆ m.marking) :
    m.oppBoundary w ∈ equivalences Y := by
  have hbo : IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ (!m.side)) := m.isMoleculeIn_bdry (!m.side)
  have hdb : (m.oppBoundary w).dim = m.atom.dimension - 1 := by
    have h := m.atom.toMoleculeShape.dimension_sub hbo
    rw [m.atom.isMolecule.krullDim_bdry (n := m.atom.dimension - 1) (by
      rw [LowerSet.krullDim_top, m.atom.krullDim_eq_dimension, Nat.sub_add_cancel m.positive])]
      at h
    exact_mod_cast h
  have hf := m.dim_face_pos_of_faceSet_subset hsub
  have hdf := m.dim_face_add_one
  refine mem_equivalences_of_forall_cellAt _ (by omega) fun t ht => ?_
  let ι : (m.atom.toMoleculeShape.sub hbo).ogp ⟶ m.atom.ogp.restrict m.hornSet :=
    codRestrict (m.atom.toMoleculeShape.subIncl hbo) m.hornSet fun a =>
      m.bdry_not_subset_hornSet
        ((m.atom.toMoleculeShape.map_subIncl_top hbo).le ⟨a, LowerSet.mem_top, rfl⟩)
  have hι : IsInclusion ι := inferInstanceAs (IsInclusion (codRestrict
    (m.atom.toMoleculeShape.subIncl hbo) m.hornSet fun a => m.bdry_not_subset_hornSet
      ((m.atom.toMoleculeShape.map_subIncl_top hbo).le ⟨a, LowerSet.mem_top, rfl⟩)))
  let c : atomToRDCpx.obj (principalAtomRDC (m.oppBoundary w).shape.rdc t) ⟶ m.hornRDC :=
    principalInclusionRDC (m.oppBoundary w).shape.rdc t ≫
      @RDCpx.ofInclusion (m.oppBoundary w).shape.rdc m.hornRDC ι hι
  have hc : Function.Injective fun s => (ConcreteCategory.hom c.hom s).1 := fun s s' h =>
    injective_principalInclusionRDC (m.oppBoundary w).shape.rdc t
      (IsInclusion.injective (f := m.atom.toMoleculeShape.subIncl hbo) h)
  have hd1 : grade ℕ (m.atom.toMoleculeShape.subIncl hbo t) = grade ℕ t :=
    (isMorphism (m.atom.toMoleculeShape.subIncl hbo)).grade_eq t
  have hmem : (ConcreteCategory.hom c.hom (principalAtomRDC (m.oppBoundary w).shape.rdc t).top).1 ∈
      m.marking := by
    change m.atom.toMoleculeShape.subIncl hbo
      (ConcreteCategory.hom (principalInclusionRDC (m.oppBoundary w).shape.rdc t).hom _) ∈ m.marking
    rw [principalInclusionRDC_top (m.oppBoundary w).shape.rdc t]
    have hdU := m.atom.dimension_eq
    have hy : m.atom.toMoleculeShape.subIncl hbo t ∈ m.atom.ogp.bdry (LowerSet.Iic m.atom.top)
        (!m.side) := by
      rw [m.atom.Iic_top]
      exact (m.atom.toMoleculeShape.map_subIncl_top hbo).le ⟨t, LowerSet.mem_top, rfl⟩
    exact hsub (mem_faces_of_mem_bdry_Iic hy (by omega))
  exact (MarkedDiagSet.mem_marked_natural_iff Y _ _).1
    (m.marked_app_of_marksHorn (X := MarkedDiagSet.natural.obj Y) w hw c hc hmem)

theorem exists_fills_natural_of_two_le (hY : HasWeakComposites Y)
    (hk : 2 ≤ m.atom.dimension) (w : realize.obj m.hornRDC ⟶ Y)
    (hw : m.MarksHorn (MarkedDiagSet.natural.obj Y) w) :
    ∃ z, m.Fills (MarkedDiagSet.natural.obj Y) w z := by
  classical
  have hdA := m.dimension_faceAtom_add_one
  have hA : 0 < m.faceAtom.dimension := by omega
  have hU : 0 < m.atom.dimension := m.positive
  obtain ⟨U₀, a₀, c₀, ht, hev, hcb, hbe⟩ := roundContext_solution_cell hY
    (m.frames w le_rfl) (m.faceBoundary hk w false) (m.faceBoundary hk w true)
    (m.oppBoundary w) (m.frameEquivalences_of_marksHorn w hw) (m.roundContextEquation hk w)
  have hv := m.dim_faceBoundary hk w false
  have hd₀ : U₀.dimension = m.faceAtom.dimension := by
    have : (ofCell a₀).dim = U₀.dimension := rfl
    have := ht.dim_eq
    omega
  obtain ⟨e₀, he₀⟩ := exists_iso_extends_of_equiv_boundary hA hd₀
    (realize.map (RDCpx.ofInclusion
      (P := m.faceAtom.toMoleculeShape.rdc.restrict (m.faceAtom.ogp.bdryFull ⊤))
      (Q := m.hornRDC) m.faceSphere) ≫ w) a₀ fun β => by
      rw [show m.faceAtom.dimension - 1 = (m.faceBoundary hk w false).dim by omega]
      refine PastingDiagram.Equiv.trans ?_ ((m.sphereBoundary_faceSphere hk w hA β).symm)
      cases β
      exacts [ht.source, ht.target]
  obtain ⟨σ, hσ₁, hσ₂⟩ := m.exists_sphere_extension w (Y.map e₀.hom.op a₀) he₀
  have hΛ := m.hornSet_subset_bdryFull
  have hsS : m.atom.ogp.bdry ⊤ m.side ≤ m.atom.ogp.bdryFull ⊤ := bdry_le_bdryFull _ _
  have hfr : m.frames σ hΛ = m.frames w le_rfl := by
    have h := m.frames_inclusion hΛ σ le_rfl
    rw [hσ₁] at h
    exact h.symm
  have hev' := m.evalFrames_restrictIn σ hΛ hsS
  rw [hfr] at hev'
  have hcl : (restrictIn σ (P := m.atom.toMoleculeShape) (m.atom.isRDC m.face)
      (m.closure_face_subset_bdry.trans hsS)).Equiv (ofCell a₀) := by
    refine (equiv_restrictAlong_of_image_eq σ _ m.faceEmb _
      (m.image_faceEmb.le.trans (m.closure_face_subset_bdry.trans hsS)) ?_).trans ?_
    · exact (m.atom.toMoleculeShape.map_subIncl_top _).trans m.image_faceEmb.symm
    · have h2 : restrictAlong σ m.faceAtom.toMoleculeShape m.faceEmb
          (m.image_faceEmb.le.trans (m.closure_face_subset_bdry.trans hsS)) =
          ofCell (Y.map e₀.hom.op a₀) := congrArg (PastingDiagram.mk _) hσ₂
      rw [h2]
      exact equiv_ofCell_map_iso e₀ a₀
  have hsc := EvalFrames.unique hev' hev hcl
  have hsph : ∀ α (hα : IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ α)),
      (sphereBoundary m.atom hU σ α).Equiv (restrictIn σ hα (bdry_le_bdryFull _ α)) :=
    fun α hα => equiv_restrictAlong_of_image_eq σ _ _ _ _
      ((m.atom.toMoleculeShape.map_boundaryIncl_eq_bdry (by omega : m.atom.dimension = _) α).trans
        (m.atom.toMoleculeShape.map_subIncl_top hα).symm)
  have hS1 : (sphereBoundary m.atom hU σ m.side).Equiv c₀.toPastingDiagram :=
    (hsph m.side (m.isMoleculeIn_bdry m.side)).trans hsc
  have hopp : restrictIn σ (P := m.atom.toMoleculeShape) (m.isMoleculeIn_bdry (!m.side))
      (bdry_le_bdryFull _ _) = (m.oppBoundary w).toPastingDiagram := by
    rw [← hσ₁]
    exact (restrictAlong_inclusion hΛ σ _ _ ((MoleculeShape.map_subIncl_top _ _).le.trans
      m.bdry_not_subset_hornSet)).symm
  have hS2 : (sphereBoundary m.atom hU σ (!m.side)).Equiv (m.oppBoundary w).toPastingDiagram :=
    hopp ▸ hsph (!m.side) (m.isMoleculeIn_bdry (!m.side))
  have hdc : c₀.dim = m.atom.dimension - 1 := by
    have h1 := dim_eq_of_equiv hS1
    have h2 : ((sphereBoundary m.atom hU σ m.side).dim : WithBot ℕ∞) =
        (m.atom.dimension - 1 : ℕ) :=
      (dim_restrictAlong σ _ _ _).trans (by
        rw [MoleculeShape.map_boundaryIncl_top]
        exact m.atom.isMolecule.krullDim_boundary (by
          rw [LowerSet.krullDim_top, m.atom.krullDim_eq_dimension]
          exact_mod_cast Nat.sub_le _ 1) _)
    have h2' : (sphereBoundary m.atom hU σ m.side).dim = m.atom.dimension - 1 := by
      exact_mod_cast h2
    omega
  obtain ⟨U₁, h₁, he₁, hd₁, hb₁⟩ : ∃ (U₁ : Atom) (h₁ : diagram Y U₁), IsEquivalence Y h₁ ∧
      U₁.dimension = m.atom.dimension ∧ ∀ α,
        ((ofCell h₁).boundary (m.atom.dimension - 1) α).Equiv
          (sphereBoundary m.atom hU σ α) := by
    obtain ⟨U₁, h₁, he, hd, hf, ht⟩ :=
      exists_equivalence_cell_side hY m.side c₀ (m.oppBoundary w) hcb
    refine ⟨U₁, h₁, he, by omega, fun α => ?_⟩
    rw [show m.atom.dimension - 1 = c₀.dim by omega]
    obtain rfl | rfl := Bool.eq_or_eq_not α m.side
    · exact hf.trans hS1.symm
    · exact ht.trans hS2.symm
  obtain ⟨e, he⟩ := exists_iso_extends_of_equiv_boundary hU hd₁ σ h₁ hb₁
  refine ⟨Y.map e.hom.op h₁, ?_, (MarkedDiagSet.mem_marked_natural_iff Y _ _).2
    ((isEquivalence_map_iso_iff e h₁).2 he₁), fun hsub => ?_⟩
  · exact (realize.map_comp_assoc (RDCpx.inclusion m.atom.toMoleculeShape.rdc hΛ)
      (m.atom.toMoleculeShape.rdc.restrictIncl (m.atom.ogp.bdryFull ⊤)) _).trans
      ((congrArg (realize.map _ ≫ ·) he).trans hσ₁)
  · have hz : Y.map (Atom.closureIncl m.atom m.face).op (Y.map e.hom.op h₁) =
        Y.map e₀.hom.op a₀ := by
      refine ofCell_map_injective ((ofCell_map_op_map (Atom.closureIncl m.atom m.face) _).trans
        (Eq.trans ?_ hσ₂))
      refine Eq.trans ?_ (congrArg (realize.map (RDCpx.ofInclusion
        (P := m.faceAtom.toMoleculeShape.rdc)
        (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.faceToSphere) ≫ ·) he)
      exact realize.map_comp_assoc (RDCpx.ofInclusion (P := m.faceAtom.toMoleculeShape.rdc)
        (Q := m.atom.toMoleculeShape.rdc.restrict (m.atom.ogp.bdryFull ⊤)) m.faceToSphere)
        (m.atom.toMoleculeShape.rdc.restrictIncl (m.atom.ogp.bdryFull ⊤)) _
    exact (MarkedDiagSet.mem_marked_natural_iff Y _ _).2 ((congrArg (IsEquivalence Y) hz).mpr
      ((isEquivalence_map_iso_iff e₀ a₀).2 (hbe (m.oppBoundary_mem_equivalences w hw hsub))))

theorem exists_fills_natural_of_dimension_eq_one (hd : m.atom.dimension = 1)
    (w : realize.obj m.hornRDC ⟶ Y) : ∃ z, m.Fills (MarkedDiagSet.natural.obj Y) w z := by
  obtain ⟨y, hy⟩ := m.exists_hornSet_eq_singleton hd
  have hyΛ : y ∈ m.hornSet := by
    rw [← SetLike.mem_coe, hy]
    exact Set.mem_singleton y
  have hdy : grade ℕ y = 0 := by
    have hne := (m.atom.mem_bdryFull_top_iff y).1 (m.hornSet_subset_bdryFull hyΛ)
    have hlt : grade ℕ y < grade ℕ m.atom.top :=
      grade_strictMono (lt_of_le_of_ne (m.atom.le_top y) hne)
    have := m.atom.dimension_eq
    omega
  have : IsIso (toAtomPoint (Atom.ofClosure m.atom y)) :=
    isIso_toAtomPoint_of_dimension_eq_zero ((Atom.dimension_ofClosure m.atom y).trans hdy)
  let c₀ : atomToRDCpx.obj atomPoint ⟶ m.hornRDC :=
    atomToRDCpx.map (inv (toAtomPoint (Atom.ofClosure m.atom y))) ≫
      principalInclusionIn m.atom m.hornSet hyΛ
  have hval : ∀ {T : Atom} (f : atomToRDCpx.obj T ⟶ m.hornRDC) (t : T.ogp),
      (ConcreteCategory.hom f.hom t).1 = y := fun f t => by
    have h := (ConcreteCategory.hom f.hom t).2
    rw [← SetLike.mem_coe, hy] at h
    exact h
  have hf : ∀ {T : Atom} (f : atomToRDCpx.obj T ⟶ m.hornRDC),
      f = atomToRDCpx.map (toAtomPoint T) ≫ c₀ := fun f => by
    ext t
    exact (hval f t).trans (hval _ t).symm
  have hdeg : ¬IsIso (toAtomPoint m.atom) := fun hi => by
    have := Atom.dimension_eq_of_iso (asIso (toAtomPoint m.atom))
    rw [hd, dimension_atomPoint] at this
    exact one_ne_zero this
  refine ⟨Y.map (toAtomPoint m.atom).op (w.app (op atomPoint) ⟨c₀⟩), ?_,
    (MarkedDiagSet.mem_marked_natural_iff Y _ _).2 (degenerate_isEquivalence Y _
      ⟨atomPoint, toAtomPoint m.atom, _, isCollapseHom_toAtomPoint m.atom, hdeg, rfl⟩),
    fun hsub => absurd (m.dim_face_pos_of_faceSet_subset hsub)
      (by have := m.dim_face_add_one; omega)⟩
  ext ⟨T⟩ ⟨f : atomToRDCpx.obj T ⟶ m.hornRDC⟩
  change Y.map (Atom.fullyFaithful.preimage (f ≫ m.hornIncl)).op
    (Y.map (toAtomPoint m.atom).op (w.app (op atomPoint) ⟨c₀⟩)) = w.app (op T) ⟨f⟩
  refine (Functor.map_comp_apply Y (toAtomPoint m.atom).op
    (Atom.fullyFaithful.preimage (f ≫ m.hornIncl)).op _).symm.trans ?_
  rw [← op_comp, Subsingleton.elim (Atom.fullyFaithful.preimage (f ≫ m.hornIncl) ≫
    toAtomPoint m.atom) (toAtomPoint T), hf f]
  exact (NatTrans.naturality_apply w (toAtomPoint T).op ⟨c₀⟩).symm

end Atoms.Shape.MarkedHornData

namespace Atoms.Diagrammatic

theorem hasMarkedRLP_markedHorns_natural_of_hasWeakComposites {X : DiagSet.{u}}
    (hX : HasWeakComposites X) : HasMarkedRLP markedHorns (MarkedDiagSet.natural.obj X) :=
  hasMarkedRLP_markedHorns_iff_fills.2 fun m w hw => by
    rcases Nat.lt_or_ge m.atom.dimension 2 with h | h
    · exact m.exists_fills_natural_of_dimension_eq_one (by have := m.positive; omega) w
    · exact m.exists_fills_natural_of_two_le hX h w hw

theorem isInftyCategory_iff_natural_hasMarkedRLP (n : ℕ∞) (X : DiagSet.{u}) :
    IsInftyCategory n X ↔
      HasMarkedRLP (markedHorns ⊔ markingGeneratorsAbove n) (MarkedDiagSet.natural.obj X) :=
  ⟨fun hX => (hasMarkedRLP_sup _ _ _).2
    ⟨hasMarkedRLP_markedHorns_natural_of_hasWeakComposites hX.1,
      (hasMarkedRLP_markingGeneratorsAbove_iff n _).2 fun U x hn =>
        (MarkedDiagSet.mem_marked_natural_iff X U x).2 (hX.2 U x hn)⟩,
    isInftyCategory_of_hasMarkedRLP n (MarkedDiagSet.natural.obj X)⟩

end Atoms.Diagrammatic
