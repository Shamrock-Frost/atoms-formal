import Atoms.Diagrammatic.Marked.HornMaps

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

variable (m : MarkedHornData) {Y : DiagSet.{u}}

def faceBoundary (hk : 2 ≤ m.atom.dimension) (w : realize.obj m.hornRDC ⟶ Y) (β : Bool) :
    RoundPastingDiagram Y :=
  ⟨restrictIn w (P := m.atom.toMoleculeShape)
      (m.isMoleculeIn_closure_face.boundary (m.atom.dimension - 2) β)
      (m.boundary_closure_face_subset_hornSet (by have := m.dim_face_add_one; omega) β),
    (m.atom.toMoleculeShape.isRound_sub_iff
      (m.isMoleculeIn_closure_face.boundary (m.atom.dimension - 2) β)).2
      ((m.atom.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := m.face))).isRound.boundary _ β)⟩

def oppBoundary (w : realize.obj m.hornRDC ⟶ Y) : RoundPastingDiagram Y :=
  ⟨restrictIn w (P := m.atom.toMoleculeShape) (M := m.atom.ogp.bdry ⊤ (!m.side))
      (m.isMoleculeIn_bdry (!m.side)) m.bdry_not_subset_hornSet,
    (m.atom.toMoleculeShape.isRound_sub_iff (S := m.atom.ogp.bdry ⊤ (!m.side))
      (m.isMoleculeIn_bdry (!m.side))).2 (m.round_bdry (!m.side))⟩

theorem dim_faceBoundary (hk : 2 ≤ m.atom.dimension) (w : realize.obj m.hornRDC ⟶ Y)
    (β : Bool) : (m.faceBoundary hk w β).dim = m.atom.dimension - 2 := by
  have hdf : grade ℕ m.face + 1 = m.atom.dimension := m.dim_face_add_one
  have h := m.atom.toMoleculeShape.dimension_sub
    (m.isMoleculeIn_closure_face.boundary (m.atom.dimension - 2) β)
  rw [m.isMoleculeIn_closure_face.krullDim_boundary (by
    rw [LowerSet.krullDim_Iic]
    exact_mod_cast (by omega : m.atom.dimension - 2 ≤ grade ℕ m.face)) β] at h
  exact_mod_cast h

theorem restrictIn_mapTo_of_ball {Y' : DiagSet.{u}} (w : realize.obj m.hornRDC ⟶ Y) (f : Y ⟶ Y')
    (F : realize.obj m.atom.toMoleculeShape.rdc ⟶ Y') (hF : realize.map m.hornIncl ≫ F = w ≫ f)
    {M : LowerSet m.atom.ogp} [DecidablePred (· ∈ M)] (hM : IsMoleculeIn m.atom.ogp M)
    (hMΛ : M ≤ m.hornSet) :
    (restrictIn w (P := m.atom.toMoleculeShape) hM hMΛ).mapTo f =
      (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hM :=
  congrArg (PastingDiagram.mk _) ((Category.assoc _ _ _).trans
    ((congrArg (realize.map _ ≫ ·) hF.symm).trans
      ((realize.map_comp_assoc _ _ _).symm.trans
        (congrArg (fun t => realize.map t ≫ F) (by ext x; rfl)))))

theorem formalCell_of_ball [∀ i, DecidablePred (· ∈ m.left i)]
    [∀ i, DecidablePred (· ∈ m.right i)] (hk : 2 ≤ m.atom.dimension) {Y' : DiagSet.{u}}
    (w : realize.obj m.hornRDC ⟶ Y) (f : Y ⟶ Y') (F : realize.obj m.atom.toMoleculeShape.rdc ⟶ Y')
    (hF : realize.map m.hornIncl ≫ F = w ≫ f) :
    ∃ (U : Atom) (a : diagram Y' U) (c : RoundPastingDiagram Y'),
      HasRoundType (ofCell a) ⟨(m.faceBoundary hk w false).toPastingDiagram.mapTo f,
          (m.faceBoundary hk w false).isRound⟩
        ⟨(m.faceBoundary hk w true).toPastingDiagram.mapTo f, (m.faceBoundary hk w true).isRound⟩ ∧
      EvalFrames ((m.frames w le_rfl).map (fun p => (p.1.mapTo f, p.2.mapTo f))) 0
        (ofCell a) c.1 ∧
      Parallel c ⟨(m.oppBoundary w).toPastingDiagram.mapTo f, (m.oppBoundary w).isRound⟩ := by
  have hdf : grade ℕ m.face + 1 = m.atom.dimension := m.dim_face_add_one
  have hcl := m.isMoleculeIn_closure_face
  have hdcl : krullDim (LowerSet.Iic m.face) = ((m.atom.dimension - 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_Iic]
    congr 1
    omega
  have hσ' : ∀ {M : LowerSet m.atom.ogp} [DecidablePred (· ∈ M)]
      (hM : IsMoleculeIn m.atom.ogp M),
      restrictIn (realize.map (m.atom.toMoleculeShape.rdc.restrictIncl ⊤) ≫ F)
        (P := m.atom.toMoleculeShape) hM le_top =
      (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hM :=
    fun hM => restrictAlong_restrictIncl _ _ _ _
  have hframes : m.frames (realize.map (m.atom.toMoleculeShape.rdc.restrictIncl ⊤) ≫ F) le_top =
      (m.frames w le_rfl).map (fun p => (p.1.mapTo f, p.2.mapTo f)) := by
    rw [frames, frames, List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => Prod.ext ?_ ?_)
    · have hi := i.isLt
      exact (hσ' _).trans (m.restrictIn_mapTo_of_ball w f F hF _
        (le_sup_left.trans (m.left_union_right_subset_hornSet hi))).symm
    · have hi := i.isLt
      exact (hσ' _).trans (m.restrictIn_mapTo_of_ball w f F hF _
        (le_sup_right.trans (m.left_union_right_subset_hornSet hi))).symm
  have hcell := PastingDiagram.equiv_ofCell_cellAt (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y')
    m.face
  have hdc : (ofCell ((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').cellAt m.face)).dim =
      m.atom.dimension - 1 := by
    have h := (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').dim_restrictTo
      (m.atom.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := m.face))).1
    rw [hdcl] at h
    exact (dim_eq_of_equiv hcell).trans (by exact_mod_cast h)
  have hbs : IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ m.side) :=
    m.isMoleculeIn_bdry m.side
  refine ⟨_, (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').cellAt m.face,
    ⟨(⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hbs,
      (PastingDiagram.isRound_restrictTo_iff _ hbs).2 (m.round_bdry m.side)⟩, ?_, ?_, ?_⟩
  · have hv : (m.faceBoundary hk w false).dim = m.atom.dimension - 2 :=
      m.dim_faceBoundary hk w false
    refine ⟨?_, (m.dim_faceBoundary hk w false).trans (m.dim_faceBoundary hk w true).symm, ?_, ?_⟩
    · change _ = (m.faceBoundary hk w false).dim + 1
      omega
    all_goals
      change ((ofCell _).boundary (m.faceBoundary hk w false).dim _).Equiv _
      rw [hv]
      refine (hcell.boundary _ _).trans
        ((PastingDiagram.equiv_boundary_restrictTo _ hcl _ _).trans ?_)
      exact .symm ((m.restrictIn_mapTo_of_ball w f F hF _
        (m.boundary_closure_face_subset_hornSet (n := m.atom.dimension - 2)
          (by have := m.dim_face_add_one; omega) _)) ▸
          PastingDiagram.Equiv.refl _)
  · have h := m.evalFrames_restrictIn
      (realize.map (m.atom.toMoleculeShape.rdc.restrictIncl ⊤) ≫ F) le_top le_top
    have e₁ := Eq.subst (motive := fun d => (restrictIn (realize.map
        (m.atom.toMoleculeShape.rdc.restrictIncl ⊤) ≫ F) (P := m.atom.toMoleculeShape)
        (m.atom.isRDC m.face) le_top).Equiv d)
      (hσ' (m.atom.isRDC m.face)) (.refl _)
    have e₂ := Eq.subst (motive := fun d => (restrictIn (realize.map
        (m.atom.toMoleculeShape.rdc.restrictIncl ⊤) ≫ F) (P := m.atom.toMoleculeShape) hbs
        le_top).Equiv d) (hσ' hbs) (.refl _)
    have e₃ := PastingDiagram.equiv_restrictTo_of_eq
        (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y')
      (m.atom.isRDC m.face) (m.atom.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := m.face))).1
      rfl
    exact hframes ▸ EvalFrames.of_equiv h (e₁.trans (e₃.trans (hcell.symm))) e₂
  · have hdS : ∀ α, krullDim (m.atom.ogp.bdry ⊤ α) =
        ((m.atom.dimension - 1 : ℕ) : WithBot ℕ∞) := fun α => by
      rw [m.atom.bdry_top_eq_boundary m.positive α]
      refine IsMoleculeIn.krullDim_boundary m.atom.isMolecule ?_ α
      rw [LowerSet.krullDim_top, m.atom.krullDim_eq_dimension]
      exact_mod_cast Nat.sub_le _ 1
    have hsph : ∀ α γ, m.atom.ogp.boundary
        (m.atom.ogp.bdry ⊤ α) (m.atom.dimension - 2) γ =
        m.atom.ogp.boundary ⊤ (m.atom.dimension - 2) γ := fun α γ => by
      rw [m.atom.bdry_top_eq_boundary m.positive α]
      exact IsMoleculeIn.isGlobular m.atom.isMolecule _ _ (by omega) γ α
    have hbo : IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ (!m.side)) :=
      m.isMoleculeIn_bdry (!m.side)
    have hb' : (m.oppBoundary w).toPastingDiagram.mapTo f =
        (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hbo :=
      m.restrictIn_mapTo_of_ball w f F hF hbo m.bdry_not_subset_hornSet
    have hcd : ((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hbs).dim =
        m.atom.dimension - 1 := by
      have h := (⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').dim_restrictTo hbs
      rw [hdS m.side] at h
      exact_mod_cast h
    have hbd : ((m.oppBoundary w).toPastingDiagram.mapTo f).dim = m.atom.dimension - 1 := by
      have h := m.atom.toMoleculeShape.dimension_sub hbo
      rw [hdS (!m.side)] at h
      exact_mod_cast h
    refine ⟨hcd.trans hbd.symm, Or.inr fun γ => ?_⟩
    change (((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hbs).boundary
      (((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hbs).dim - 1) γ).Equiv
      (((m.oppBoundary w).toPastingDiagram.mapTo f).boundary
        (((m.oppBoundary w).toPastingDiagram.mapTo f).dim - 1) γ)
    rw [hcd, hbd, hb', show m.atom.dimension - 1 - 1 = m.atom.dimension - 2 by omega]
    have key : ∀ (α : Bool) (hα : IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ α)),
        (((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo hα).boundary
          (m.atom.dimension - 2) γ).Equiv
        ((⟨m.atom.toMoleculeShape, F⟩ : PastingDiagram Y').restrictTo
          (IsMoleculeIn.boundary m.atom.isMolecule (m.atom.dimension - 2) γ)) :=
      fun α hα => (PastingDiagram.equiv_boundary_restrictTo _ hα _ γ).trans
        (PastingDiagram.equiv_restrictTo_of_eq _ _ _ (hsph α γ))
    exact (key m.side hbs).trans ((key (!m.side) hbo).symm)

theorem marked_app_of_marksHorn {X : MarkedDiagSet.{u}} (w : realize.obj m.hornRDC ⟶ X.underlying)
    (hw : m.MarksHorn X w) {T : Atom} (c : atomToRDCpx.obj T ⟶ m.hornRDC)
    (hc : Function.Injective fun t => (ConcreteCategory.hom c.hom t).1)
    (ht : (ConcreteCategory.hom c.hom T.top).1 ∈ m.marking) : w.app (op T) ⟨c⟩ ∈ X.marked T := by
  let g : T ⟶ m.atom := Atom.fullyFaithful.preimage (c ≫ m.hornIncl)
  have hg : IsInclusionHom g := hc
  have hd : T.dimension = grade ℕ (g T.top) :=
    T.dimension_eq.trans (grade_eq_of_isInclusionHom g hg T.top).symm
  obtain ⟨e, he⟩ := exists_iso_comp_closureIncl g (Atom.map_top_eq_Iic_iff.1 (Atom.map_top g)) hd
  have hcm : c = atomToRDCpx.map e.hom ≫
      principalInclusionIn m.atom m.hornSet (m.marking_mem _ ht).1 := by
    ext t
    exact congrArg (fun f : T ⟶ m.atom => f t) he.symm
  have hval : w.app (op T) ⟨c⟩ = X.underlying.map e.hom.op
      (w.app _ ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem _ ht).1⟩) :=
    (congrArg (w.app (op T)) (congrArg ULift.up hcm)).trans (NatTrans.naturality_apply w e.hom.op _)
  exact (congrArg (· ∈ X.marked T) hval).mpr ((X.transport e _).1 (hw _ ht))

theorem frameEquivalences_of_marksHorn [∀ i, DecidablePred (· ∈ m.left i)]
    [∀ i, DecidablePred (· ∈ m.right i)] (w : realize.obj m.hornRDC ⟶ Y)
    (hw : m.MarksHorn (MarkedDiagSet.natural.obj Y) w) :
    FrameEquivalences (m.frames w le_rfl) := by
  intro i p hp U x hU hι
  have hi : i.val < m.atom.dimension - 1 :=
    lt_of_lt_of_eq i.isLt (m.length_frames w le_rfl)
  have key : ∀ {M : LowerSet m.atom.ogp} [DecidablePred (· ∈ M)]
      (hM : IsMoleculeIn m.atom.ogp M) (hMΛ : M ≤ m.hornSet),
      (∀ y ∈ M, grade ℕ y = i.val + 1 → y ∈ m.marking) →
      p = restrictIn w (P := m.atom.toMoleculeShape) hM hMΛ → IsEquivalence Y x := by
    intro M _ hM hMΛ hmk hpM
    subst hpM
    obtain ⟨v, ι, -, hιx⟩ := hι
    obtain ⟨c, hcx, hcinj, hcimg⟩ := exists_app_eq_of_subdiagram w _ _ ι hιx
    let g : U ⟶ m.atom := Atom.fullyFaithful.preimage (c ≫ m.hornIncl)
    have htM : (ConcreteCategory.hom c.hom U.top).1 ∈ M :=
      m.atom.toMoleculeShape.map_subIncl_top hM ▸ hcimg U.top
    have hdt : grade ℕ (ConcreteCategory.hom c.hom U.top).1 = i.val + 1 :=
      (grade_eq_of_isInclusionHom g hcinj U.top).trans (U.dimension_eq.symm.trans hU)
    rw [← hcx]
    exact (MarkedDiagSet.mem_marked_natural_iff Y U _).1
      (m.marked_app_of_marksHorn (X := MarkedDiagSet.natural.obj Y) w hw c hcinj (hmk _ htM hdt))
  have hL := m.staged.isMoleculeIn_left i.val hi
  have hR := m.staged.isMoleculeIn_right i.val hi
  have hLR := m.left_union_right_subset_hornSet hi
  rcases hp with rfl | rfl
  · refine key hL.1 (le_sup_left.trans hLR) (fun y hy hyd => m.marked_tops _ hi y
      (LowerSet.mem_sup_iff.2 (Or.inl hy)) hyd) ?_
    rw [m.frames_get]
    rfl
  · refine key hR.1 (le_sup_right.trans hLR) (fun y hy hyd => m.marked_tops _ hi y
      (LowerSet.mem_sup_iff.2 (Or.inr hy)) hyd) ?_
    rw [m.frames_get]
    rfl

theorem parallel_faceBoundary (hk : 2 ≤ m.atom.dimension) (w : realize.obj m.hornRDC ⟶ Y) :
    Parallel (m.faceBoundary hk w false) (m.faceBoundary hk w true) := by
  have hcl := m.isMoleculeIn_closure_face
  have hdf : grade ℕ m.face + 1 = m.atom.dimension := m.dim_face_add_one
  refine ⟨(m.dim_faceBoundary hk w false).trans (m.dim_faceBoundary hk w true).symm, ?_⟩
  rcases Nat.eq_zero_or_pos (m.atom.dimension - 2) with h0 | hpos
  · exact Or.inl ((m.dim_faceBoundary hk w false).trans h0)
  refine Or.inr fun γ => ?_
  have hsub := m.boundary_closure_face_subset_hornSet
    (n := m.atom.dimension - 2 - 1) (by have := m.dim_face_add_one; omega) γ
  have key : ∀ β, ((m.faceBoundary hk w β).boundary (m.atom.dimension - 2 - 1) γ).Equiv
      (restrictIn w (P := m.atom.toMoleculeShape) (hcl.boundary _ γ) hsub) := fun β =>
    equiv_boundary_restrictAlong w _ _
      ((m.atom.toMoleculeShape.map_subIncl_top (hcl.boundary _ β)).trans_le
        (m.boundary_closure_face_subset_hornSet (by omega) β)) _ _ γ
      ((congrArg (fun S => m.atom.ogp.boundary S _ γ)
        (m.atom.toMoleculeShape.map_subIncl_top (hcl.boundary _ β))).trans
        ((IsMoleculeIn.isGlobular hcl _ _ (by omega) γ β).trans
          (m.atom.toMoleculeShape.map_subIncl_top (hcl.boundary _ γ)).symm))
  have h1 : (m.faceBoundary hk w false).dim - 1 = m.atom.dimension - 2 - 1 := by
    rw [m.dim_faceBoundary hk w false]
  have h2 : (m.faceBoundary hk w true).dim - 1 = m.atom.dimension - 2 - 1 := by
    rw [m.dim_faceBoundary hk w true]
  rw [h1, h2]
  exact (key false).trans ((key true).symm)

theorem roundContextEquation [∀ i, DecidablePred (· ∈ m.left i)]
    [∀ i, DecidablePred (· ∈ m.right i)] (hk : 2 ≤ m.atom.dimension)
    (w : realize.obj m.hornRDC ⟶ Y) :
    RoundContextEquation (m.frames w le_rfl) (m.faceBoundary hk w false)
      (m.faceBoundary hk w true) (m.oppBoundary w) := by
  refine ⟨m.parallel_faceBoundary hk w, ?_, ?_, pushout (realize.map m.hornIncl) w,
    pushout.inr (realize.map m.hornIncl) w,
    (MorphismProperty.monomorphisms _).of_isPushout
      (IsPushout.of_hasPushout (realize.map m.hornIncl) w).flip
      (mono_realize_map m.hornIncl Subtype.val_injective),
    m.formalCell_of_ball hk w _ _ pushout.condition⟩
  · rw [m.length_frames, m.dim_faceBoundary hk w false]
    omega
  · intro i
    have hi : i.val < m.atom.dimension - 1 :=
      lt_of_lt_of_eq i.isLt (m.length_frames w le_rfl)
    rw [m.frames_get]
    exact ⟨by exact_mod_cast (m.atom.toMoleculeShape.dimension_sub
        (m.staged.isMoleculeIn_left _ hi).1).trans_le (m.staged.isMoleculeIn_left _ hi).2,
      by exact_mod_cast (m.atom.toMoleculeShape.dimension_sub
        (m.staged.isMoleculeIn_right _ hi).1).trans_le (m.staged.isMoleculeIn_right _ hi).2⟩

end Atoms.Shape.MarkedHornData
