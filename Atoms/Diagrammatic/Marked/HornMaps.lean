import Atoms.Diagrammatic.Marked.Generators
import Atoms.Diagrammatic.Context.Frames

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram
open Atoms.Homotopical (MarkedPresheaf)

universe u

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

variable (m : MarkedHornData)

def MarksHorn (X : MarkedDiagSet.{u}) (w : realize.obj m.hornRDC ⟶ X.underlying) : Prop :=
  ∀ a (ha : a ∈ m.marking), w.app (op (Atom.ofClosure m.atom a))
    ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩ ∈ X.marked _

def Fills (X : MarkedDiagSet.{u}) (w : realize.obj m.hornRDC ⟶ X.underlying)
    (z : diagram X.underlying m.atom) : Prop :=
  realize.map m.hornIncl ≫ (ofCell z).map = w ∧ z ∈ X.marked m.atom ∧
    (m.atom.ogp.faces (!m.side) m.atom.top ⊆ m.marking →
      X.underlying.map (Atom.closureIncl m.atom m.face).op z ∈ X.marked _)

end Atoms.Shape.MarkedHornData

namespace Atoms.Diagrammatic

theorem hasMarkedRLP_markedHorns_iff_fills {X : MarkedDiagSet.{u}} :
    HasMarkedRLP markedHorns X ↔ ∀ (m : MarkedHornData)
      (w : realize.obj m.hornRDC ⟶ X.underlying), m.MarksHorn X w → ∃ z, m.Fills X w z := by
  constructor
  · intro hX m w hw
    let Φ := closedSubpresheafRealizeIso m.atom m.hornSet
    let q : m.source ⟶ X := MarkedPresheaf.homMk (Φ.inv ≫ w) fun V y hy => by
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨a, ha, him, hd⟩
      · exact X.mem_marked_of_isDegenerate (isDegenerate_app _ hy)
      · obtain ⟨e, he⟩ := exists_iso_comp_closureIncl y.1.down (Atom.map_top_eq_Iic_iff.1 him) hd
        have hy' : Φ.inv.app (op V) y = (realize.obj m.hornRDC).map e.hom.op
            ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩ := by
          have h1 := NatTrans.naturality_apply Φ.hom e.hom.op
            ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩
          have h2 : (closedSubpresheaf m.atom m.hornSet).toFunctor.map e.hom.op
              (Φ.hom.app _ ⟨principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1⟩) = y :=
            Subtype.ext (congrArg ULift.up he)
          rw [← h2, ← h1, Iso.hom_inv_id_app_apply]
        change w.app (op V) (Φ.inv.app (op V) y) ∈ X.marked V
        rw [hy']
        exact (congrArg (· ∈ X.marked V) (NatTrans.naturality_apply w e.hom.op _)).mpr
          ((X.transport e _).1 (hw a ha))
    obtain ⟨f, hf⟩ := hasMarkedRLP_iff.1 hX (markedHornInclusion m) (MorphismProperty.ofHoms.mk m) q
    let F := MarkedPresheaf.forget.map f
    let z : diagram X.underlying m.atom :=
      F.app (op m.atom) ⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩
    have hfz : ∀ {T : Atom} (g : T ⟶ m.atom) (hg : ∀ t, g t ∈ (⊤ : LowerSet m.atom.ogp)),
        F.app (op T) ⟨⟨g⟩, hg⟩ = X.underlying.map g.op z := by
      intro T g hg
      exact (congrArg (F.app (op T))
        (Subtype.ext (congrArg ULift.up (Category.comp_id g).symm))).trans
        (NatTrans.naturality_apply F g.op
          (⟨⟨𝟙 m.atom⟩, fun _ => LowerSet.mem_top⟩ : m.target.underlying.obj (op m.atom)))
    refine ⟨z, ?_, ?_, fun hsub => ?_⟩
    · ext ⟨T⟩ ⟨c⟩
      have e := congrArg (fun φ : m.source ⟶ X =>
        (MarkedPresheaf.forget.map φ).app (op T) (Φ.hom.app (op T) ⟨c⟩)) hf
      exact (hfz (Atom.fullyFaithful.preimage (c ≫ m.hornIncl))
        (fun _ => LowerSet.mem_top)).symm.trans e
    · exact MarkedPresheaf.map_mem_marked f ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ⟨m.atom.top, m.mem_targetMarking_iff.2 (Or.inl rfl), Atom.map_top _,
          m.atom.dimension_eq⟩))
    · exact (congrArg (· ∈ X.marked _) (hfz _ (fun _ => LowerSet.mem_top))).mp
        (MarkedPresheaf.map_mem_marked f ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr ⟨m.face, m.mem_targetMarking_iff.2 (Or.inr (Or.inl ⟨hsub, rfl⟩)),
            Atom.map_closureInclOGP_top m.atom m.face, Atom.dimension_ofClosure m.atom m.face⟩)))
  · intro h
    refine hasMarkedRLP_iff.2 fun A B i hi q => ?_
    cases hi with
    | mk m =>
      let Φ := closedSubpresheafRealizeIso m.atom m.hornSet
      have hw : m.MarksHorn X (Φ.hom ≫ MarkedPresheaf.forget.map q) := fun a ha =>
        MarkedPresheaf.map_mem_marked q ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr ⟨a, ha, Atom.map_closureInclOGP_top m.atom a,
            Atom.dimension_ofClosure m.atom a⟩))
      obtain ⟨z, hz, hzm, hzf⟩ := h m _ hw
      have hzi : ∀ {T : Atom} (c : atomToRDCpx.obj T ⟶ m.hornRDC),
          (realize.map m.hornIncl ≫ (ofCell z).map).app (op T) ⟨c⟩ =
            (MarkedPresheaf.forget.map q).app (op T) (Φ.hom.app (op T) ⟨c⟩) := fun c =>
        congrArg (fun φ => φ.app (op _) ⟨c⟩) hz
      refine ⟨MarkedPresheaf.homMk ((closedSubpresheafUnivIso m.atom).hom ≫ uliftYonedaEquiv.symm z)
        fun V y hy => ?_, MarkedPresheaf.hom_ext ?_⟩
      · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨a, ha, him, hd⟩
        · exact X.mem_marked_of_isDegenerate
            (isDegenerate_app ((closedSubpresheafUnivIso m.atom).hom ≫ uliftYonedaEquiv.symm z) hy)
        change X.underlying.map y.1.down.op z ∈ X.marked V
        obtain ⟨e, he⟩ := exists_iso_comp_closureIncl y.1.down (Atom.map_top_eq_Iic_iff.1 him) hd
        have hyz : X.underlying.map y.1.down.op z =
            X.underlying.map e.hom.op (X.underlying.map (Atom.closureIncl m.atom a).op z) := by
          rw [← he]
          exact Functor.map_comp_apply X.underlying (Atom.closureIncl m.atom a).op e.hom.op z
        refine (congrArg (· ∈ X.marked V) hyz).mpr ((X.transport e _).1 ?_)
        rcases m.mem_targetMarking_iff.1 ha with rfl | ⟨hsub, rfl⟩ | ha
        · obtain ⟨e', he'⟩ := exists_iso_comp_closureIncl (a := m.atom.top) (𝟙 m.atom)
            (Atom.map_top_eq_Iic_iff.1 (Atom.map_top _)) m.atom.dimension_eq
          have hι : Atom.closureIncl m.atom m.atom.top = e'.inv := by
            rw [← Category.id_comp (Atom.closureIncl m.atom m.atom.top), ← e'.inv_hom_id,
              Category.assoc, he', Category.comp_id]
          have hz' : X.underlying.map (Atom.closureIncl m.atom m.atom.top).op z =
              X.underlying.map e'.symm.hom.op z := by
            rw [hι]
            rfl
          exact (congrArg (· ∈ X.marked _) hz').mpr ((X.transport e'.symm z).1 hzm)
        · exact hzf hsub
        · exact (congrArg (· ∈ X.marked _)
            (hzi (principalInclusionIn m.atom m.hornSet (m.marking_mem a ha).1))).mpr
            (hw a ha)
      · ext ⟨T⟩ y
        exact hzi (Φ.inv.app (op T) y).down

end Atoms.Diagrammatic

namespace Atoms.Shape.MarkedHornData

open Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

variable (m : MarkedHornData) [∀ i, DecidablePred (· ∈ m.left i)]
  [∀ i, DecidablePred (· ∈ m.right i)]

def frameAt {S : LowerSet m.atom.ogp}
    (w : realize.obj (m.atom.toMoleculeShape.rdc.restrict S) ⟶ X) (hΛS : m.hornSet ≤ S) (i : ℕ)
    (hi : i < m.atom.dimension - 1) : PastingDiagram X × PastingDiagram X :=
  (restrictIn w (m.staged.isMoleculeIn_left i hi).1
      ((le_sup_left.trans (m.left_union_right_subset_hornSet hi)).trans hΛS),
    restrictIn w (m.staged.isMoleculeIn_right i hi).1
      ((le_sup_right.trans (m.left_union_right_subset_hornSet hi)).trans hΛS))

def frames {S : LowerSet m.atom.ogp}
    (w : realize.obj (m.atom.toMoleculeShape.rdc.restrict S) ⟶ X) (hΛS : m.hornSet ≤ S) :
    ContextFrames X :=
  List.ofFn fun i : Fin (m.atom.dimension - 1) => m.frameAt w hΛS i i.isLt

theorem length_frames {S : LowerSet m.atom.ogp}
    (w : realize.obj (m.atom.toMoleculeShape.rdc.restrict S) ⟶ X) (hΛS : m.hornSet ≤ S) :
    (m.frames w hΛS).length = m.atom.dimension - 1 :=
  List.length_ofFn

theorem frames_get {S : LowerSet m.atom.ogp}
    (w : realize.obj (m.atom.toMoleculeShape.rdc.restrict S) ⟶ X) (hΛS : m.hornSet ≤ S)
    (i : Fin (m.frames w hΛS).length) :
    (m.frames w hΛS).get i =
      m.frameAt w hΛS i (lt_of_lt_of_eq i.isLt (m.length_frames w hΛS)) :=
  List.get_ofFn _ i

theorem evalFrames_restrictIn {S : LowerSet m.atom.ogp}
    (w : realize.obj (m.atom.toMoleculeShape.rdc.restrict S) ⟶ X) (hΛS : m.hornSet ≤ S)
    (hsS : m.atom.ogp.bdry ⊤ m.side ≤ S) :
    EvalFrames (m.frames w hΛS) 0
      (restrictIn w (m.atom.isRDC m.face) (m.closure_face_subset_bdry.trans hsS))
      (restrictIn w (P := m.atom.toMoleculeShape) (m.stage_last ▸
        m.staged.isMoleculeIn_stage _ le_rfl) hsS) := by
  classical
  have hMol : ∀ i, i ≤ m.atom.dimension - 1 → IsMoleculeIn m.atom.ogp (m.stage i) :=
    m.staged.isMoleculeIn_stage
  have hSub : ∀ i, i ≤ m.atom.dimension - 1 → m.stage i ≤ S := fun i hi =>
    ((m.staged.stage_le i _ hi le_rfl).trans m.stage_last.le).trans hsS
  have key : ∀ n (hn : n ≤ m.atom.dimension - 1),
      EvalFrames (List.ofFn fun i : Fin n => m.frameAt w hΛS i (by omega)) 0
        (restrictIn w (hMol 0 (Nat.zero_le _)) (hSub 0 (Nat.zero_le _)))
        (restrictIn w (hMol n hn) (hSub n hn)) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [List.ofFn_zero]
      exact .refl _
    | succ n ih =>
      intro hn
      rw [List.ofFn_succ_last, EvalFrames.append_singleton]
      refine ⟨restrictIn w (hMol n (by omega)) (hSub n (by omega)), ?_, ?_⟩
      · exact ih (by omega)
      · rw [List.length_ofFn, Nat.zero_add]
        obtain ⟨hL, hR⟩ := m.staged.stage_succ n (by omega)
        have hLm := (m.staged.isMoleculeIn_left n (by omega)).1
        have hRm := (m.staged.isMoleculeIn_right n (by omega)).1
        have hNm := hL.isMoleculeIn hLm (hMol n (by omega))
        have hNS : m.left (n + 1) ⊔ m.stage n ≤ S :=
          (le_sup_left.trans hR.sup_eq.le).trans (hSub (n + 1) hn)
        refine ⟨restrictIn w hNm hNS, restrictIn w (hMol (n + 1) hn) (hSub (n + 1) hn),
          pastes_restrictIn w hLm (hMol n (by omega)) hNm _ _ hNS hL,
          pastes_restrictIn w hNm hRm (hMol (n + 1) hn) hNS _ _ hR, .refl _⟩
  refine EvalFrames.of_equiv (key _ le_rfl)
    (equiv_restrictIn_of_eq w _ _ _ _ m.staged.stage_zero)
    (equiv_restrictIn_of_eq w _ _ _ _ m.stage_last)

end Atoms.Shape.MarkedHornData
