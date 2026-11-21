import Atoms.Diagrammatic.AtomTest
import Atoms.Diagrammatic.Horn.MoleculeLocalizer

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
  Atoms.Diagrammatic

universe u

namespace Atoms.Diagrammatic

def complementInclusion (T : Atom) {U V : LowerSet T.ogp}
    (hV : T.ogp.IsRewritableSubmolecule V U) :
    (closedSubpresheaf.{u} T (T.ogp.bdryFull U)).toFunctor ⟶
      (closedSubpresheaf T hV.complement).toFunctor :=
  Subfunctor.homOfLe (closedSubpresheaf_mono T hV.bdryFull_le_complement)

theorem hornInclusions_le_of_ball {V : MorphismProperty DiagSet.{u}}
    [hV : Homotopical.IsALocalizer V] (hball : ∀ U : Atom, V (terminal.from (ball U))) :
    hornInclusions.{u} ≤ V := by
  rintro _ _ _ ⟨h⟩
  exact hV.of_terminal_from _ (terminal_from_horn_mem_of_ball (m := h.atom.dimension)
    (fun U _ ↦ hball U) h (Nat.le_succ _)) (hball h.atom)

end Atoms.Diagrammatic

namespace Atoms.TestCategory.BasicLocalizer

theorem wDiagSet_terminal_from_ball (𝒲 : BasicLocalizer.{u}) (U : Atom) :
    𝒲.wDiagSet (terminal.from (ball.{u} U)) := by
  have hT : IsTerminal (DiagSet.asSmall.obj (⊤_ DiagSet.{u})) :=
    terminalIsTerminal.isTerminalObj _
  let e : Arrow.mk (terminal.from (yoneda.obj (AsSmall.up.obj U))) ≅
      Arrow.mk (DiagSet.asSmall.map (terminal.from (ball.{u} U))) :=
    Arrow.isoMk (DiagSet.asSmallBallIso U).symm
      (terminalIsTerminal.uniqueUpToIso hT) (hT.hom_ext _ _)
  exact (𝒲.wDiagSet_iff _).2 (((𝒲.wPsh _).arrow_mk_iso_iff e).1
    ((𝒲.pshAspherical_iff_wPsh_terminal_from _ 𝒲.aspherical_asSmallAtom _).1
      (𝒲.pshAspherical_yoneda _ _)))

theorem hornInclusions_le_wDiagSet (𝒲 : BasicLocalizer.{u}) : hornInclusions.{u} ≤ 𝒲.wDiagSet :=
  hornInclusions_le_of_ball 𝒲.wDiagSet_terminal_from_ball

variable (𝒲 : BasicLocalizer.{0})

theorem wPsh_terminal_from_ball (U : Atom) : 𝒲.wPsh Atom (terminal.from (ball U)) :=
  𝒲.wDiagSet_eq_wPsh ▸ 𝒲.wDiagSet_terminal_from_ball U

theorem pshAspherical_closedSubpresheaf_of_isMoleculeIn (T : Atom)
    {S : LowerSet T.ogp} (hS : IsMoleculeIn T.ogp S) :
    𝒲.PshAspherical Atom (closedSubpresheaf T S).toFunctor :=
  (𝒲.pshAspherical_iff_wPsh_terminal_from Atom 𝒲.aspherical_atom _).2
    (terminal_from_closedSubpresheaf_mem_of_ball (m := T.dimension)
      (fun U _ ↦ 𝒲.wPsh_terminal_from_ball U) T hS
      ((LowerSet.krullDim_mono le_top).trans_eq
        (LowerSet.krullDim_top.trans T.krullDim_eq_dimension)))

theorem wPsh_homOfLe_closedSubpresheaf_of_isMoleculeIn (T : Atom)
    {S R : LowerSet T.ogp} (h : S ≤ R)
    (hS : IsMoleculeIn T.ogp S) (hR : IsMoleculeIn T.ogp R) :
    𝒲.wPsh Atom (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) :=
  𝒲.wPsh_of_pshAspherical Atom _ (𝒲.pshAspherical_closedSubpresheaf_of_isMoleculeIn T hS)
    (𝒲.pshAspherical_closedSubpresheaf_of_isMoleculeIn T hR)

theorem wPsh_homOfLe_closedSubpresheaf_of_eq_complement (T : Atom) (n : ℕ) :
    ∀ {U V : LowerSet T.ogp}, krullDim U = n → IsMoleculeIn T.ogp U →
      T.ogp.IsRound U → ∀ (hV : T.ogp.IsRewritableSubmolecule V U)
      {S R : LowerSet T.ogp} (h : S ≤ R), S = T.ogp.bdryFull U → R = hV.complement →
        𝒲.wPsh Atom (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) :=
  homOfLe_mem_of_eq_complement_of_ball (fun U _ ↦ 𝒲.wPsh_terminal_from_ball U) T n le_rfl

theorem wPsh_complementInclusion (T : Atom) {U V : LowerSet T.ogp}
    (hU : IsMoleculeIn T.ogp U) (hr : T.ogp.IsRound U)
    (hV : T.ogp.IsRewritableSubmolecule V U) :
    𝒲.wPsh Atom (complementInclusion T hV) := by
  obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
  exact 𝒲.wPsh_homOfLe_closedSubpresheaf_of_eq_complement T n hn hU hr hV
    hV.bdryFull_le_complement rfl rfl

theorem wPsh_oppositeBoundary_horn (h : HornData) :
    𝒲.wPsh Atom
      (Subfunctor.homOfLe (closedSubpresheaf_mono h.atom h.bdry_not_subset_hornSubset)) := by
  suffices key : ∀ {R : LowerSet h.atom.ogp} (hSR : h.atom.ogp.bdry ⊤ (!h.side) ≤ R),
      R = h.rewritable.complement ⊔ h.atom.ogp.bdry ⊤ (!h.side) →
      𝒲.wPsh Atom (Subfunctor.homOfLe (closedSubpresheaf_mono h.atom hSR)) from
    key h.bdry_not_subset_hornSubset (hornSubset_eq_complement_union h)
  intro R hSR hR
  subst hR
  have hmol := h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive) h.side
  have hround : h.atom.ogp.IsRound (h.atom.ogp.bdry ⊤ h.side) := by
    rw [h.atom.bdry_top_eq_boundary h.positive]
    exact h.atom.isAtom.isRound.boundary _ _
  obtain ⟨n, hn⟩ := hmol.exists_krullDim_eq
  have htop := 𝒲.wPsh_homOfLe_closedSubpresheaf_of_eq_complement h.atom n hn hmol hround
    h.rewritable inf_le_left h.sdiff_interior_inter_bdry_not_eq_bdryFull rfl
  exact ((𝒲.wPsh_isStableUnderCobaseChange Atom).of_isPushout
    (isPushout_closedSubpresheaf h.atom h.rewritable.complement
      (h.atom.ogp.bdry ⊤ (!h.side))).flip
    ⟨MorphismProperty.monomorphisms.infer_property _, htop⟩).2

theorem pshAspherical_horn (h : HornData) : 𝒲.PshAspherical Atom (horn h) := by
  have hO := 𝒲.pshAspherical_closedSubpresheaf_of_isMoleculeIn h.atom
    (h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive) (!h.side))
  rw [𝒲.pshAspherical_iff_wPsh_terminal_from Atom 𝒲.aspherical_atom] at hO ⊢
  have e : terminal.from
        (closedSubpresheaf h.atom (h.atom.ogp.bdry ⊤ (!h.side))).toFunctor =
      Subfunctor.homOfLe (closedSubpresheaf_mono h.atom h.bdry_not_subset_hornSubset) ≫
        terminal.from (horn h) := terminal.hom_ext _ _
  rw [e] at hO
  exact MorphismProperty.of_precomp _ _ _ (𝒲.wPsh_oppositeBoundary_horn h) hO

theorem hornInclusions_le_wPsh : hornInclusions ≤ 𝒲.wPsh Atom :=
  𝒲.wDiagSet_eq_wPsh ▸ 𝒲.hornInclusions_le_wDiagSet

theorem wPsh_hornInclusion (h : HornData) : 𝒲.wPsh Atom (hornInclusion h) :=
  𝒲.hornInclusions_le_wPsh _ ⟨h⟩

end Atoms.TestCategory.BasicLocalizer
