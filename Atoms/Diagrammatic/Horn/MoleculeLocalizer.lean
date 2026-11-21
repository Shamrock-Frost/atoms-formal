import Atoms.Diagrammatic.ClosedSubpresheafPushout
import Atoms.Diagrammatic.Horn.Basic
import Atoms.Homotopical.Localizer.LeftProper

open Order Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {W : MorphismProperty DiagSet.{u}}

private theorem homOfLe_closedSubpresheaf_mem_of_eq [hW : Homotopical.IsALocalizer W] (T : Atom)
    {S R : LowerSet T.ogp} (h : S ≤ R) (e : S = R) :
    W (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) := by
  subst e
  have : Subfunctor.homOfLe (closedSubpresheaf_mono T h) =
      𝟙 (closedSubpresheaf T S).toFunctor := by
    ext
    rfl
  rw [this]
  exact hW.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property _)

theorem terminal_from_ball_mem_of_dimension_eq_zero [hW : Homotopical.IsALocalizer W]
    (U : Atom) (h0 : U.dimension = 0) : W (terminal.from (ball U)) := by
  have : IsIso (toAtomPoint U) := isIso_toAtomPoint_of_dimension_eq_zero h0
  rw [show terminal.from (ball U) =
    uliftYoneda.{u}.map (toAtomPoint U) ≫ terminal.from (ball atomPoint) from terminal.hom_ext _ _]
  have : IsIso (uliftYoneda.{u}.map (toAtomPoint U)) := inferInstance
  exact W.comp_mem _ _ (hW.isomorphisms_le _ ‹_›)
    (hW.isomorphisms_le _ (isIso_of_isTerminal isTerminalBallAtomPoint terminalIsTerminal _))

section Induction

variable {m : ℕ} [hW : Homotopical.IsALocalizer W]
  (hball : ∀ U : Atom, U.dimension ≤ m → W (terminal.from (ball U)))
include hball

theorem terminal_from_closure_singleton_mem_of_ball (T : Atom) (x : T.ogp)
    (hx : grade ℕ x ≤ m) :
    W (terminal.from (closedSubpresheaf T (LowerSet.Iic x)).toFunctor) := by
  have himg : Atom.map (Atom.closureIncl T x) ⊤ = LowerSet.Iic x :=
    Atom.map_closureInclOGP_top T x
  rw [← himg]
  refine hW.terminal_from_of_iso (closedSubpresheafImageIso (Atom.closureIncl T x)
    (Atom.isInclusionHom_closureIncl T x) ⊤).symm ?_
  have : IsIso (closedSubpresheaf (Atom.ofClosure T x) ⊤).ι :=
    (Subfunctor.eq_top_iff_isIso _).1 (closedSubpresheaf_univ _)
  exact hW.terminal_from_of_iso (asIso (closedSubpresheaf (Atom.ofClosure T x) ⊤).ι)
    (hball _ (by rw [Atom.dimension_ofClosure]; exact hx))

theorem terminal_from_closedSubpresheaf_mem_of_ball (T : Atom)
    {S : LowerSet T.ogp} (hS : IsMoleculeIn T.ogp S) (hd : krullDim S ≤ m) :
    W (terminal.from (closedSubpresheaf T S).toFunctor) := by
  suffices key : ∀ d : ℕ, d ≤ m → ∀ {S : LowerSet T.ogp},
      IsMoleculeIn T.ogp S → krullDim S ≤ d →
      W (terminal.from (closedSubpresheaf T S).toFunctor) from
    key m le_rfl hS hd
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro hdm S hS hd
  induction hS with
  | point x hx =>
    exact terminal_from_closure_singleton_mem_of_ball hball T x
      (by rw [isMin_iff_eq_bot.1 (hx.grade ℕ)]; exact Nat.zero_le m)
  | atom t _ _ _ =>
    rw [LowerSet.krullDim_Iic, Nat.cast_le] at hd
    exact terminal_from_closure_singleton_mem_of_ball hball T t (hd.trans hdm)
  | paste k V₁ V₂ U hpaste hV₁ _ hk ih₁ ih₂ =>
    have hkd : k < d := by
      have := (hk.trans_le (min_le_left _ _)).trans_le
        ((LowerSet.krullDim_mono hpaste.left_le).trans hd)
      exact_mod_cast this
    have hI : W (terminal.from (closedSubpresheaf T (V₁ ⊓ V₂)).toFunctor) := by
      rw [hpaste.inf_eq_output]
      exact ihd k hkd (hkd.le.trans hdm) (hV₁.boundary k true) (krullDim_boundary_le V₁ k true)
    rw [← hpaste.sup_eq]
    exact hW.of_isPushout_of_mono (isPushout_closedSubpresheaf T V₁ V₂)
      (IsPushout.of_id_fst (f := 𝟙 (⊤_ DiagSet.{u}))) (terminal.from _) (terminal.from _)
      (terminal.from _) (terminal.from _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)
      (terminal.hom_ext _ _) (terminal.hom_ext _ _) hI
      (ih₁ ((LowerSet.krullDim_mono hpaste.left_le).trans hd))
      (ih₂ ((LowerSet.krullDim_mono hpaste.right_le).trans hd))

theorem homOfLe_mem_of_isMoleculeIn_of_ball (T : Atom) {S R : LowerSet T.ogp}
    (h : S ≤ R) (hS : IsMoleculeIn T.ogp S) (hR : IsMoleculeIn T.ogp R)
    (hd : krullDim R ≤ m) : W (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) :=
  hW.of_terminal_from _
    (terminal_from_closedSubpresheaf_mem_of_ball hball T hS ((LowerSet.krullDim_mono h).trans hd))
    (terminal_from_closedSubpresheaf_mem_of_ball hball T hR hd)

theorem homOfLe_mem_of_eq_complement_of_ball (T : Atom) (n : ℕ) :
    n ≤ m → ∀ {U V : LowerSet T.ogp}, krullDim U = n → IsMoleculeIn T.ogp U →
      T.ogp.IsRound U → ∀ (hV : T.ogp.IsRewritableSubmolecule V U)
      {S R : LowerSet T.ogp} (h : S ≤ R), S = T.ogp.bdryFull U →
        R = hV.complement →
        W (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) := by
  induction n with
  | zero =>
    intro _ U V hdim _ _ hV S R h hS hR
    have hdim0 : krullDim U = 0 := by exact_mod_cast hdim
    exact homOfLe_closedSubpresheaf_mem_of_eq T h (hS.trans ((bdryFull_eq_bot hdim0.le).trans
      ((hV.complement_eq_bot_of_krullDim_eq_zero hdim0).symm.trans hR.symm)))
  | succ k ih =>
    intro hnm U V hdim hU hr hV S R h hS hR
    have hn' : krullDim U = k + 1 := by rw [hdim]; push_cast; rfl
    obtain ⟨b⟩ := nonempty_rewritableBlock hV hn'
    obtain ⟨hL, hRt, hF, hA⟩ := b.outer_boundary hr hV hn'
    have hI : b.left ⊓ b.right = (b.rewritable false).complement :=
      SetLike.coe_injective (b.coe_inf_eq_complement hV hn')
    have hFI : T.ogp.bdry U false ⊓ T.ogp.bdry U true ≤ b.left ⊓ b.right := inf_le_inf hL hRt
    have hmid := ih (by omega) hA (b.isMoleculeIn_middle.boundary k false)
      (b.isRound_input hr hn') (b.rewritable false) hFI hF hI
    have hpos : 0 < krullDim U := by rw [hn']; exact_mod_cast k.succ_pos
    have hbf : IsMoleculeIn T.ogp (T.ogp.bdry U false) := hU.bdry hpos false
    have hbt : IsMoleculeIn T.ogp (T.ogp.bdry U true) := hU.bdry hpos true
    have hRU : b.left ⊔ b.right ≤ U := sup_le b.left_le b.right_le
    obtain rfl : R = b.left ⊔ b.right := hR.trans
      (SetLike.coe_injective (b.coe_sup_eq_complement hV.isSubmoleculeOf.isMoleculeIn)).symm
    subst hS
    have hkm : (krullDim U : WithBot ℕ∞) ≤ m := hdim.le.trans (by exact_mod_cast hnm)
    exact hW.of_isPushout_of_mono
      (isPushout_closedSubpresheaf T (T.ogp.bdry U false) (T.ogp.bdry U true))
      (isPushout_closedSubpresheaf T b.left b.right)
      (Subfunctor.homOfLe (closedSubpresheaf_mono T hFI))
      (Subfunctor.homOfLe (closedSubpresheaf_mono T hL))
      (Subfunctor.homOfLe (closedSubpresheaf_mono T hRt))
      (Subfunctor.homOfLe (closedSubpresheaf_mono T h)) rfl rfl rfl rfl hmid
      (homOfLe_mem_of_isMoleculeIn_of_ball hball T hL hbf b.isMoleculeIn_left
        ((LowerSet.krullDim_mono (le_sup_left.trans hRU)).trans hkm))
      (homOfLe_mem_of_isMoleculeIn_of_ball hball T hRt hbt b.isMoleculeIn_right
        ((LowerSet.krullDim_mono (le_sup_right.trans hRU)).trans hkm))

theorem terminal_from_horn_mem_of_ball (h : HornData) (hd : h.atom.dimension ≤ m + 1) :
    W (terminal.from (horn h)) := by
  have hdim : ∀ α : Bool,
      krullDim (h.atom.ogp.bdry ⊤ α) = (h.atom.dimension - 1 : ℕ) := fun α ↦ by
    rw [h.atom.bdry_top_eq_boundary h.positive]
    exact h.atom.isMolecule.krullDim_boundary
      (by rw [LowerSet.krullDim_top, h.atom.krullDim_eq_dimension]; exact_mod_cast Nat.sub_le _ 1) α
  have hle : h.atom.dimension - 1 ≤ m := by omega
  have hmol : ∀ α : Bool, IsMoleculeIn h.atom.ogp (h.atom.ogp.bdry ⊤ α) := fun α ↦
    h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive) α
  have hround : h.atom.ogp.IsRound (h.atom.ogp.bdry ⊤ h.side) := by
    rw [h.atom.bdry_top_eq_boundary h.positive]
    exact h.atom.isAtom.isRound.boundary _ _
  have hV := h.rewritable
  have htop := homOfLe_mem_of_eq_complement_of_ball hball h.atom (h.atom.dimension - 1) hle
    (hdim h.side) (hmol h.side) hround hV inf_le_left
    h.sdiff_interior_inter_bdry_not_eq_bdryFull rfl
  have hj := (hW.isStableUnderCobaseChange.of_isPushout
    (isPushout_closedSubpresheaf h.atom hV.complement (h.atom.ogp.bdry ⊤ (!h.side))).flip
    ⟨MorphismProperty.monomorphisms.infer_property _, htop⟩).2
  have hO := terminal_from_closedSubpresheaf_mem_of_ball hball h.atom
    (hmol (!h.side)) ((hdim (!h.side)).le.trans (by exact_mod_cast hle))
  have hU := hW.terminal_from_of_mem _ hj hO
  rw [horn, hornSubset_eq_complement_union h]
  exact hU

end Induction

theorem terminal_from_ball_mem_of_inclusions {V : MorphismProperty DiagSet.{u}}
    [hV : Homotopical.IsALocalizer V]
    (h : ∀ {U T : Atom} (f : U ⟶ T), IsInclusionHom f → V (uliftYoneda.{u}.map f)) (U : Atom) :
    V (terminal.from (ball U)) := by
  obtain ⟨f, hf⟩ := exists_inclusion_atomPoint U
  have hfg : V (uliftYoneda.{u}.map f ≫ uliftYoneda.{u}.map (toAtomPoint U)) := by
    rw [← uliftYoneda.{u}.map_comp, Subsingleton.elim (f ≫ toAtomPoint U) (𝟙 _),
      uliftYoneda.{u}.map_id]
    exact hV.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property _)
  have hg : V (uliftYoneda.{u}.map (toAtomPoint U)) := V.of_precomp _ _ (h f hf) hfg
  have heq : terminal.from (ball U) =
      uliftYoneda.{u}.map (toAtomPoint U) ≫ terminal.from (ball atomPoint) := terminal.hom_ext _ _
  rw [heq]
  exact V.comp_mem _ _ hg (hV.isomorphisms_le _
    (isIso_of_isTerminal isTerminalBallAtomPoint terminalIsTerminal _))

end Atoms.Diagrammatic
