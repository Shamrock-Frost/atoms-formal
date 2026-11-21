import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

section Horns

private lemma rlp_J_of_hasLiftingProperty {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (h₁ : ∀ i : Fin 2, HasLiftingProperty Λ[1, i].ι p)
    (h₀ : ∀ n : ℕ, HasLiftingProperty Λ[n + 2, 0].ι p)
    (hl : ∀ n : ℕ, HasLiftingProperty Λ[n + 2, Fin.last (n + 2)].ι p) :
    modelCategoryQuillen.J.rlp p := by
  intro _ _ _ hf
  simp only [modelCategoryQuillen.J, iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  cases n with
  | zero => exact h₁ i
  | succ n =>
    by_cases hi0 : i = 0
    · subst hi0
      exact h₀ n
    by_cases hil : i = Fin.last _
    · subst hil
      exact hl n
    exact mem_innerFibrations p _ (horn_ι_mem_innerHornInclusions
      ((Fin.pos_iff_ne_zero' i).2 hi0) (Fin.lt_last_iff_ne_last.2 hil))

private lemma kanComplex_of_rlp {X : SSet.{u}} (h : modelCategoryQuillen.J.rlp (terminal.from X)) :
    X.KanComplex :=
  (modelCategoryQuillen.fibration_iff _).2 h

private lemma kanComplex_of_isTerminal {T : SSet.{u}} (hT : IsTerminal T) : T.KanComplex :=
  have : IsIso (terminal.from T) := isIso_of_isTerminal hT terminalIsTerminal _
  kanComplex_of_rlp (rlp_of_isIso _ _)

private lemma hasLiftingProperty_horn_one_terminal (X : SSet.{u}) (i : Fin 2) :
    HasLiftingProperty Λ[1, i].ι (terminal.from X) := by
  have hrev : i.rev ≠ i := by
    fin_cases i <;> decide
  refine ⟨fun {a _} _ ↦ ⟨⟨⟨stdSimplex.isTerminalObj₀.from Δ[1] ≫ horn.ι i i.rev hrev ≫ a,
    horn.hom_ext' fun j hj ↦ ?_, terminal.hom_ext _ _⟩⟩⟩⟩
  obtain rfl : j = i.rev := by
    revert j
    fin_cases i <;> decide
  rw [horn.ι_ι_assoc, ← Category.assoc,
    stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.δ i.rev ≫ _) (𝟙 _), Category.id_comp]

private lemma hasLiftingProperty_horn_one_one {E B : SSet.{u}} [B.Quasicategory] (q : E ⟶ B)
    (hB : ∀ e : B _⦋1⦌, Nonempty (Edge.mk' e).InvStruct)
    (hq : ∀ n : ℕ, HasLiftingProperty Λ[n + 1, 0].ι q) : HasLiftingProperty Λ[1, 1].ι q := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨G, hG⟩ := exists_coherentIso_extension (Edge.mk' (yonedaEquiv b)) (hB _).some
  have hGb : yonedaEquiv.symm coherentIso.hom.edge ≫ G = b :=
    yonedaEquiv.injective (by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hG]
      rfl)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have sq' : CommSq (horn.ι 1 0 h01 ≫ a)
      (yonedaEquiv.symm (cond true coherentIso.x₁ coherentIso.x₀) : Δ[0] ⟶ coherentIso.{u}) q G :=
    ⟨by rw [Category.assoc, sq.w, horn.ι_ι_assoc, ← hGb, ← Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, coherentIso.hom.tgt_eq]; rfl⟩
  obtain ⟨l⟩ := ((hasLiftingProperty_coherentIso_vertex_of_horn_zero true q hq).sq_hasLift
    sq').exists_lift
  refine ⟨⟨⟨yonedaEquiv.symm coherentIso.hom.edge ≫ l.l, horn.hom_ext' fun j hj ↦ ?_, by
    rw [Category.assoc, l.fac_right, hGb]⟩⟩⟩
  obtain rfl : j = 0 := by
    fin_cases j
    · rfl
    · exact (hj rfl).elim
  rw [horn.ι_ι_assoc, ← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm,
    coherentIso.hom.tgt_eq]
  exact l.fac_left

end Horns

theorem kanComplex_iff_nonempty_invStruct (X : SSet.{u}) [X.Quasicategory] :
    X.KanComplex ↔ ∀ e : X _⦋1⦌, Nonempty (Edge.mk' e).InvStruct := by
  refine ⟨fun _ ↦ nonempty_invStruct_of_kanComplex X, fun h ↦ ?_⟩
  have := kanComplex_of_isTerminal (terminalIsTerminal (C := SSet.{u}))
  exact kanComplex_of_rlp (rlp_J_of_hasLiftingProperty _ (hasLiftingProperty_horn_one_terminal X)
    (fun _ ↦ ⟨fun sq ↦ hasLift_horn_zero_of_invStruct _ sq (h _)⟩)
    (fun _ ↦ ⟨fun sq ↦ hasLift_horn_last_of_invStruct _ sq (h _)⟩))

section Core

instance innerFibration_core_ι (X : SSet.{u}) : InnerFibration X.core.ι :=
  ⟨fun _ _ _ ⟨_, _, _⟩ ↦ ⟨fun {a b} sq ↦ by
    have hr : Subcomplex.range b ≤ X.core := by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      exact mem_core_of_horn b a sq.w.symm
    exact ⟨⟨⟨Subcomplex.lift b hr, by
      rw [← cancel_mono X.core.ι, Category.assoc, Subcomplex.lift_ι, sq.w],
      Subcomplex.lift_ι _ _⟩⟩⟩⟩⟩

instance quasicategory_core (X : SSet.{u}) [X.Quasicategory] : (X.core : SSet.{u}).Quasicategory :=
  quasicategory_of_innerFibration X.core.ι

theorem nonempty_invStruct_of_core_ι {X : SSet.{u}} (e : (X.core : SSet.{u}) _⦋1⦌)
    (he : Nonempty (Edge.mk' (X.core.ι.app _ e)).InvStruct) : Nonempty (Edge.mk' e).InvStruct := by
  obtain ⟨I⟩ := he
  have hinv : I.inv.edge ∈ X.core.obj _ := edge_mem_core_of_isIso _ I.invStructInv.isIso_homMk
  have hσ (σ : X _⦋2⦌) (h₂ : X.δ 2 σ ∈ X.core.obj _) (h₀ : X.δ 0 σ ∈ X.core.obj _) :
      σ ∈ X.core.obj _ :=
    mem_core_of_δ_mem_core σ 1 fun j hj ↦ by
      fin_cases j
      · exact h₀
      · exact (hj rfl).elim
      · exact h₂
  exact ⟨{ inv := Edge.mk ⟨I.inv.edge, hinv⟩ (Subtype.ext I.inv.src_eq) (Subtype.ext I.inv.tgt_eq)
           homInvId := Edge.CompStruct.mk ⟨I.homInvId.simplex, hσ _
              (by rw [I.homInvId.d₂]; exact e.2) (by rw [I.homInvId.d₀]; exact hinv)⟩
              (Subtype.ext I.homInvId.d₂) (Subtype.ext I.homInvId.d₀) (Subtype.ext I.homInvId.d₁)
           invHomId := Edge.CompStruct.mk ⟨I.invHomId.simplex, hσ _
              (by rw [I.invHomId.d₂]; exact hinv) (by rw [I.invHomId.d₀]; exact e.2)⟩
              (Subtype.ext I.invHomId.d₂) (Subtype.ext I.invHomId.d₀)
              (Subtype.ext I.invHomId.d₁) }⟩

instance kanComplex_core (X : SSet.{u}) [X.Quasicategory] : (X.core : SSet.{u}).KanComplex :=
  (kanComplex_iff_nonempty_invStruct _).2 fun e ↦
    nonempty_invStruct_of_core_ι e ((isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ e.2))

def coreLiftEquiv (K X : SSet.{u}) [K.KanComplex] :
    (K ⟶ (X.core : SSet.{u})) ≃ (K ⟶ X) where
  toFun g := g ≫ X.core.ι
  invFun f := Subcomplex.lift f (range_le_core f (nonempty_invStruct_of_kanComplex K))
  left_inv g := by
    rw [← cancel_mono X.core.ι, Subcomplex.lift_ι]
  right_inv f := Subcomplex.lift_ι _ _

@[simp]
lemma coreLiftEquiv_apply (K X : SSet.{u}) [K.KanComplex] (g : K ⟶ (X.core : SSet.{u})) :
    coreLiftEquiv K X g = g ≫ X.core.ι :=
  rfl

instance isofibration_core_ι (X : SSet.{u}) : Isofibration X.core.ι where
  exists_lift _ _ g hg := by
    have hg' : g.edge ∈ X.core.obj _ := edge_mem_core_of_isIso g hg.some.isIso_homMk
    exact ⟨_, Edge.mk (⟨g.edge, hg'⟩ : (X.core : SSet.{u}) _⦋1⦌) (Subtype.ext g.src_eq) rfl,
      (nonempty_invStruct_of_core_ι _ ⟨hg.some.ofEq rfl⟩).map fun I ↦ I.ofEq rfl, rfl⟩

end Core

section RightFibrations

theorem kanFibration_of_rightFibrations {X Y : SSet.{u}} {p : X ⟶ Y} (hp : rightFibrations p)
    [Y.KanComplex] : modelCategoryQuillen.J.rlp p := by
  have := innerFibration_of_rightFibrations hp
  have := quasicategory_of_innerFibration p
  have hr (n : ℕ) (i : Fin (n + 2)) (h0 : 0 < i) : HasLiftingProperty Λ[n + 1, i].ι p :=
    hp _ (horn_ι_mem_rightHornInclusions h0)
  refine rlp_J_of_hasLiftingProperty p (fun i ↦ ?_)
    (fun _ ↦ ⟨fun sq ↦ hasLift_horn_zero_of_invStruct p sq
      (nonempty_invStruct_of_rightFibrations hp _
        ⟨(nonempty_invStruct_of_kanComplex Y _).some.ofEq rfl⟩)⟩)
    (fun _ ↦ hr _ _ (Fin.pos_iff_ne_zero.2 (Fin.last_pos'.ne')))
  fin_cases i
  · exact ⟨fun sq ↦ hasLift_horn_one_zero_of_rightFibrations hp sq
      (nonempty_invStruct_of_kanComplex Y _)⟩
  · exact hr 0 1 (by decide)

theorem kanComplex_of_rightFibrations {X Y : SSet.{u}} {p : X ⟶ Y} (hp : rightFibrations p)
    [Y.KanComplex] : X.KanComplex := by
  have := innerFibration_of_rightFibrations hp
  have := quasicategory_of_innerFibration p
  exact (kanComplex_iff_nonempty_invStruct X).2 fun _ ↦ nonempty_invStruct_of_rightFibrations hp _
    ⟨(nonempty_invStruct_of_kanComplex Y _).some.ofEq rfl⟩

theorem kanComplex_fiber_of_rightFibrations {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : rightFibrations p) (y : Y _⦋0⦌) :
    (pullback p (yonedaEquiv.symm y : Δ[0] ⟶ Y)).KanComplex :=
  have := kanComplex_of_isTerminal stdSimplex.isTerminalObj₀.{u}
  kanComplex_of_rightFibrations
    (MorphismProperty.pullback_snd (P := rightHornInclusions.rlp) _ _ hp)

end RightFibrations

theorem kanFibration_coreMap {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory] (p : X ⟶ Y)
    [Isofibration p] : modelCategoryQuillen.J.rlp (coreMap p) := by
  have : InnerFibration (coreMap p) :=
    ⟨fun _ _ _ ⟨k, h0, hn⟩ ↦ hasLiftingProperty_horn_coreMap_of_hasLift p k fun _ _ sq ↦
      (mem_innerFibrations p _ (.intro k h0 hn) : HasLiftingProperty _ _).sq_hasLift sq⟩
  refine rlp_J_of_hasLiftingProperty _ (fun i ↦ ?_)
    (fun n ↦ hasLiftingProperty_horn_zero_coreMap p (n + 1))
    (fun _ ↦ hasLiftingProperty_horn_coreMap_of_hasLift p _ fun a _ sq ↦
      hasLift_horn_last_of_invStruct p sq
        ((isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ (a.app _ _).2)))
  fin_cases i
  · exact hasLiftingProperty_horn_zero_coreMap p 0
  · exact hasLiftingProperty_horn_one_one (coreMap p) (nonempty_invStruct_of_kanComplex _)
      (hasLiftingProperty_horn_zero_coreMap p)

end SSet
