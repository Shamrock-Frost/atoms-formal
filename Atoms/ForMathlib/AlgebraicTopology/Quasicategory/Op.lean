import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Op

open CategoryTheory Limits Simplicial MonoidalCategory

universe u

namespace SSet

private theorem hasLift_of_hasLift_map {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {A B X Y : C} {a : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
    (sq : CommSq a i p b) (h : (F.map_commSq sq).HasLift) : sq.HasLift := by
  obtain ⟨l⟩ := h.exists_lift
  refine ⟨⟨⟨hF.preimage l.l, hF.map_injective ?_, hF.map_injective ?_⟩⟩⟩
  · rw [F.map_comp, hF.map_preimage, l.fac_left]
  · rw [F.map_comp, hF.map_preimage, l.fac_right]

private theorem hasLift_of_arrowIso {C : Type*} [Category* C] {A B A' B' X Y : C} {i : A ⟶ B}
    {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk i') {a : A ⟶ X} {p : X ⟶ Y} {b : B ⟶ Y}
    (sq : CommSq a i p b) {a' : A' ⟶ X} {b' : B' ⟶ Y} (sq' : CommSq a' i' p b')
    (ha : a = e.hom.left ≫ a') (hb : b = e.hom.right ≫ b') (h : sq'.HasLift) : sq.HasLift := by
  obtain ⟨l⟩ := h.exists_lift
  refine ⟨⟨⟨e.hom.right ≫ l.l, ?_, ?_⟩⟩⟩
  · have hw : i ≫ e.hom.right = e.hom.left ≫ i' := (Arrow.w e.hom).symm
    rw [← Category.assoc, hw, Category.assoc, l.fac_left, ha]
  · rw [Category.assoc, l.fac_right, hb]

def arrowIsoOfPreimage {X Y : SSet.{u}} (e : X ≅ Y) (C : Y.Subcomplex)
    (D : X.Subcomplex) (h : C.preimage e.hom = D) : Arrow.mk D.ι ≅ Arrow.mk C.ι :=
  Arrow.isoMk
    { hom := Subcomplex.lift (D.ι ≫ e.hom) (by
        rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff, h])
      inv := Subcomplex.lift (C.ι ≫ e.inv) (by
        rw [← Subcomplex.image_eq_range, Subcomplex.image_le_iff, ← h,
          ← Subcomplex.preimage_comp, Iso.inv_hom_id, Subcomplex.preimage_id])
      hom_inv_id := by
        rw [← cancel_mono D.ι]
        simp
      inv_hom_id := by
        rw [← cancel_mono C.ι]
        simp } e (by simp)

def hornArrowIsoOp (n : ℕ) (i j : Fin (n + 1)) (h : i.rev = j) :
    Arrow.mk Λ[n, j].ι ≅ Arrow.mk (opFunctor.map Λ[n, i].ι) :=
  arrowIsoOfPreimage (stdSimplex.opIso ⦋n⦌).symm Λ[n, i].op Λ[n, j] (h ▸ op_horn i)

theorem isPullback_op_pullback {X S K K' : SSet.{u}} (p : X ⟶ S) (b : K ⟶ S) (e : K.op ≅ K')
    (b' : K' ⟶ S.op) (hb : e.inv ≫ opFunctor.map b = b') :
    IsPullback (opFunctor.map (pullback.fst p b)) (opFunctor.map (pullback.snd p b) ≫ e.hom)
      (opFunctor.map p) b' :=
  ((IsPullback.of_hasPullback p b).map opFunctor).of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [← hb])

instance innerFibration_opFunctor_map {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] :
    InnerFibration (opFunctor.map p) := by
  refine ⟨fun _ _ _ ⟨i, h0, hn⟩ ↦ ?_⟩
  refine (HasLiftingProperty.iff_of_arrow_iso_left
    (hornArrowIsoOp _ i.rev i (Fin.rev_rev i)) _).2 ?_
  refine (Functor.hasLiftingProperty_iff_of_isEquivalence opFunctor _ _).2 ?_
  refine mem_innerFibrations p _ (horn_ι_mem_innerHornInclusions ?_ ?_)
  · rw [Fin.lt_def] at hn ⊢
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at hn ⊢
    omega
  · rw [Fin.lt_def] at h0 ⊢
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at h0 ⊢
    omega

instance quasicategory_op (X : SSet.{u}) [X.Quasicategory] : X.op.Quasicategory :=
  (quasicategory_iff_of_isTerminal (opFunctor.map (terminal.from X))
    ((terminalIsTerminal (C := SSet.{u})).isTerminalObj opFunctor _)).2 inferInstance

theorem nonempty_invStruct_op {X : SSet.{u}} (e : X _⦋1⦌)
    (h : Nonempty (Edge.mk' e).InvStruct) :
    Nonempty (Edge.mk' (opObjEquiv.symm e : X.op _⦋1⦌)).InvStruct := by
  obtain ⟨I⟩ := h
  refine ⟨{ inv := Edge.mk (opObjEquiv.symm I.inv.edge) ?_ ?_
            homInvId := Edge.CompStruct.mk (opObjEquiv.symm I.invHomId.simplex) ?_ ?_ ?_
            invHomId := Edge.CompStruct.mk (opObjEquiv.symm I.homInvId.simplex) ?_ ?_ ?_ }⟩
  all_goals
    have h₁ : (1 : Fin 2).rev = 0 := rfl
    have h₂ : (0 : Fin 2).rev = 1 := rfl
    have h₃ : (0 : Fin 3).rev = 2 := rfl
    have h₄ : (1 : Fin 3).rev = 1 := rfl
    have h₅ : (2 : Fin 3).rev = 0 := rfl
    have h₆ : (0 : Fin 1).rev = 0 := rfl
    simp only [op_δ, op_σ, Edge.mk'_edge, Edge.mk_edge, Edge.id_edge, Equiv.apply_symm_apply,
      h₁, h₂, h₃, h₄, h₅, h₆, Edge.src_eq, Edge.tgt_eq, Edge.CompStruct.d₀, Edge.CompStruct.d₁,
      Edge.CompStruct.d₂]

theorem hasLift_horn_last_of_invStruct {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    [X.Quasicategory] [Y.Quasicategory] {n : ℕ}
    {a : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X} {b : Δ[n + 2] ⟶ Y}
    (sq : CommSq a Λ[n + 2, Fin.last (n + 2)].ι p b)
    (h : Nonempty (Edge.mk' (a.app _ (horn.edge (n + 2) (Fin.last (n + 2))
      (Fin.last (n + 1)).castSucc (Fin.last (n + 2)) (Fin.le_last _) (by simp)))).InvStruct) :
    sq.HasLift := by
  refine hasLift_of_hasLift_map opEquivalence.fullyFaithfulFunctor sq ?_
  let φ := hornArrowIsoOp (n + 2) (Fin.last (n + 2)) 0 (Fin.rev_last _)
  have sq' : CommSq (φ.hom.left ≫ opFunctor.map a) Λ[n + 2, 0].ι (opFunctor.map p)
      (φ.hom.right ≫ opFunctor.map b) := ⟨by
    rw [Category.assoc, ← Functor.map_comp, sq.w, Functor.map_comp, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ opFunctor.map b) (Arrow.w φ.hom)⟩
  refine hasLift_of_arrowIso φ.symm (opEquivalence.functor.map_commSq sq) sq' ?_ ?_
    (hasLift_horn_zero_of_invStruct (opFunctor.map p) sq' ?_)
  · exact (Arrow.inv_hom_id_left_assoc φ _).symm
  · exact (Arrow.inv_hom_id_right_assoc φ _).symm
  · refine (nonempty_invStruct_op _ h).elim fun I ↦ ⟨I.ofEq ?_⟩
    change opObjEquiv.symm (a.app _ _) = opObjEquiv.symm (a.app _ _)
    refine congrArg (fun x ↦ opObjEquiv.symm (a.app _ x)) (Subtype.ext ?_)
    refine stdSimplex.ext _ _ fun i ↦ ?_
    fin_cases i
    · rfl
    · rfl

end SSet
