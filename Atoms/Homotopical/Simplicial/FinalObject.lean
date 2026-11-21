import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Nerve
import Atoms.Homotopical.Simplicial.RightAnodyne
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

open CategoryTheory Limits Simplicial MorphismProperty HomotopicalAlgebra

universe u v

namespace SSet

variable {X : SSet.{u}}

theorem isFinal_iff_trivialFibration_sliceAtπ [X.Quasicategory] (ω : X _⦋0⦌) :
    IsFinal ω ↔ modelCategoryQuillen.I.rlp (sliceAtπ X ω) := by
  refine ⟨fun h ↦ ?_, isFinal_of_trivialFibration_sliceAtπ⟩
  obtain ⟨s, hs, hω⟩ := exists_section_of_isFinal h
  have : Mono s := mono_of_mono_fac hs
  refine trivialFibration_of_rightFibrations_of_section (rightFibrations_sliceAtπ X ω) s hs ?_
  exact modelCategoryJoyal.rightAnodyneExtensions_of_comp _ s h
    (hω ▸ rightAnodyneExtensions_sliceId X ω)

theorem isFinal_iff_trivialFibration_fiber [X.Quasicategory] (ω : X _⦋0⦌) :
    IsFinal ω ↔ ∀ x : X _⦋0⦌,
      modelCategoryQuillen.I.rlp (pullback.snd (sliceAtπ X ω) (yonedaEquiv.symm x)) :=
  (isFinal_iff_trivialFibration_sliceAtπ ω).trans
    (trivialFibration_sliceAtπ_iff_trivialFibration_fiber ω)

theorem isFinal_iff_extend_boundary [X.Quasicategory] (ω : X _⦋0⦌) :
    IsFinal ω ↔ ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), b.app _ (boundary.lastVertex n) = ω →
      ∃ v : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ v = b :=
  (isFinal_iff_trivialFibration_sliceAtπ ω).trans (trivialFibration_sliceAtπ_iff ω)

open modelCategoryJoyal in
theorem modelCategoryJoyal.isFinal_iff_weakEquivalence_sliceAtπ [X.Quasicategory]
    (ω : X _⦋0⦌) : IsFinal ω ↔ WeakEquivalence (sliceAtπ X ω) := by
  have hπ := rightFibrations_sliceAtπ X ω
  have : InnerFibration (sliceAtπ X ω) := innerFibration_of_rightFibrations hπ
  have : (Under.mk (yonedaEquiv.symm ω)).right.Quasicategory := ‹X.Quasicategory›
  have : Fibration (sliceAtπ X ω) := (fibration_iff_isofibration _).2
    (Isofibration.of_hasLiftingProperty_vertex _ (rightAnodyneExtensions_coherentIso_vertex false _
      hπ))
  rw [isFinal_iff_trivialFibration_sliceAtπ, ← rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp _ ↔ _
  rw [cofibrations_rlp, mem_trivialFibrations_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩

noncomputable def isTerminalOfIsFinal [X.Quasicategory] {ω : X _⦋0⦌} (h : IsFinal ω) :
    IsTerminal (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) ω) :=
  isTerminalOfTrivialFibrationSliceAtπ ((isFinal_iff_trivialFibration_sliceAtπ ω).1 h)

theorem isIso_homMk_of_isFinal [X.Quasicategory] {ω ω' : X _⦋0⦌} (h : IsFinal ω)
    (h' : IsFinal ω') (e : Edge ω ω') :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (V := (SSet.truncation 2).obj X) e) :=
  isIso_of_isTerminal (isTerminalOfIsFinal h) (isTerminalOfIsFinal h') _

private lemma map_const_yonedaEquiv {m : ℕ} (v : Δ[m] ⟶ X) (i : Fin (m + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (yonedaEquiv v) =
      v.app _ (stdSimplex.obj₀Equiv.symm i) :=
  (NatTrans.naturality_apply v _ _).symm.trans rfl

theorem trivialFibration_finalSubcomplex [X.Quasicategory] (h : ∃ ω : X _⦋0⦌, IsFinal ω) :
    modelCategoryQuillen.I.rlp (stdSimplex.isTerminalObj₀.from (finalSubcomplex X : SSet.{u})) := by
  suffices H : ∀ n, HasLiftingProperty (boundary.{u} n).ι
      (stdSimplex.isTerminalObj₀.from (finalSubcomplex X : SSet.{u})) from fun _ _ _ ⟨n⟩ ↦ H n
  intro n
  refine ⟨fun {a b} _ ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨ω, hω⟩ := h
    exact ⟨⟨⟨yonedaEquiv.symm ⟨ω, (mem_finalSubcomplex_obj_zero_iff ω).2 hω⟩, boundary.hom_ext₀,
      stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
  | succ n =>
    have hc := (mem_finalSubcomplex_obj_zero_iff _).1 (a.app _ (boundary.lastVertex n)).2
    obtain ⟨v, hv⟩ := (isFinal_iff_extend_boundary _).1 hc n (a ≫ (finalSubcomplex X).ι) rfl
    have hle : Subcomplex.range v ≤ finalSubcomplex X := by
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
      intro i
      rw [map_const_yonedaEquiv]
      have hi : stdSimplex.obj₀Equiv.symm i ∈
          (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).obj _ := by
        rw [boundary_obj_eq_univ 0 (n + 1)]
        trivial
      have hv' : v.app _ (stdSimplex.obj₀Equiv.symm i) = (a.app _ ⟨_, hi⟩).1 :=
        ConcreteCategory.congr_hom (congr_app hv _) ⟨_, hi⟩
      rw [hv']
      exact (mem_finalSubcomplex_obj_zero_iff _).1 (a.app _ _).2
    refine ⟨⟨⟨Subcomplex.lift v hle, ?_, stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
    rw [← cancel_mono (finalSubcomplex X).ι, Category.assoc, Subcomplex.lift_ι, hv]

private def boundaryVertex (n : ℕ) (j : Fin (n + 2)) : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm j, by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩

private lemma yonedaEquiv_boundary_ι_comp {X : SSet.{u}} {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) (i : Fin (n + 2)) (θ : ⦋0⦌ ⟶ ⦋n⦌) :
    X.map θ.op (yonedaEquiv (boundary.ι i ≫ b)) =
      b.app _ (boundaryVertex n (i.succAbove (θ.toOrderHom 0))) := by
  rw [yonedaEquiv_comp, ← NatTrans.naturality_apply]
  congr 1
  exact Subtype.ext (stdSimplex.obj₀Equiv.injective rfl)

private lemma boundary_ι_comp_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) (σ : X _⦋n + 1⦌)
    (h : ∀ i, X.δ i σ = yonedaEquiv (boundary.ι i ≫ b)) :
    (∂Δ[n + 1]).ι ≫ yonedaEquiv.symm σ = b :=
  boundary.hom_ext fun i ↦ by
    rw [boundary.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, h i, Equiv.symm_apply_apply]

private lemma nonempty_isTerminal_of_isFinal_nerve {C : Type u} [Category.{v} C] {c : C}
    (h : IsFinal (X := nerve C) (nerveEquiv.symm c)) : Nonempty (IsTerminal c) := by
  let t := isTerminalOfIsFinal h
  have hne (y : C) : Nonempty (y ⟶ c) := by
    obtain ⟨e, -⟩ := Truncated.HomotopyCategory.homMk_surjective
      (t.from (Truncated.HomotopyCategory.mk (nerveEquiv.symm y)))
    exact ⟨nerve.homEquiv (Edge.ofTruncated e)⟩
  have hsub (y : C) (f g : y ⟶ c) : f = g := by
    obtain ⟨cs⟩ := (Truncated.HomotopyCategory.homMk_eq_homMk_iff _ _).1
      (t.hom_ext (Truncated.HomotopyCategory.homMk (nerve.edgeMk f).toTruncated)
        (Truncated.HomotopyCategory.homMk (nerve.edgeMk g).toTruncated))
    have cs' : Edge.CompStruct (nerve.edgeMk f) (nerve.edgeMk (𝟙 c)) (nerve.edgeMk g) := by
      rw [nerve.edgeMk_id]
      exact Edge.CompStruct.ofTruncated cs
    exact (Category.comp_id f).symm.trans ((nerve.nonempty_compStruct_iff _ _ _).1 ⟨cs'⟩)
  exact ⟨IsTerminal.ofUniqueHom (fun y ↦ (hne y).some) fun y f ↦ hsub y f _⟩

private lemma exists_extend_boundary_nerve {C : Type u} [Category.{v} C] {c : C}
    (hc : IsTerminal c) (n : ℕ) (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ nerve C)
    (hb : b.app _ (boundary.lastVertex n) = nerveEquiv.symm c) :
    ∃ v : Δ[n + 1] ⟶ nerve C, (∂Δ[n + 1]).ι ≫ v = b := by
  have hedge {x y : (nerve C) _⦋0⦌} (e : (nerve C).Edge x y) :
      ComposableArrows.mk₁ (nerve.homEquiv e) = e.edge :=
    congrArg Edge.edge (nerve.homEquiv.symm_apply_apply e)
  match n, b, hb with
  | 0, b, hb =>
    have hv (i : Fin 2) : yonedaEquiv (boundary.ι i ≫ b) =
        b.app _ (boundaryVertex 0 (i.succAbove 0)) := by
      have := yonedaEquiv_boundary_ι_comp b i (𝟙 _)
      rwa [op_id, Functor.map_id_apply] at this
    let y := nerveEquiv (b.app _ (boundaryVertex 0 0))
    refine ⟨yonedaEquiv.symm (nerve.edgeMk (hc.from y)).edge,
      boundary_ι_comp_yonedaEquiv_symm b _ fun i ↦ ?_⟩
    rw [hv]
    fin_cases i
    · exact (nerve.edgeMk (hc.from y)).tgt_eq.trans hb.symm
    · exact (nerve.edgeMk (hc.from y)).src_eq.trans (nerveEquiv.symm_apply_apply _)
  | 1, b, hb =>
    have hv (i : Fin 3) (k : Fin 2) : (nerve C).δ k (yonedaEquiv (boundary.ι i ≫ b)) =
        b.app _ (boundaryVertex 1 (i.succAbove (k.succAbove 0))) :=
      yonedaEquiv_boundary_ι_comp b i (SimplexCategory.δ k)
    let e₂ : (nerve C).Edge (b.app _ (boundaryVertex 1 0)) (b.app _ (boundaryVertex 1 1)) :=
      Edge.mk _ (hv 2 1) (hv 2 0)
    let e₀ : (nerve C).Edge (b.app _ (boundaryVertex 1 1)) (b.app _ (boundaryVertex 1 2)) :=
      Edge.mk _ (hv 0 1) (hv 0 0)
    let e₁ : (nerve C).Edge (b.app _ (boundaryVertex 1 0)) (b.app _ (boundaryVertex 1 2)) :=
      Edge.mk _ (hv 1 1) (hv 1 0)
    have hc' : IsTerminal (nerveEquiv (b.app _ (boundaryVertex 1 2))) := by
      have hb' : b.app _ (boundaryVertex 1 2) = nerveEquiv.symm c := hb
      rw [hb']
      exact hc
    refine ⟨yonedaEquiv.symm (ComposableArrows.mk₂ (nerve.homEquiv e₂) (nerve.homEquiv e₀)),
      boundary_ι_comp_yonedaEquiv_symm b _ fun i ↦ ?_⟩
    fin_cases i
    · exact (nerve.δ₀_mk₂_eq _ _).trans (hedge e₀)
    · exact (nerve.δ₁_mk₂_eq _ _).trans
        ((congrArg ComposableArrows.mk₁ (hc'.hom_ext _ _)).trans (hedge e₁))
    · exact (nerve.δ₂_mk₂_eq _ _).trans (hedge e₂)
  | n + 2, b, _ => exact (existsUnique_extend_boundary_of_isCoskeletal b).exists

theorem isFinal_nerve_iff {C : Type u} [Category.{v} C] (c : C) :
    IsFinal (X := nerve C) (nerveEquiv.symm c) ↔ Nonempty (IsTerminal c) :=
  ⟨nonempty_isTerminal_of_isFinal_nerve, fun ⟨hc⟩ ↦ isFinal_of_trivialFibration_sliceAtπ
    ((trivialFibration_sliceAtπ_iff _).2 (exists_extend_boundary_nerve hc))⟩

end SSet
