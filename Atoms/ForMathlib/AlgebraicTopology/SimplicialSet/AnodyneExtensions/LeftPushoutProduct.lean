import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Isofibration
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Left
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial MorphismProperty
  HomotopicalAlgebra

universe u

namespace SSet

private lemma llp_leftFibrations_ι_of_pairing {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (hP : ∀ x : P.II, (P.isUniquelyCodimOneFace x).index rfl ≠ Fin.last _) :
    leftFibrations.llp A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact leftAnodyneExtensions.horn_ι (Fin.lt_last_iff_ne_last.2 (hP c.s))⟩

private lemma index_pairingCore_ne_last {m : ℕ} (k : Fin (m + 1)) (n : ℕ)
    (x : (prodStdSimplex.pairingCore.{u} k n).pairing.II) :
    ((prodStdSimplex.pairingCore.{u} k n).pairing.isUniquelyCodimOneFace x).index rfl ≠
      Fin.last _ := by
  obtain ⟨s, rfl⟩ := (prodStdSimplex.pairingCore k n).equivII.surjective x
  rw [Subcomplex.PairingCore.pairing_isUniquelyCodimOneFace_index]
  exact (Fin.castSucc_lt_last _).ne

private lemma llp_leftFibrations_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (hk : k < Fin.last (m + 1))
    (n : ℕ) : leftFibrations.llp (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  obtain ⟨k, rfl⟩ : ∃ k' : Fin (m + 1), k = k'.castSucc :=
    ⟨k.castPred hk.ne, (Fin.castSucc_castPred _ _).symm⟩
  exact llp_leftFibrations_ι_of_pairing _ (index_pairingCore_ne_last k n)

section

variable {X₁ Y₁ X₂ Y₂ E B : SSet.{u}}

open modelCategoryQuillen in
theorem leftFibrations_pullbackObjObjπ (i : X₁ ⟶ Y₁) [Mono i] {p : E ⟶ B}
    (hp : leftFibrations p) (sq : MonoidalClosed.internalHom.PullbackObjObj i p) :
    leftFibrations sq.π := by
  rintro _ _ _ ⟨k, hk⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_ + 1, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  refine (?_ : leftAnodyneExtensions sq₁₂.ι) _ hp
  intro E' B' p' hp'
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (Arrow.isoMk (Iso.refl _) (β_ _ _) : Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι)]
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[_ + 1, k].ι p'
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  refine (?_ : (MorphismProperty.monomorphisms _).rlp sq₁₃.π) _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _), Subcomplex.unionProd.pushoutObjObj_ι]
  exact llp_leftFibrations_unionProd_ι _ hk _ _ hp'

theorem leftAnodyneExtensions_pushoutObjObjι {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) [Mono i] (hj : leftAnodyneExtensions j) :
    leftAnodyneExtensions sq.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  exact hj _ (leftFibrations_pullbackObjObjπ i hp sq₁₃)

theorem leftAnodyneExtensions_pushoutObjObjι_left {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) [Mono j] (hi : leftAnodyneExtensions i) :
    leftAnodyneExtensions sq.ι :=
  (leftAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Iso.refl _) (β_ _ _) : Arrow.mk sq.flipTensor.ι ≅ Arrow.mk sq.ι)).1
    (leftAnodyneExtensions_pushoutObjObjι sq.flipTensor hi)

end

theorem innerFibration_of_leftFibrations {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : leftFibrations p) : InnerFibration p :=
  ⟨antitone_rlp (fun _ _ _ ⟨i, _, hi⟩ ↦ ⟨i, hi⟩) _ hp⟩

theorem leftAnodyneExtensions_coherentIso_vertex (b : Bool) :
    leftAnodyneExtensions (yonedaEquiv.symm (cond b coherentIso.x₁ coherentIso.x₀) :
      Δ[0] ⟶ coherentIso.{u}) := fun _ _ q hq ↦
  hasLiftingProperty_coherentIso_vertex_of_horn_zero b q fun _ ↦
    hq _ (.intro 0 (Fin.pos_iff_ne_zero.2 Fin.last_pos.ne'))

private lemma exists_compStruct_id_of_hasLiftingProperty_horn_zero {E B : SSet.{u}} (q : E ⟶ B)
    [HasLiftingProperty Λ[2, 0].ι q] {x y : E _⦋0⦌} (e : Edge x y) (τ : B _⦋2⦌)
    (h₂ : B.δ 2 τ = q.app _ e.edge) (h₁ : B.δ 1 τ = q.app _ (E.σ 0 x)) :
    ∃ e' : Edge y x, Nonempty (Edge.CompStruct e e' (Edge.id x)) ∧
      q.app _ e'.edge = B.δ 0 τ := by
  obtain ⟨σ, hσ, hqσ⟩ := exists_simplex_of_hasLiftingProperty_horn q (i := 0)
    (fun j _ ↦ ![e.edge, E.σ 0 x, e.edge] j) (fun j k hj hk hjk ↦ by
      fin_cases j <;> fin_cases k
      all_goals try exact absurd hjk (by decide)
      all_goals try exact (hj rfl).elim
      simp only [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg _ ((δ_comp_σ_succ_apply (S := E) 0 x).trans (Edge.src_eq e).symm))
    τ (fun j hj ↦ by
      fin_cases j
      · exact (hj rfl).elim
      · exact h₁
      · exact h₂)
  have h₁' : E.δ 1 σ = E.σ 0 x := hσ 1 (by decide)
  have h₂' : E.δ 2 σ = e.edge := hσ 2 (by decide)
  refine ⟨Edge.mk (E.δ 0 σ) ((δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ).symm.trans
    ((congrArg _ h₂').trans (Edge.tgt_eq e)))
    ((δ_comp_δ_self_apply (i := 0) σ).trans
      ((congrArg _ h₁').trans (δ_comp_σ_self_apply (S := E) 0 x))),
    ⟨Edge.CompStruct.mk σ h₂' rfl h₁'⟩,
    (δ_naturality_apply q 0 σ).trans (congrArg (B.δ 0) hqσ)⟩

theorem nonempty_invStruct_of_leftFibrations {P Z : SSet.{u}} {r : P ⟶ Z}
    (hr : leftFibrations r) [P.Quasicategory] {x₀ x₁ : P _⦋0⦌} (f : Edge x₀ x₁)
    (h : Nonempty (f.map r).InvStruct) : Nonempty f.InvStruct := by
  obtain ⟨I⟩ := h
  have : HasLiftingProperty Λ[2, 0].ι r := hr _ (.intro 0 (by decide))
  obtain ⟨g, ⟨hg⟩, hrg⟩ := exists_compStruct_id_of_hasLiftingProperty_horn_zero r f
    I.homInvId.simplex I.homInvId.d₂ (I.homInvId.d₁.trans (σ_naturality_apply r 0 x₀).symm)
  obtain ⟨h, ⟨hh⟩, -⟩ := exists_compStruct_id_of_hasLiftingProperty_horn_zero r g
    I.invHomId.simplex (I.invHomId.d₂.trans (hrg.trans I.homInvId.d₀).symm)
    (I.invHomId.d₁.trans (σ_naturality_apply r 0 x₁).symm)
  have h₁ := (Truncated.HomotopyCategory.homMk_comp_homMk hg).trans
    (Truncated.HomotopyCategory.homMk_id _)
  have h₂ := (Truncated.HomotopyCategory.homMk_comp_homMk hh).trans
    (Truncated.HomotopyCategory.homMk_id _)
  have hhf : Truncated.HomotopyCategory.homMk h.toTruncated =
      Truncated.HomotopyCategory.homMk f.toTruncated := by
    rw [← Category.id_comp (Truncated.HomotopyCategory.homMk h.toTruncated), ← h₁,
      Category.assoc, h₂, Category.comp_id]
  rw [← isIso_homMk_iff]
  exact ⟨Truncated.HomotopyCategory.homMk g.toTruncated, h₁,
    (congrArg (Truncated.HomotopyCategory.homMk g.toTruncated ≫ ·) hhf.symm).trans h₂⟩

theorem isofibration_of_leftFibrations {X Y : SSet.{u}} [Y.Quasicategory] {p : X ⟶ Y}
    (hp : leftFibrations p) : Isofibration p :=
  have : InnerFibration p := innerFibration_of_leftFibrations hp
  Isofibration.of_hasLiftingProperty_vertex p (leftAnodyneExtensions_coherentIso_vertex false _ hp)

end SSet
