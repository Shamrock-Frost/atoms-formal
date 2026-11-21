import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial MorphismProperty
  HomotopicalAlgebra

universe u

namespace SSet

private lemma index_op {X : SSet.{u}} {x y : X.S} (hxy : x.IsUniquelyCodimOneFace y) {d : ℕ}
    (hd : x.dim = d) : hxy.op.index hd = (hxy.index hd).rev := by
  obtain ⟨d', x, rfl⟩ := x.mk_surjective
  obtain ⟨d'', y, rfl⟩ := y.mk_surjective
  obtain rfl : d'' = d' + 1 := hxy.dim_eq
  obtain rfl : d' = d := hd
  refine ((hxy.op.δ_eq_iff rfl _).1 ?_).symm
  have h := hxy.δ_index rfl
  simp only [S.cast_simplex_rfl] at h
  change X.op.δ _ (opObjEquiv.symm y) = opObjEquiv.symm x
  rw [op_δ, Fin.rev_rev, Equiv.apply_symm_apply, h]

private lemma llp_rightFibrations_ι_of_pairing {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (hP : ∀ x : P.II, (P.isUniquelyCodimOneFace x).index rfl ≠ 0) :
    rightFibrations.llp A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact rightAnodyneExtensions.horn_ι (Fin.pos_iff_ne_zero.mpr (hP c.s))⟩

private lemma index_ofIso_op_ne_zero {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex}
    (Q : A.Pairing) [Q.IsProper]
    (hQ : ∀ x : Q.II, (Q.isUniquelyCodimOneFace x).index rfl ≠ Fin.last _) (e : Y ≅ X.op)
    (hA : A.op.preimage e.hom = B) (x : (Q.op.ofIso e hA).II) :
    ((Q.op.ofIso e hA).isUniquelyCodimOneFace x).index rfl ≠ 0 := by
  obtain ⟨b, hb⟩ := x
  obtain ⟨a, rfl⟩ := (Subcomplex.N.orderIsoOfIso e hA).symm.surjective b
  simp only [Subcomplex.Pairing.ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
  have h₁ := Subcomplex.Pairing.ofIso_index Q.op e hA ⟨a, hb⟩ rfl
  have h₂ := index_op (Q.isUniquelyCodimOneFace ⟨_, hb⟩) rfl
  intro h
  have h₃ : ((Q.isUniquelyCodimOneFace ⟨_, hb⟩).index rfl).rev = 0 :=
    h₂.symm.trans (h₁.symm.trans h)
  exact hQ _ (by rw [← Fin.rev_rev ((Q.isUniquelyCodimOneFace ⟨_, hb⟩).index rfl), h₃,
    Fin.rev_zero])

private lemma index_pairingCore_ne_last {m : ℕ} (k : Fin (m + 1)) (n : ℕ)
    (x : (prodStdSimplex.pairingCore.{u} k n).pairing.II) :
    ((prodStdSimplex.pairingCore.{u} k n).pairing.isUniquelyCodimOneFace x).index rfl ≠
      Fin.last _ := by
  obtain ⟨s, rfl⟩ := (prodStdSimplex.pairingCore k n).equivII.surjective x
  rw [Subcomplex.PairingCore.pairing_isUniquelyCodimOneFace_index]
  exact (Fin.castSucc_lt_last _).ne

private lemma llp_rightFibrations_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (hk : 0 < k) (n : ℕ) :
    rightFibrations.llp (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  by_cases h : k = Fin.last (m + 1)
  · subst h
    obtain ⟨hA, -⟩ : ∃ hA, prodStdSimplex.pairing.{u} (Fin.last (m + 1)) n =
        (prodStdSimplex.pairingCore (0 : Fin (m + 1)) n).pairing.op.ofIso
          (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
            Functor.Monoidal.μIso opFunctor _ _) hA := ⟨_, dif_pos rfl⟩
    exact llp_rightFibrations_ι_of_pairing _
      (index_ofIso_op_ne_zero _ (index_pairingCore_ne_last 0 n) _ hA)
  · exact innerAnodyneExtensions_le_rightAnodyneExtensions _
      (prodStdSimplex.innerAnodyneExtensions_unionProd_ι k hk (Fin.lt_last_iff_ne_last.2 h) n)

section

variable {X₁ Y₁ X₂ Y₂ E B : SSet.{u}}

open modelCategoryQuillen in
theorem rightFibrations_pullbackObjObjπ (i : X₁ ⟶ Y₁) [Mono i] {p : E ⟶ B}
    (hp : rightFibrations p) (sq : MonoidalClosed.internalHom.PullbackObjObj i p) :
    rightFibrations sq.π := by
  rintro _ _ _ ⟨k, hk⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_ + 1, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  refine (?_ : rightAnodyneExtensions sq₁₂.ι) _ hp
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
  exact llp_rightFibrations_unionProd_ι _ hk _ _ hp'

theorem rightAnodyneExtensions_pushoutObjObjι {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) [Mono i] (hj : rightAnodyneExtensions j) :
    rightAnodyneExtensions sq.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  exact hj _ (rightFibrations_pullbackObjObjπ i hp sq₁₃)

theorem rightAnodyneExtensions_pushoutObjObjι_left {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂}
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) [Mono j] (hi : rightAnodyneExtensions i) :
    rightAnodyneExtensions sq.ι :=
  (rightAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Iso.refl _) (β_ _ _) : Arrow.mk sq.flipTensor.ι ≅ Arrow.mk sq.ι)).1
    (rightAnodyneExtensions_pushoutObjObjι sq.flipTensor hi)

end

end SSet
