import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

open CategoryTheory MorphismProperty Simplicial

universe u

namespace SSet

inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) : leftHornInclusions Λ[n + 1, i].ι

def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp

def leftAnodyneExtensions : MorphismProperty SSet.{u} := leftFibrations.llp
deriving RespectsIso

theorem leftHornInclusions_le_J : leftHornInclusions.{u} ≤ modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _⟩ ↦ modelCategoryQuillen.horn_ι_mem_J ..

theorem leftHornInclusions_le_monomorphisms :
    leftHornInclusions.{u} ≤ MorphismProperty.monomorphisms SSet :=
  fun _ _ _ ⟨_, _⟩ ↦ monomorphisms.infer_property _

private lemma leftHornInclusions_eq_iSup :
    leftHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, hi⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, hi⟩, _, _⟩ := h
    exact .intro i hi

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} leftHornInclusions.{u} := by
  rw [leftHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u}
        fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument leftHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [leftHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} leftHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

theorem leftAnodyneExtensions.horn_ι {n : ℕ} {i : Fin (n + 1)} (hi : i < Fin.last n) :
    leftAnodyneExtensions.{u} Λ[n, i].ι := by
  obtain _ | n := n
  · exact absurd hi (by simp)
  · exact le_llp_rlp _ _ (.intro i hi)

theorem innerAnodyneExtensions_le_leftAnodyneExtensions :
    innerAnodyneExtensions.{u} ≤ leftAnodyneExtensions := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  refine antitone_llp (antitone_rlp ?_)
  rintro _ _ _ ⟨i, -, hi⟩
  exact .intro i hi

theorem leftAnodyneExtensions_stdSimplex_δ_one :
    leftAnodyneExtensions.{u} (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) := by
  intro E B q hq
  have : HasLiftingProperty Λ[1, 0].ι q := hq _ (.intro 0 (by decide))
  have h₁ : stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ 1 = (horn.{u} 1 0).ι :=
    horn.hom_ext' fun j hj ↦ by
      obtain rfl : j = 1 := by
        fin_cases j
        · exact (hj rfl).elim
        · rfl
      rw [horn.ι_ι, ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext
        (horn.ι 0 1 hj ≫ stdSimplex.isTerminalObj₀.from _) (𝟙 _), Category.id_comp]
  refine ⟨fun {a b} sq ↦ ?_⟩
  have sq' : CommSq (stdSimplex.isTerminalObj₀.from _ ≫ a) Λ[1, 0].ι q b :=
    ⟨(Category.assoc _ _ _).trans ((congrArg _ sq.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) h₁)))⟩
  obtain ⟨l⟩ := (HasLiftingProperty.sq_hasLift sq').exists_lift
  refine ⟨⟨⟨l.l, ?_, l.fac_right⟩⟩⟩
  rw [← horn.ι_ι 0 1 (by decide), Category.assoc, l.fac_left, ← Category.assoc,
    stdSimplex.isTerminalObj₀.hom_ext (horn.ι 0 1 _ ≫ stdSimplex.isTerminalObj₀.from _) (𝟙 _),
    Category.id_comp]

theorem leftAnodyneExtensions_stdSimplex_δ_of_ne_zero {i : Fin 3} (hi : i ≠ 0) :
    leftAnodyneExtensions.{u} (stdSimplex.δ i : Δ[1] ⟶ Δ[2]) := by
  have hΛ := leftAnodyneExtensions.horn_ι.{u} (n := 2) (i := 0) (by decide)
  obtain rfl | rfl : i = 1 ∨ i = 2 := by
    revert hi
    fin_cases i <;> decide
  · rw [← horn.ι_ι 0 1 (by decide)]
    exact leftFibrations.llp.comp_mem _ _ (leftFibrations.llp.of_isPushout
      horn₂₀.isPushout.flip leftAnodyneExtensions_stdSimplex_δ_one) hΛ
  · rw [← horn.ι_ι 0 2 (by decide)]
    exact leftFibrations.llp.comp_mem _ _ (leftFibrations.llp.of_isPushout
      horn₂₀.isPushout leftAnodyneExtensions_stdSimplex_δ_one) hΛ

end SSet
