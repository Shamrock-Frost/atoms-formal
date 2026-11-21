import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.SliceJoin
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra

universe u

namespace SSet

open modelCategoryJoyal

theorem isFinal_iff_of_trivialFibration {E B : SSet.{u}} [E.Quasicategory] [B.Quasicategory]
    {p : E ⟶ B} (hp : modelCategoryQuillen.I.rlp p) (x : E _⦋0⦌) :
    IsFinal (p.app _ x) ↔ IsFinal x := by
  have := weakEquivalence_of_rlp_I hp
  exact isFinal_iff_of_weakEquivalence p x

theorem isFinal_sliceRes_iff {K' K X : SSet.{u}} [X.Quasicategory] {i : K' ⟶ K}
    (hi : leftAnodyneExtensions i) (d : K ⟶ X) (w : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    IsFinal ((sliceRes i (Under.mk d)).app _ w) ↔ IsFinal w :=
  have : ((slice K).obj (Under.mk d)).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs X.Quasicategory)
  have : ((slice K').obj (Under.mk (i ≫ (Under.mk d).hom))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs X.Quasicategory)
  isFinal_iff_of_trivialFibration (trivialFibration_sliceRes hi d) w

theorem modelCategoryJoyal.weakEquivalence_slice_map {K X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (F : X ⟶ Y) [WeakEquivalence F] (d : K ⟶ X) :
    WeakEquivalence ((slice K).map (Under.homMk F rfl : Under.mk d ⟶ Under.mk (d ≫ F))) := by
  have : WeakEquivalence (Under.homMk F rfl : Under.mk d ⟶ Under.mk (d ≫ F)) :=
    (weakEquivalences_under_iff _ _).2 ‹_›
  have : IsFibrant (Under.mk d) :=
    (isFibrant_under_iff _ _).2 ((isFibrant_iff_quasicategory X).2 inferInstance)
  have : IsFibrant (Under.mk (d ≫ F)) :=
    (isFibrant_under_iff _ _).2 ((isFibrant_iff_quasicategory Y).2 inferInstance)
  exact (isQuillen_joinRightUnderAdjunction K).weakEquivalence_map_of_isFibrant _

theorem modelCategoryJoyal.isFinal_slice_map_iff {K X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (F : X ⟶ Y) [WeakEquivalence F] (d : K ⟶ X)
    (w : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    IsFinal (((slice K).map (Under.homMk F rfl : Under.mk d ⟶ Under.mk (d ≫ F))).app _ w) ↔
      IsFinal w :=
  have : ((slice K).obj (Under.mk d)).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs X.Quasicategory)
  have : ((slice K).obj (Under.mk (d ≫ F))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs Y.Quasicategory)
  have := weakEquivalence_slice_map F d
  isFinal_iff_of_weakEquivalence _ w

theorem isFinal_iff_trivialFibration_sliceRes {K X : SSet.{u}} [X.Quasicategory]
    (c : join Δ[0] K ⟶ X) :
    IsFinal ((sliceObjEquiv K (Under.mk (joinInclRight Δ[0] K ≫ c)) 0).symm ⟨c, rfl⟩) ↔
      modelCategoryQuillen.I.rlp (sliceRes (joinInclRight Δ[0] K) (Under.mk c)) := by
  have : ((slice K).obj (Under.mk (joinInclRight Δ[0] K ≫ c))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs X.Quasicategory)
  have h : ∀ {Y : SSet.{u}} [Y.Quasicategory] (j : Δ[0] ⟶ Y),
      IsFinal (yonedaEquiv j) ↔ modelCategoryQuillen.I.rlp (sliceπ (Under.mk j)) := fun j ↦ by
    obtain ⟨y, rfl⟩ := yonedaEquiv.symm.surjective j
    rw [Equiv.apply_symm_apply]
    exact isFinal_iff_trivialFibration_sliceAtπ y
  rw [← yonedaEquiv_joinAdjunct, h,
    ← (modelCategoryQuillen.I.rlp).cancel_left_of_respectsIso (sliceJoinIso c).hom,
    sliceJoinIso_hom_comp_sliceRes]

end SSet
