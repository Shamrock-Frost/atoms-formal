import Atoms.TestCategory.FiniteSetsTest
import Atoms.TestCategory.Simplicial.Contraction
import Atoms.TestCategory.TotallyAspherical

open CategoryTheory Limits MorphismProperty MonoidalCategory Simplicial

namespace Atoms.TestCategory

open Homotopical (SeparatingInterval)

universe u

open CartesianMonoidalCategory in
private def simplicialContractionTensor {X Y : SSet.{u}} (c : SimplicialContraction X)
    (d : SimplicialContraction Y) : SimplicialContraction (X ⊗ Y) where
  pt := lift c.pt d.pt
  homotopy := lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ c.homotopy)
    (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ d.homotopy)
  homotopy_zero := by
    have k₁ : lift (toUnit (X ⊗ Y) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (fst X Y) =
        fst X Y ≫ lift (toUnit X ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 X) := by ext1 <;> simp
    have k₂ : lift (toUnit (X ⊗ Y) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (snd X Y) =
        snd X Y ≫ lift (toUnit Y ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 Y) := by ext1 <;> simp
    ext1
    · simp only [Category.assoc, lift_fst, comp_lift_assoc, lift_snd_assoc, Category.id_comp]
      rw [k₁, Category.assoc, c.homotopy_zero, Category.comp_id]
    · simp only [Category.assoc, lift_snd, comp_lift_assoc, lift_fst, lift_snd_assoc,
        Category.id_comp]
      rw [k₂, Category.assoc, d.homotopy_zero, Category.comp_id]
  homotopy_one := by
    have k₁ : lift (toUnit (X ⊗ Y) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (fst X Y) =
        fst X Y ≫ lift (toUnit X ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 X) := by ext1 <;> simp
    have k₂ : lift (toUnit (X ⊗ Y) ≫
          SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (snd X Y) =
        snd X Y ≫ lift (toUnit Y ≫
            SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 Y) := by ext1 <;> simp
    ext1
    · simp only [Category.assoc, lift_fst, comp_lift_assoc, lift_snd_assoc, Category.id_comp]
      rw [k₁, Category.assoc, c.homotopy_one]
      simp
    · simp only [Category.assoc, lift_snd, comp_lift_assoc, lift_fst, lift_snd_assoc,
        Category.id_comp]
      rw [k₂, Category.assoc, d.homotopy_one]
      simp

namespace BasicLocalizer

section

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

class IsStrictTest : Prop extends 𝒲.IsTest A, 𝒲.IsTotallyAspherical A

theorem isStrictTest_tfae [𝒲.IsTotallyAspherical A] :
    List.TFAE
      [𝒲.IsWeakTest A, 𝒲.IsLocalTest A, 𝒲.IsTest A, 𝒲.IsStrictTest A,
        ∃ J : SeparatingInterval A, 𝒲.PshAspherical A J.interval,
        𝒲.PshAspherical A ((nerveFunctor A).obj interval)] := by
  have hloc := (𝒲.isTotallyAspherical_iff_forall_locallyAspherical_iff A).1 inferInstance
  tfae_have 1 → 2 := fun h => 𝒲.isLocalTest_of_locallyAspherical_nerveFunctor_obj A
    fun C _ => (hloc _).2 ((𝒲.aspherical_iff_of_W _ (h.counit_mem C)).2
      (𝒲.terminal_aspherical C))
  tfae_have 2 → 3 := fun h =>
    (𝒲.isTest_iff_aspherical_and_isLocalTest A).2 ⟨IsTotallyAspherical.aspherical, h⟩
  tfae_have 3 → 1 := fun h => h.toIsWeakTest
  tfae_have 3 → 4 := fun h => { toIsTest := h, toIsTotallyAspherical := inferInstance }
  tfae_have 4 → 3 := fun h => h.toIsTest
  tfae_have 2 → 6 := fun _ =>
    (hloc _).1 (𝒲.locallyAspherical_nerveFunctor_obj_of_isLocalTest A interval)
  tfae_have 6 → 5 := fun h => ⟨⟨_, nervePoint, isPullback_nervePoint⟩, h⟩
  tfae_have 5 → 2 := fun ⟨J, hJ⟩ => 𝒲.isLocalTest_of_separatingInterval A J ((hloc _).2 hJ)
  tfae_finish

theorem isStrictTest_of_isRepresentable [𝒲.IsTotallyAspherical A] (J : SeparatingInterval.{u, u} A)
    [J.interval.IsRepresentable] : 𝒲.IsStrictTest A :=
  ((𝒲.isStrictTest_tfae A).out 4 3).1 (⟨J, (𝒲.pshAspherical_iff_of_iso A J.interval.reprW).1
    (𝒲.pshAspherical_yoneda A _)⟩ : ∃ J : SeparatingInterval.{u, u} A, 𝒲.PshAspherical A J.interval)

end

instance isStrictTest_asSmallSimplexCategory (𝒲 : BasicLocalizer.{u}) :
    𝒲.IsStrictTest (AsSmall.{u} SimplexCategory) where
  aspherical := 𝒲.aspherical_asSmallSimplexCategory
  pshAspherical_prod a b := by
    have e : yoneda.obj a ⨯ yoneda.obj b ≅
        SSet.asSmall.obj (Δ[(ULift.down a).len] ⊗ Δ[(ULift.down b).len]) :=
      prod.mapIso (SSet.asSmallStdSimplexIso a).symm (SSet.asSmallStdSimplexIso b).symm ≪≫
        (PreservesLimitPair.iso SSet.asSmall.{u} _ _).symm ≪≫
        SSet.asSmall.mapIso ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[(ULift.down a).len] : SSet.{u})).app Δ[(ULift.down b).len]).symm
    exact (𝒲.pshAspherical_iff_of_iso _ e).2 (𝒲.pshAspherical_sSetAsSmall_of_contraction
      (simplicialContractionTensor (stdSimplexContraction _) (stdSimplexContraction _)))

instance isStrictTest_simplexCategory (𝒲 : BasicLocalizer.{0}) :
    𝒲.IsStrictTest SimplexCategory where
  toIsTotallyAspherical := 𝒲.isTotallyAspherical_of_asphericalFunctor AsSmall.equiv.inverse
    (𝒲.asphericalFunctor_of_adjunction (v := AsSmall.equiv.functor.toCatHom)
      AsSmall.equiv.symm.toAdjunction)

instance isStrictTest_nonemptyFinSet (𝒲 : BasicLocalizer.{u}) :
    𝒲.IsStrictTest NonemptyFinSet.{u} where

end BasicLocalizer

end Atoms.TestCategory
