import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

namespace CategoryTheory.MorphismProperty

universe v u

abbrev splitEpimorphisms (C : Type u) [Category.{v} C] : MorphismProperty C :=
  fun _ _ f ↦ IsSplitEpi f

instance RespectsIso.splitEpimorphisms (C : Type u) [Category.{v} C] :
    (splitEpimorphisms C).RespectsIso := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f (_ : IsSplitEpi f)
      exact inferInstanceAs (IsSplitEpi (_ ≫ _))

theorem map_functor_map_inverse_iff {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    (W : MorphismProperty D) [W.RespectsIso] {X Y : D} (f : X ⟶ Y) :
    W (E.functor.map (E.inverse.map f)) ↔ W f :=
  W.arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))

theorem inverseImage_inverseImage_congrLeft_op {C D E : Type*} [Category C] [Category D]
    [Category E] (e : C ≌ D) (V : MorphismProperty (Dᵒᵖ ⥤ E)) [V.RespectsIso] :
    (V.inverseImage e.op.congrLeft.functor).inverseImage
      e.symm.op.congrLeft.functor = V := by
  rw [inverseImage_equivalence_inverse_eq_map_functor V e.op.congrLeft]
  exact inverseImage_map_eq_of_isEquivalence V e.op.congrLeft.inverse

section Equivalence

variable {C D : Type*} [Category C] [Category D]

theorem monomorphisms_eq_inverseImage_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence] :
    monomorphisms C = (monomorphisms D).inverseImage F := by
  ext X Y f
  exact ⟨fun (_ : Mono f) ↦ (inferInstance : Mono (F.map f)),
    fun (h : Mono (F.map f)) ↦ F.mono_of_mono_map h⟩

theorem rlp_inverseImage_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence] (P : MorphismProperty D)
    [P.RespectsIso] : (P.inverseImage F).rlp = P.rlp.inverseImage F := by
  let E : D ≌ C := F.asEquivalence.symm
  ext X Y p
  refine ⟨fun hp K L j hj ↦ ?_, fun hp K L i hi ↦ ?_⟩
  · refine (E.toAdjunction.hasLiftingProperty_iff j p).1 (hp _ ?_)
    exact (map_functor_map_inverse_iff E.symm P j).2 hj
  · have := (E.toAdjunction.hasLiftingProperty_iff (E.inverse.map i) p).2 (hp _ hi)
    exact HasLiftingProperty.of_arrow_iso_left (i := E.functor.map (E.inverse.map i))
      (Arrow.isoMk (E.counitIso.app K) (E.counitIso.app L) (E.counit.naturality i).symm) p

theorem inverseImage_inverse_inverseImage_functor (E : C ≌ D) (P : MorphismProperty C)
    [P.RespectsIso] : (P.inverseImage E.inverse).inverseImage E.functor = P := by
  ext X Y f
  exact map_functor_map_inverse_iff E.symm P f

end Equivalence

end CategoryTheory.MorphismProperty
