import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.PiZero
import Atoms.Homotopical.Simplicial.KanDatum

open CategoryTheory Limits Simplicial Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical CartesianMonoidalCategory MonoidalCategory

universe u

namespace SSet

private theorem bijective_mapπ₀_contraction (X : SSet.{u}) :
    Function.Bijective (mapπ₀ (simplicialCylinder.contraction.app X)) := by
  let s := (simplicialCylinder.endpoint false).app X
  let p := simplicialCylinder.contraction.app X
  have hp : ∀ a, mapπ₀ p (mapπ₀ s a) = a := fun a => by
    rw [← mapπ₀_comp_apply, simplicialCylinder.endpoint_app_contraction_app]
    exact mapπ₀_id_apply (X := X) a
  have hv (v : (simplicialCylinder.I.obj X) _⦋0⦌) :
      π₀.mk (s.app _ (p.app _ v)) = π₀.mk v := by
    let a := stdSimplex.asOrderHom v.1 0
    have he : Edge
        (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0), v.2)
        (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1), v.2) :=
      Edge.mk (X := simplicialCylinder.I.obj X)
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌), (Edge.id v.2).edge)
        (Prod.ext (by apply stdSimplex.ext; intro i; fin_cases i; rfl) (Edge.id v.2).src_eq)
        (Prod.ext (by apply stdSimplex.ext; intro i; fin_cases i; rfl) (Edge.id v.2).tgt_eq)
    have ev : v.1 = stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ a) := by
      apply stdSimplex.objEquiv.injective
      ext i
      fin_cases i
      rfl
    have es : s.app _ (p.app _ v) =
        (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0), v.2) := by
      apply Prod.ext
      · have e : s ≫ fst _ _ = terminal.from X ≫ simplicialPoint false :=
          lift_fst _ _
        have h := ConcreteCategory.congr_hom (NatTrans.congr_app e _) (p.app _ v)
        change (s.app _ (p.app _ v)).1 = _ at h
        apply stdSimplex.ext
        intro i
        rw [h]
        exact simplicialPoint_app_apply false (op ⦋0⦌) _ i
      · exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (lift_snd (terminal.from X ≫ simplicialPoint false) (𝟙 X)) _)
          (p.app _ v)
    have ev' :
        (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ a), v.2) = v :=
      Prod.ext ev.symm rfl
    have ha : a.val = 0 ∨ a.val = 1 := by
      have := a.is_lt
      omega
    apply (congrArg π₀.mk es).trans
    rcases ha with ha | ha
    · have ea : a = (0 : Fin 2) := Fin.ext ha
      exact congrArg π₀.mk ((congrArg
        (fun t : Fin 2 => (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ t), v.2))
          ea.symm).trans ev')
    · have ea : a = (1 : Fin 2) := Fin.ext ha
      exact (π₀.sound he).trans (congrArg π₀.mk ((congrArg
        (fun t : Fin 2 => (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ t), v.2))
          ea.symm).trans ev'))
  have hs : ∀ a, mapπ₀ s (mapπ₀ p a) = a := by
    intro a
    obtain ⟨v, rfl⟩ := π₀.mk_surjective a
    rw [mapπ₀_mk, mapπ₀_mk]
    exact hv v
  exact ⟨fun a b h => (hs a).symm.trans ((congrArg (mapπ₀ s) h).trans (hs b)),
    fun a => ⟨mapπ₀ s a, hp a⟩⟩

private theorem isALocalizer_components :
    IsALocalizer ((isomorphisms (Type u)).inverseImage π₀Functor.{u}) := by
  let W := (isomorphisms (Type u)).inverseImage π₀Functor.{u}
  have : IsSaturated.{u} (isomorphisms (Type u)) :=
    { isStableUnderCobaseChange := inferInstance
      isStableUnderTransfiniteComposition := inferInstance
      isStableUnderRetracts := inferInstance }
  have : IsSaturated.{u} W := inferInstance
  exact {
    hasTwoOutOfThreeProperty := inferInstance
    rlp_monomorphisms_le := fun _ _ f hf =>
      (isIso_iff_bijective _).2 (bijective_mapπ₀_of_rlp_monomorphisms hf)
    isStableUnderCobaseChange := inferInstance
    isStableUnderTransfiniteComposition := inferInstance }

theorem bijective_mapπ₀_of_kanWeak {A B : SSet.{u}} {f : A ⟶ B} (hf : kanWeak f) :
    Function.Bijective (mapπ₀ f) := by
  have := isALocalizer_components.{u}
  have h : kanWeak.{u} ≤ (isomorphisms (Type u)).inverseImage π₀Functor := by
    rw [kanWeak_eq_generatedALocalizer_cellularContractions]
    refine generatedALocalizer_le ?_
    rintro _ _ g (hg | hg) <;> cases hg with
    | mk i => exact (isIso_iff_bijective _).2 (bijective_mapπ₀_contraction _)
  exact (isIso_iff_bijective _).1 (h f hf)

end SSet
