import Atoms.Diagrammatic.Localization.Inversion

open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

@[implicit_reducible]
def topInversionData (U : Atom) (hU : 0 < U.dimension) : InversionData (ball.{u} U) where
  ι := PUnit
  shape _ := U
  cell _ := ⟨𝟙 U⟩
  dim_pos _ := hU

noncomputable def walkingEquivalence (U : Atom) (hU : 0 < U.dimension) : DiagSet.{u} :=
  (topInversionData U hU).localization

noncomputable def toWalkingEquivalence (U : Atom) (hU : 0 < U.dimension) :
    ball.{u} U ⟶ walkingEquivalence U hU :=
  (topInversionData U hU).toLocalization

noncomputable def invertorPair (U : Atom) (hU : 0 < U.dimension) : DiagSet.{u} :=
  (topInversionData U hU).step

noncomputable def toInvertorPair (U : Atom) (hU : 0 < U.dimension) :
    ball.{u} U ⟶ invertorPair U hU :=
  (topInversionData U hU).stepIncl

theorem exists_toWalkingEquivalence_comp_eq_iff (U : Atom) (hU : 0 < U.dimension)
    {Y : DiagSet.{u}} (hY : HasWeakComposites Y) (x : diagram Y U) :
    (∃ g : walkingEquivalence U hU ⟶ Y, toWalkingEquivalence U hU ≫ g = uliftYonedaEquiv.symm x) ↔
      IsEquivalence Y x := by
  have hx : (uliftYonedaEquiv.symm x).app (op U) ⟨𝟙 U⟩ = x :=
    (uliftYonedaEquiv_apply _).symm.trans (uliftYonedaEquiv.apply_symm_apply x)
  constructor
  · rintro ⟨g, hg⟩
    have h : IsEquivalence Y ((toWalkingEquivalence U hU ≫ g).app (op U) ⟨𝟙 U⟩) :=
      (topInversionData U hU).isEquivalence_of_toLocalization_comp_eq g ⟨⟩
    rw [hg] at h
    exact (congrArg (IsEquivalence Y) hx).mp h
  · intro h
    exact (topInversionData U hU).exists_toLocalization_comp_eq hY (uliftYonedaEquiv.symm x)
      fun _ => (congrArg (IsEquivalence Y) hx).mpr h

end Atoms.Diagrammatic
