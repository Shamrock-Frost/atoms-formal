import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore

universe u

namespace SSet

lemma Subcomplex.PairingCore.pairing_isUniquelyCodimOneFace_index {X : SSet.{u}}
    {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper] (s : h.ι) :
    (h.pairing.isUniquelyCodimOneFace (h.equivII s)).index rfl = h.index s := by
  have key : ∀ (y : A.N) (_ : y = h.type₁ s)
      (hxy : S.IsUniquelyCodimOneFace (h.type₂ s).toS y.toS), hxy.index rfl = h.index s := by
    rintro _ rfl hxy
    exact h.isUniquelyCodimOneFace_index s
  exact key _ (h.type₁_pairing s).symm _

end SSet
