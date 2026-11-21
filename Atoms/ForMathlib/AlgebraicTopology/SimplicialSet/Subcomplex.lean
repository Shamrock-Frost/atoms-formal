import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Limits.Types.Pushouts

universe u

open CategoryTheory Limits

namespace SSet.Subcomplex

section

variable {X : SSet.{u}} {A B : X.Subcomplex}

theorem range_homOfLE (hAB : A ≤ B) :
    Subcomplex.range (Subcomplex.homOfLE hAB) = A.preimage B.ι := by
  ext n x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

end

noncomputable def preimageιArrowIso {X Y : SSet.{u}} (f : Y ⟶ X) [Mono f] (A : X.Subcomplex) :
    Arrow.mk (A.preimage f).ι ≅
      Arrow.mk (homOfLE (inf_le_right : A ⊓ range f ≤ range f)) :=
  have : Mono ((A.preimage f).toImage f) :=
    mono_of_mono_fac ((A.preimage f).toImage_ι f)
  have : IsIso ((A.preimage f).toImage f) := isIso_of_mono_of_epi _
  Arrow.isoMk (asIso ((A.preimage f).toImage f) ≪≫
      Subcomplex.eqToIso (by aesop)) (asIso (toRange f)) rfl

end SSet.Subcomplex

namespace SSet

lemma isPushout_bot_ι_coprod {X : SSet.{u}} :
    IsPushout (⊥ : X.Subcomplex).ι (⊥ : X.Subcomplex).ι (coprod.inl : X ⟶ X ⨿ X) coprod.inr := by
  have h := IsPushout.of_is_coproduct' (coprodIsCoprod X X) (Subcomplex.isInitialBot (X := X))
  rwa [Subcomplex.isInitialBot.hom_ext (Subcomplex.isInitialBot.to _) (⊥ : X.Subcomplex).ι] at h

end SSet
