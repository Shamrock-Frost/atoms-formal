import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Colimits

namespace CategoryTheory

open Limits Opposite

universe w v u

theorem isSplitEpi_of_epi_yoneda_map {C : Type u} [Category.{v} C] {a b : C} (f : a ⟶ b)
    (h : Epi (yoneda.map f)) : IsSplitEpi f := by
  have hb : Epi ((yoneda.map f).app (op b)) := (NatTrans.epi_iff_epi_app _).1 h (op b)
  obtain ⟨s, hs⟩ := (epi_iff_surjective _).1 hb (𝟙 b)
  exact IsSplitEpi.mk' ⟨s, hs⟩

namespace FunctorToTypes

theorem mono_sigmaDesc_of_disjoint {C : Type*} [Category* C] {ι : Type*}
    [HasColimitsOfShape (Discrete ι) (Type w)] {T : ι → Cᵒᵖ ⥤ Type w} {L : Cᵒᵖ ⥤ Type w}
    (a : ∀ k, T k ⟶ L) [∀ k, Mono (a k)]
    (h : ∀ U k l (x : (T k).obj U) (y : (T l).obj U), (a k).app U x = (a l).app U y → k = l) :
    Mono (Sigma.desc a) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  have hc := isColimitOfPreserves ((evaluation _ _).obj U)
    (colimit.isColimit (Discrete.functor T))
  have hι (k : ι) (x : (T k).obj U) :
      (Sigma.desc a).app U ((Sigma.ι T k).app U x) = (a k).app U x := by
    rw [← NatTrans.comp_app_apply, Sigma.ι_desc]
  intro z₁ z₂ hz
  obtain ⟨⟨k⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc z₁
  obtain ⟨⟨l⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc z₂
  have e := (hι k x).symm.trans (hz.trans (hι l y))
  obtain rfl := h U k l x y e
  exact congrArg _ ((mono_iff_injective _).1
    (NatTrans.mono_iff_mono_app (a k) |>.1 inferInstance U) e)

end FunctorToTypes

end CategoryTheory
