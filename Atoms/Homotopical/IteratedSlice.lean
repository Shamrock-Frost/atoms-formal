import Atoms.Homotopical.PresheafSlice

open CategoryTheory

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

noncomputable def costructuredArrowSliceEquivalence (X : Aᵒᵖ ⥤ Type v)
    (Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    CostructuredArrow yoneda Z ≌ CostructuredArrow yoneda ((sliceForget X).obj Z) :=
  (CostructuredArrow.post yoneda (overEquivPresheafCostructuredArrow X).inverse
      Z).asEquivalence.trans
    ((CostructuredArrow.mapNatIso (sliceYonedaOverIso X)).trans
      (CostructuredArrow.costructuredArrowToOverEquivalence yoneda
        ((overEquivPresheafCostructuredArrow X).inverse.obj Z)))

noncomputable def costructuredArrowSliceEquivalenceMapIso (X : Aᵒᵖ ⥤ Type v)
    {Z Z' : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v} (f : Z ⟶ Z') :
    (costructuredArrowSliceEquivalence X Z).functor ⋙
        CostructuredArrow.map ((sliceForget X).map f) ≅
      CostructuredArrow.map f ⋙ (costructuredArrowSliceEquivalence X Z').functor :=
  NatIso.ofComponents
    (fun s => CostructuredArrow.isoMk (Iso.refl s.left.left) (by
      change yoneda.map (𝟙 _) ≫ (sliceForgetYonedaIso s.left).inv ≫
        (sliceForget X).map (s.hom ≫ f) =
          ((sliceForgetYonedaIso s.left).inv ≫ (sliceForget X).map s.hom) ≫
            (sliceForget X).map f
      simp))
    (fun g => by
      ext
      change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
      simp)

noncomputable def costructuredArrowSliceEquivalenceProjIso (X : Aᵒᵖ ⥤ Type v)
    (Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :
    (costructuredArrowSliceEquivalence X Z).functor ⋙
        CostructuredArrow.proj yoneda ((sliceForget X).obj Z) ≅
      CostructuredArrow.proj yoneda Z ⋙ CostructuredArrow.proj yoneda X :=
  NatIso.ofComponents (fun s => Iso.refl s.left.left)
    (fun g => by
      change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
      simp)

noncomputable def costructuredArrowYonedaSliceEquivalence {X : Aᵒᵖ ⥤ Type v}
    (e : CostructuredArrow yoneda X) :
    CostructuredArrow yoneda (yoneda.obj e) ≌ CostructuredArrow yoneda (yoneda.obj e.left) :=
  (costructuredArrowSliceEquivalence X (yoneda.obj e)).trans
    (CostructuredArrow.mapIso (sliceForgetYonedaIso e))

end Atoms.Homotopical
