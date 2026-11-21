import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Presheaf.Basic

namespace CategoryTheory.CostructuredArrow

universe u w

variable {C : Type u} [Category.{w} C] {Y : Cᵒᵖ ⥤ Type w}

theorem exists_section_of_comp_left_eq_id {x y : CostructuredArrow yoneda Y} (f : x ⟶ y)
    (s : y.left ⟶ x.left) (hs : s ≫ f.left = 𝟙 y.left) :
    ∃ s' : y ⟶ x, s'.left = s ∧ s' ≫ f = 𝟙 y :=
  ⟨CostructuredArrow.homMk s (by
      rw [← CostructuredArrow.w f, ← Functor.map_comp_assoc, hs,
        CategoryTheory.Functor.map_id, Category.id_comp]),
    rfl, CostructuredArrow.hom_ext _ _ (by simp [hs])⟩

theorem mono_left_iff {x y : CostructuredArrow yoneda Y} (f : x ⟶ y) : Mono f.left ↔ Mono f := by
  constructor
  · intro h
    exact CostructuredArrow.mono_of_mono_left f
  · intro h
    refine ⟨fun {z} g g' e ↦ ?_⟩
    let z' : CostructuredArrow yoneda Y := CostructuredArrow.mk (yoneda.map g ≫ x.hom)
    let a : z' ⟶ x := CostructuredArrow.homMk g rfl
    let b : z' ⟶ x := CostructuredArrow.homMk g' (by
      simp only [z', CostructuredArrow.mk_hom_eq_self]
      rw [← CostructuredArrow.w f, ← Functor.map_comp_assoc,
        ← Functor.map_comp_assoc, e])
    have hab : a ≫ f = b ≫ f := CostructuredArrow.hom_ext _ _ (by simpa [a, b] using e)
    exact congrArg CommaMorphism.left ((cancel_mono f).1 hab)

theorem isSplitEpi_left_iff {x y : CostructuredArrow yoneda Y} (f : x ⟶ y) :
    IsSplitEpi f.left ↔ IsSplitEpi f := by
  constructor
  · intro h
    obtain ⟨s, -, hs⟩ := exists_section_of_comp_left_eq_id f (section_ f.left) (IsSplitEpi.id _)
    exact IsSplitEpi.mk' ⟨s, hs⟩
  · intro h
    exact inferInstanceAs (IsSplitEpi ((CostructuredArrow.proj yoneda Y).map f))

def overMkIsoYoneda {X : Cᵒᵖ ⥤ Type w} (t : CostructuredArrow yoneda X) :
    (overEquivPresheafCostructuredArrow X).functor.obj (Over.mk t.hom) ≅ yoneda.obj t :=
  (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow X).app t

theorem overMkIsoYoneda_naturality {X : Cᵒᵖ ⥤ Type w} {s t : CostructuredArrow yoneda X}
    (g : s ⟶ t) :
    (overEquivPresheafCostructuredArrow X).functor.map
        (Over.homMk (U := Over.mk s.hom) (V := Over.mk t.hom) (yoneda.map g.left)
          (CostructuredArrow.w g)) ≫ (overMkIsoYoneda t).hom =
      (overMkIsoYoneda s).hom ≫ yoneda.map g :=
  (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow X).hom.naturality g

section Slice

variable {A : Type u} [SmallCategory A] (X : Aᵒᵖ ⥤ Type u)

def sliceProj (e : CostructuredArrow yoneda X) : Over e ⥤ Over e.left :=
  Over.post (X := e) (CostructuredArrow.proj yoneda X)

def sliceLift (e : CostructuredArrow yoneda X) : Over e.left ⥤ Over e where
  obj t := Over.mk (CostructuredArrow.homMk
    (f := CostructuredArrow.mk (yoneda.map t.hom ≫ e.hom)) t.hom (by simp))
  map {t u} g := Over.homMk (CostructuredArrow.homMk g.left (by
    dsimp
    rw [← Category.assoc, ← Functor.map_comp, Over.w g])) (by
      apply CostructuredArrow.hom_ext
      exact Over.w g)

def sliceIso (e : CostructuredArrow yoneda X) : Cat.of (Over e) ≅ Cat.of (Over e.left) := by
  have h1 : sliceProj X e ⋙ sliceLift X e = 𝟭 (Over e) := by
    have hobj : ∀ t : Over e, (sliceProj X e ⋙ sliceLift X e).obj t = t := by
      intro t
      have hleft : ((sliceLift X e).obj ((sliceProj X e).obj t)).left = t.left := by
        refine CostructuredArrow.obj_ext _ _ rfl ?_
        change yoneda.map (eqToHom rfl) ≫ t.left.hom =
          yoneda.map t.hom.left ≫ e.hom
        simp
      refine CostructuredArrow.obj_ext _ _ hleft ?_
      change eqToHom hleft ≫ t.hom =
        CostructuredArrow.hom ((sliceLift X e).obj ((sliceProj X e).obj t))
      apply CostructuredArrow.hom_ext
      rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
      exact Category.id_comp _
    refine CategoryTheory.Functor.ext hobj ?_
    intro t u g
    apply CostructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change ((sliceLift X e).map ((sliceProj X e).map g)).left.left =
      (eqToHom _ ≫ g ≫ eqToHom _).left.left
    simp only [Over.comp_left, Over.eqToHom_left, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  have h2 : sliceLift X e ⋙ sliceProj X e = 𝟭 (Over e.left) := rfl
  exact { hom := (sliceProj X e).toCatHom
          inv := (sliceLift X e).toCatHom
          hom_inv_id := congrArg Functor.toCatHom h1
          inv_hom_id := congrArg Functor.toCatHom h2 }

end Slice

end CategoryTheory.CostructuredArrow
