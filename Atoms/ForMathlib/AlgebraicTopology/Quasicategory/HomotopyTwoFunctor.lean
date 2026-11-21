import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoCategoryIso
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed

universe u

namespace SSet

open CategoryTheory MonoidalCategory MonoidalClosed CategoryTheory.Prod

namespace hoFunctor

noncomputable def ihomEval (X Y : SSet.{u}) :
    hoFunctor.obj X ⊗ hoFunctor.obj ((ihom X).obj Y) ⟶ hoFunctor.obj Y :=
  Functor.LaxMonoidal.μ hoFunctor X _ ≫ hoFunctor.map ((ihom.ev X).app Y)

private abbrev ihomComp (X Y Z : SSet.{u}) :
    (ihom X).obj Y ⊗ (ihom Y).obj Z ⟶ (ihom X).obj Z :=
  eComp SSet X Y Z

private noncomputable def ihomEvalFunctor (X Y : SSet.{u}) :
    hoFunctor.obj X × hoFunctor.obj ((ihom X).obj Y) ⥤ hoFunctor.obj Y :=
  (ihomEval X Y).toFunctor

private noncomputable def ihomCompFunctor (X Y Z : SSet.{u}) :
    hoFunctor.obj ((ihom X).obj Y) × hoFunctor.obj ((ihom Y).obj Z) ⥤
      hoFunctor.obj ((ihom X).obj Z) :=
  (Functor.LaxMonoidal.μ hoFunctor _ _ ≫ hoFunctor.map (ihomComp X Y Z)).toFunctor

noncomputable def ihomComparison (X Y : SSet.{u}) :
    hoFunctor.obj ((ihom X).obj Y) ⥤ hoFunctor.obj X ⥤ hoFunctor.obj Y :=
  (Functor.curry.obj (ihomEvalFunctor X Y)).flip

private theorem ihomComparison_map_app (X Y : SSet.{u}) {x x'} (θ : x ⟶ x') (a) :
    ((ihomComparison X Y).map θ).app a = (ihomEvalFunctor X Y).map (𝟙 a ×ₘ θ) := rfl

theorem ihomComparison_eq_curry (X Y : SSet.{u}) :
    ihomComparison X Y = (MonoidalClosed.curry (ihomEval X Y)).toFunctor := rfl

theorem map_comp_curry_ihomEval {K X Y : SSet.{u}} (g : K ⟶ (ihom X).obj Y) :
    hoFunctor.map g ≫ MonoidalClosed.curry (ihomEval X Y) =
      MonoidalClosed.curry (Functor.LaxMonoidal.μ hoFunctor X K ≫
        hoFunctor.map (MonoidalClosed.uncurry g)) := by
  rw [← MonoidalClosed.curry_natural_left, ihomEval,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp, MonoidalClosed.uncurry_eq]

private theorem ihomEval_comp (X Y Z : SSet.{u}) :
    hoFunctor.obj X ◁ (Functor.LaxMonoidal.μ hoFunctor _ _ ≫ hoFunctor.map (ihomComp X Y Z)) ≫
      ihomEval X Z = (α_ _ _ _).inv ≫ ihomEval X Y ▷ _ ≫ ihomEval Y Z := by
  have h3 : (α_ _ _ _).hom ≫ X ◁ ihomComp X Y Z ≫ (ihom.ev X).app Z =
      (ihom.ev X).app Y ▷ _ ≫ (ihom.ev Y).app Z := by
    ext n ⟨⟨a, x⟩, y⟩
    rfl
  rw [ihomEval, ihomEval, ihomEval, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    Iso.eq_inv_comp, ← Functor.LaxMonoidal.associativity_assoc, ← Functor.map_comp, h3,
    Functor.map_comp, MonoidalCategory.comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc]

private theorem ihomEvalFunctor_obj_ihomCompFunctor (X Y Z : SSet.{u}) (a x y) :
    (ihomEvalFunctor X Z).obj (a, (ihomCompFunctor X Y Z).obj (x, y)) =
      (ihomEvalFunctor Y Z).obj ((ihomEvalFunctor X Y).obj (a, x), y) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (ihomEval_comp X Y Z)) (a, (x, y))

private theorem ihomEvalFunctor_map_ihomCompFunctor {X Y Z : SSet.{u}} {a a'} (φ₀ : a ⟶ a')
    {x x'} (φ : x ⟶ x') {y y'} (ψ : y ⟶ y') :
    (ihomEvalFunctor X Z).map (φ₀ ×ₘ (ihomCompFunctor X Y Z).map (φ ×ₘ ψ)) =
      eqToHom (ihomEvalFunctor_obj_ihomCompFunctor X Y Z a x y) ≫
        (ihomEvalFunctor Y Z).map ((ihomEvalFunctor X Y).map (φ₀ ×ₘ φ) ×ₘ ψ) ≫
        eqToHom (ihomEvalFunctor_obj_ihomCompFunctor X Y Z a' x' y').symm :=
  Functor.congr_hom (congrArg Cat.Hom.toFunctor (ihomEval_comp X Y Z)) (φ₀ ×ₘ (φ ×ₘ ψ))

end hoFunctor

private theorem map_mkHom_id_eqToHom_comp {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C × D ⥤ E) (a : C) {y₀ y y' y₁ : D} (p : y₀ = y) (M : y ⟶ y')
    (q : y' = y₁) :
    F.map (𝟙 a ×ₘ (eqToHom p ≫ M ≫ eqToHom q)) =
      eqToHom (by rw [p]) ≫ F.map (𝟙 a ×ₘ M) ≫ eqToHom (by rw [q]) := by
  subst p q
  simp

private theorem map_mkHom_id_id {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) (c : C) (d : D) : F.map (𝟙 c ×ₘ 𝟙 d) = 𝟙 _ :=
  F.map_id (c, d)

private theorem map_mkHom_id_of_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {c c' : C} (h : c = c') {y y' : D} (θ : y ⟶ y') :
    F.map (𝟙 c ×ₘ θ) = eqToHom (by rw [h]) ≫ F.map (𝟙 c' ×ₘ θ) ≫ eqToHom (by rw [h]) := by
  subst h
  simp

namespace QCat

private abbrev Hom₁ (A B : QCat.{u}) : Type u :=
  @Quiver.Hom QCat.{u} Bicategory.toCategoryStruct.toQuiver A B

private def ssetHom {A B : QCat.{u}} (f : Hom₁ A B) : A.obj ⟶ B.obj := f.hom

private def vertex {A B : QCat.{u}} (f : Hom₁ A B) : 𝟙_ SSet ⟶ (ihom A.obj).obj B.obj :=
  Functor.natTransEquiv.symm f.hom

private def toHo (A B : QCat.{u}) : Hom₁ A B ⥤ hoFunctor.obj ((ihom A.obj).obj B.obj) where
  obj f := CatEnrichedOrdinary.homEquiv f
  map α := CatEnrichedOrdinary.Hom.base α
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem ihomComparison_obj_toHo_obj {A B : QCat.{u}} (f : Hom₁ A B) :
    (hoFunctor.ihomComparison A.obj B.obj).obj ((toHo A B).obj f) =
      (hoFunctor.map (ssetHom f)).toFunctor := by
  have h0 : A.obj ◁ vertex f ≫ (ihom.ev A.obj).app B.obj = (ρ_ A.obj).hom ≫ ssetHom f := by
    ext n ⟨a, x⟩
    rfl
  have key : ∀ t, (Functor.LaxMonoidal.ε hoFunctor ≫ hoFunctor.map (vertex f) ≫
      MonoidalClosed.curry (hoFunctor.ihomEval A.obj B.obj)).toFunctor.obj t =
      (hoFunctor.map (ssetHom f)).toFunctor := by
    intro t
    rw [hoFunctor.map_comp_curry_ihomEval, MonoidalClosed.uncurry_eq, h0,
      ← MonoidalClosed.curry_natural_left, Functor.map_comp,
      ← reassoc_of% (Functor.LaxMonoidal.right_unitality hoFunctor A.obj)]
    rfl
  exact key ⟨ULiftHom.objUp ⟨()⟩⟩

private noncomputable def homotopyFunctorHom' (A B : QCat.{u}) :
    Hom₁ A B ⥤ (hoFunctor.obj A.obj ⥤ hoFunctor.obj B.obj) :=
  Functor.copyObj (toHo A B ⋙ hoFunctor.ihomComparison A.obj B.obj)
    (fun f ↦ (hoFunctor.map (ssetHom f)).toFunctor)
    (fun f ↦ eqToIso (ihomComparison_obj_toHo_obj f))

noncomputable def homCategoryEquiv (A B : QCat.{u}) :
    (A ⟶ B) ≌ hoFunctor.obj ((ihom A.obj).obj B.obj) :=
  have : (toHo A B).Full := ⟨fun φ ↦ ⟨CatEnrichedOrdinary.Hom.mk φ, rfl⟩⟩
  have : (toHo A B).Faithful := ⟨fun h ↦ CatEnrichedOrdinary.Hom.ext _ _ h⟩
  have : (toHo A B).EssSurj := ⟨fun x ↦ ⟨CatEnrichedOrdinary.homEquiv.symm x, ⟨eqToIso
    ((CatEnrichedOrdinary.homEquiv (C := QCat.{u}) (a := A) (b := B)).apply_symm_apply x)⟩⟩⟩
  have : (toHo A B).IsEquivalence := { }
  (toHo A B).asEquivalence

noncomputable def homotopyFunctorHom (A B : QCat.{u}) :
    (A ⟶ B) ⥤ (hoFunctor.obj A.obj ⥤ hoFunctor.obj B.obj) :=
  homotopyFunctorHom' A B

theorem homotopyFunctorHom_obj {A B : QCat.{u}} (f : A ⟶ B) :
    (homotopyFunctorHom A B).obj f = (hoFunctor.map f.hom).toFunctor := rfl

noncomputable def homotopyFunctorHomIso (A B : QCat.{u}) :
    homotopyFunctorHom A B ≅
      (homCategoryEquiv A B).functor ⋙ hoFunctor.ihomComparison A.obj B.obj :=
  (Functor.isoCopyObj _ _ _).symm

private theorem ihomEvalFunctor_obj_toHo_obj {A B : QCat.{u}} (f : Hom₁ A B)
    (a : hoFunctor.obj A.obj) :
    (hoFunctor.ihomEvalFunctor A.obj B.obj).obj (a, (toHo A B).obj f) =
      ((homotopyFunctorHom' A B).obj f).obj a :=
  Functor.congr_obj (ihomComparison_obj_toHo_obj f) a

private theorem homotopyFunctorHom'_map_app {A B : QCat.{u}} {f g : Hom₁ A B} (η : f ⟶ g)
    (a : hoFunctor.obj A.obj) :
    ((homotopyFunctorHom' A B).map η).app a =
      eqToHom (ihomEvalFunctor_obj_toHo_obj f a).symm ≫
      (hoFunctor.ihomEvalFunctor A.obj B.obj).map (𝟙 a ×ₘ (toHo A B).map η) ≫
      eqToHom (ihomEvalFunctor_obj_toHo_obj g a) := by
  simp only [homotopyFunctorHom', Functor.copyObj, NatTrans.comp_app, eqToIso.hom,
    eqToIso.inv, eqToHom_app, Functor.comp_map, hoFunctor.ihomComparison_map_app]
  rfl

private theorem ihomEvalFunctor_map_mkHom_id {B C : QCat.{u}} (g : Hom₁ B C)
    {b b' : hoFunctor.obj B.obj} (m : b ⟶ b') :
    (hoFunctor.ihomEvalFunctor B.obj C.obj).map (m ×ₘ 𝟙 ((toHo B C).obj g)) =
      eqToHom (ihomEvalFunctor_obj_toHo_obj g b) ≫ ((homotopyFunctorHom' B C).obj g).map m ≫
        eqToHom (ihomEvalFunctor_obj_toHo_obj g b').symm :=
  Functor.congr_hom (ihomComparison_obj_toHo_obj g) m

private theorem toHo_obj_comp {A B C : QCat.{u}} (f : Hom₁ A B) (g : Hom₁ B C) :
    (toHo A C).obj (f ≫ g) =
      (hoFunctor.ihomCompFunctor A.obj B.obj C.obj).obj ((toHo A B).obj f, (toHo B C).obj g) :=
  CatEnrichedOrdinary.homEquiv_comp f g

private theorem toHo_map_whiskerLeft {A B C : QCat.{u}} (f : Hom₁ A B) {g g' : Hom₁ B C}
    (η : g ⟶ g') :
    (toHo A C).map (Bicategory.whiskerLeft f η) =
      eqToHom (toHo_obj_comp f g) ≫
        (hoFunctor.ihomCompFunctor A.obj B.obj C.obj).map
          (𝟙 ((toHo A B).obj f) ×ₘ (toHo B C).map η) ≫
        eqToHom (toHo_obj_comp f g').symm := rfl

private theorem toHo_map_whiskerRight {A B C : QCat.{u}} {f f' : Hom₁ A B} (η : f ⟶ f')
    (g : Hom₁ B C) :
    (toHo A C).map (Bicategory.whiskerRight η g) =
      eqToHom (toHo_obj_comp f g) ≫
        (hoFunctor.ihomCompFunctor A.obj B.obj C.obj).map
          ((toHo A B).map η ×ₘ 𝟙 ((toHo B C).obj g)) ≫
        eqToHom (toHo_obj_comp f' g).symm := rfl

private theorem homotopyFunctorHom'_obj_comp {A B C : QCat.{u}} (f : Hom₁ A B)
    (g : Hom₁ B C) :
    (homotopyFunctorHom' A C).obj (f ≫ g) =
      (homotopyFunctorHom' A B).obj f ⋙ (homotopyFunctorHom' B C).obj g :=
  congrArg Cat.Hom.toFunctor (hoFunctor.map_comp (ssetHom f) (ssetHom g))

private theorem homotopyFunctorHom'_map_whiskerLeft {A B C : QCat.{u}} (f : Hom₁ A B)
    {g g' : Hom₁ B C} (η : g ⟶ g') :
    (homotopyFunctorHom' A C).map (Bicategory.whiskerLeft f η) =
      eqToHom (homotopyFunctorHom'_obj_comp f g) ≫
        Functor.whiskerLeft ((homotopyFunctorHom' A B).obj f)
          ((homotopyFunctorHom' B C).map η) ≫
        eqToHom (homotopyFunctorHom'_obj_comp f g').symm := by
  ext a
  rw [homotopyFunctorHom'_map_app, toHo_map_whiskerLeft, map_mkHom_id_eqToHom_comp,
    hoFunctor.ihomEvalFunctor_map_ihomCompFunctor, map_mkHom_id_id,
    map_mkHom_id_of_eq _ (ihomEvalFunctor_obj_toHo_obj f a)]
  simp [eqToHom_app, homotopyFunctorHom'_map_app]

private theorem homotopyFunctorHom'_map_whiskerRight {A B C : QCat.{u}} {f f' : Hom₁ A B}
    (η : f ⟶ f') (g : Hom₁ B C) :
    (homotopyFunctorHom' A C).map (Bicategory.whiskerRight η g) =
      eqToHom (homotopyFunctorHom'_obj_comp f g) ≫
        Functor.whiskerRight ((homotopyFunctorHom' A B).map η)
          ((homotopyFunctorHom' B C).obj g) ≫
        eqToHom (homotopyFunctorHom'_obj_comp f' g).symm := by
  ext a
  rw [homotopyFunctorHom'_map_app, toHo_map_whiskerRight, map_mkHom_id_eqToHom_comp,
    hoFunctor.ihomEvalFunctor_map_ihomCompFunctor, ihomEvalFunctor_map_mkHom_id]
  simp [eqToHom_app, homotopyFunctorHom'_map_app, eqToHom_map]

noncomputable def homotopyFunctor : StrictPseudofunctor QCat.{u} Cat.{u, u} :=
  StrictPseudofunctor.mk'' {
    obj A := Cat.of (hoFunctor.obj A.obj)
    map {A B} f := ((homotopyFunctorHom' A B).obj f).toCatHom
    map₂ {A B _ _} η := ((homotopyFunctorHom' A B).map η).toCatHom₂
    map₂_id {A B} f := congrArg NatTrans.toCatHom₂ ((homotopyFunctorHom' A B).map_id f)
    map₂_comp {A B _ _ _} η θ :=
      congrArg NatTrans.toCatHom₂ ((homotopyFunctorHom' A B).map_comp η θ)
    map_id A := hoFunctor.map_id A.obj
    map_comp f g := congrArg Functor.toCatHom (homotopyFunctorHom'_obj_comp f g)
    map₂_whisker_left {_ _ _} f {_ _} η := by
      ext : 1
      rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
        Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans]
      exact homotopyFunctorHom'_map_whiskerLeft f η
    map₂_whisker_right η g := by
      ext : 1
      rw [Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
        Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans]
      exact homotopyFunctorHom'_map_whiskerRight η g }

theorem homotopyFunctor_obj (A : QCat.{u}) : homotopyFunctor.obj A = hoFunctor.obj A.obj := rfl

theorem homotopyFunctor_map {A B : QCat.{u}} (f : A ⟶ B) :
    homotopyFunctor.map f = hoFunctor.map f.hom := rfl

theorem homotopyFunctor_map₂ {A B : QCat.{u}} {f g : A ⟶ B} (η : f ⟶ g) :
    homotopyFunctor.map₂ η = ((homotopyFunctorHom A B).map η).toCatHom₂ := rfl

noncomputable def homotopyAdjunction {A B : QCat.{u}} {f : A ⟶ B} {g : B ⟶ A}
    (adj : Bicategory.Adjunction f g) :
    (hoFunctor.map f.hom).toFunctor ⊣ (hoFunctor.map g.hom).toFunctor :=
  Adjunction.ofCat (homotopyFunctor.mapAdjunction adj)

noncomputable def homotopyEquivalence {A B : QCat.{u}} (e : Bicategory.Equivalence A B) :
    hoFunctor.obj A.obj ≌ hoFunctor.obj B.obj :=
  CategoryTheory.Equivalence.mk (hoFunctor.map e.hom.hom).toFunctor
    (hoFunctor.map e.inv.hom).toFunctor
    (eqToIso (congrArg Cat.Hom.toFunctor (homotopyFunctor.map_id A)).symm ≪≫
      Cat.Hom.toNatIso (homotopyFunctor.map₂Iso e.unit) ≪≫
      eqToIso (congrArg Cat.Hom.toFunctor (homotopyFunctor.map_comp e.hom e.inv)))
    (eqToIso (congrArg Cat.Hom.toFunctor (homotopyFunctor.map_comp e.inv e.hom)).symm ≪≫
      Cat.Hom.toNatIso (homotopyFunctor.map₂Iso e.counit) ≪≫
      eqToIso (congrArg Cat.Hom.toFunctor (homotopyFunctor.map_id B)))

theorem homotopyEquivalence_functor {A B : QCat.{u}} (e : Bicategory.Equivalence A B) :
    (homotopyEquivalence e).functor = (hoFunctor.map e.hom.hom).toFunctor := rfl

end QCat

end SSet
