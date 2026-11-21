import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.HomotopyTwoFunctor
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

universe u

namespace SSet

open CategoryTheory

section

open Bicategory

variable {B C : Type*} [Bicategory B] [Bicategory C] (P : Pseudofunctor B C)
  {a b : B} {f : a ⟶ b} {g : b ⟶ a}

private theorem map_leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    leftZigzag ((P.mapId a).inv ≫ P.map₂ η ≫ (P.mapComp f g).hom)
      ((P.mapComp g f).inv ≫ P.map₂ ε ≫ (P.mapId b).hom) =
    (whiskerRightIso (P.mapId a).symm (P.map f) ≪≫ (P.mapComp (𝟙 a) f).symm).hom ≫
      P.map₂ (leftZigzag η ε) ≫
        (P.mapComp f (𝟙 b) ≪≫ whiskerLeftIso (P.map f) (P.mapId b)).hom := by
  simp [leftZigzag, bicategoricalComp]

private theorem map_rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    rightZigzag ((P.mapId a).inv ≫ P.map₂ η ≫ (P.mapComp f g).hom)
      ((P.mapComp g f).inv ≫ P.map₂ ε ≫ (P.mapId b).hom) =
    (whiskerLeftIso (P.map g) (P.mapId a).symm ≪≫ (P.mapComp g (𝟙 a)).symm).hom ≫
      P.map₂ (rightZigzag η ε) ≫
        (P.mapComp (𝟙 b) g ≪≫ whiskerRightIso (P.mapId b) (P.map g)).hom := by
  simp [rightZigzag, bicategoricalComp, P.map₂_iso_inv]

private theorem map_leftUnitor_comp_rightUnitor_inv :
    (whiskerRightIso (P.mapId a).symm (P.map f) ≪≫ (P.mapComp (𝟙 a) f).symm).hom ≫
      P.map₂ ((λ_ f).hom ≫ (ρ_ f).inv) ≫
        (P.mapComp f (𝟙 b) ≪≫ whiskerLeftIso (P.map f) (P.mapId b)).hom =
      (λ_ (P.map f)).hom ≫ (ρ_ (P.map f)).inv := by
  rw [← cancel_mono (ρ_ (P.map f)).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom, P.map₂_comp,
    Category.assoc, ← P.map₂_right_unitor, ← P.map₂_comp, Iso.inv_hom_id, P.map₂_id,
    Category.comp_id, P.map₂_left_unitor]
  simp

private theorem map_rightUnitor_comp_leftUnitor_inv :
    (whiskerLeftIso (P.map g) (P.mapId a).symm ≪≫ (P.mapComp g (𝟙 a)).symm).hom ≫
      P.map₂ ((ρ_ g).hom ≫ (λ_ g).inv) ≫
        (P.mapComp (𝟙 b) g ≪≫ whiskerRightIso (P.mapId b) (P.map g)).hom =
      (ρ_ (P.map g)).hom ≫ (λ_ (P.map g)).inv := by
  rw [← cancel_mono (λ_ (P.map g)).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom, P.map₂_comp,
    Category.assoc, ← P.map₂_left_unitor, ← P.map₂_comp, Iso.inv_hom_id, P.map₂_id,
    Category.comp_id, P.map₂_right_unitor]
  simp

private noncomputable def adjunctionOfMap (adj : Bicategory.Adjunction (P.map f) (P.map g))
    (haa : Function.Bijective (P.map₂ (f := 𝟙 a) (g := f ≫ g)))
    (hbb : Function.Bijective (P.map₂ (f := g ≫ f) (g := 𝟙 b)))
    (hab : Function.Injective (P.map₂ (f := 𝟙 a ≫ f) (g := f ≫ 𝟙 b)))
    (hba : Function.Injective (P.map₂ (f := g ≫ 𝟙 a) (g := 𝟙 b ≫ g))) :
    Bicategory.Adjunction f g :=
  let η := (Equiv.ofBijective _ haa).symm ((P.mapId a).hom ≫ adj.unit ≫ (P.mapComp f g).inv)
  let ε := (Equiv.ofBijective _ hbb).symm ((P.mapComp g f).hom ≫ adj.counit ≫ (P.mapId b).inv)
  have hη : P.map₂ η = (P.mapId a).hom ≫ adj.unit ≫ (P.mapComp f g).inv :=
    Equiv.ofBijective_apply_symm_apply _ haa _
  have hε : P.map₂ ε = (P.mapComp g f).hom ≫ adj.counit ≫ (P.mapId b).inv :=
    Equiv.ofBijective_apply_symm_apply _ hbb _
  { unit := η
    counit := ε
    left_triangle := hab <| by
      have h := map_leftZigzag P η ε
      simp only [hη, hε, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id] at h
      rw [adj.left_triangle, ← map_leftUnitor_comp_rightUnitor_inv P] at h
      exact ((cancel_mono _).mp ((cancel_epi _).mp h)).symm
    right_triangle := hba <| by
      have h := map_rightZigzag P η ε
      simp only [hη, hε, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id] at h
      rw [adj.right_triangle, ← map_rightUnitor_comp_leftUnitor_inv P] at h
      exact ((cancel_mono _).mp ((cancel_epi _).mp h)).symm }

end

open MonoidalCategory MonoidalClosed

private noncomputable def functorCategoryIso {A A' B B' : Cat.{u, u}} (eA : A ≅ A')
    (eB : B ≅ B') : Cat.of (A ⥤ B) ≅ Cat.of (A' ⥤ B') where
  hom := ((Functor.whiskeringLeft _ _ _).obj eA.inv.toFunctor ⋙
    (Functor.whiskeringRight _ _ _).obj eB.hom.toFunctor).toCatHom
  inv := ((Functor.whiskeringLeft _ _ _).obj eA.hom.toFunctor ⋙
    (Functor.whiskeringRight _ _ _).obj eB.inv.toFunctor).toCatHom
  hom_inv_id := Cat.Hom.ext <| congrArg₂ (fun H K ↦ (Functor.whiskeringLeft _ _ _).obj H ⋙
    (Functor.whiskeringRight _ _ _).obj K) (congrArg Cat.Hom.toFunctor eA.hom_inv_id)
      (congrArg Cat.Hom.toFunctor eB.hom_inv_id)
  inv_hom_id := Cat.Hom.ext <| congrArg₂ (fun H K ↦ (Functor.whiskeringLeft _ _ _).obj H ⋙
    (Functor.whiskeringRight _ _ _).obj K) (congrArg Cat.Hom.toFunctor eA.inv_hom_id)
      (congrArg Cat.Hom.toFunctor eB.inv_hom_id)

private noncomputable def counitIso (C : Type u) [Category.{u} C] :
    hoFunctor.obj (nerve C) ≅ Cat.of C :=
  nerveFunctorCompHoFunctorIso.app (Cat.of C)

private theorem map_nerveMap_comp_counitIso {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) :
    hoFunctor.map (nerveMap F) ≫ (counitIso D).hom = (counitIso C).hom ≫ F.toCatHom :=
  nerveAdjunction.counit.naturality (X := Cat.of C) (Y := Cat.of D) F.toCatHom

private theorem toFunctor_map_nerveMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) : (hoFunctor.map (nerveMap F)).toFunctor =
      ((counitIso C).hom.toFunctor ⋙ F) ⋙ (counitIso D).inv.toFunctor :=
  congrArg Cat.Hom.toFunctor ((Iso.eq_comp_inv _).mpr (map_nerveMap_comp_counitIso F))

private noncomputable def functorCategoryCounitIso (C D : Type u) [Category.{u} C]
    [Category.{u} D] :
    (ihom (hoFunctor.obj (nerve C))).obj (hoFunctor.obj (nerve D)) ≅ Cat.of (C ⥤ D) :=
  functorCategoryIso (counitIso C) (counitIso D)

private theorem bijective_map_comp_curry_ihomEval (C D : Type u) [Category.{u} C]
    [Category.{u} D] (K : SSet.{u}) :
    Function.Bijective (fun x : K ⟶ (ihom (nerve C)).obj (nerve D) ↦
      hoFunctor.map x ≫ curry (hoFunctor.ihomEval (nerve C) (nerve D))) := by
  have e : (fun x : K ⟶ (ihom (nerve C)).obj (nerve D) ↦
      hoFunctor.map x ≫ curry (hoFunctor.ihomEval (nerve C) (nerve D))) =
      (fun v ↦ curry v) ∘ (fun w ↦ Functor.LaxMonoidal.μ hoFunctor _ K ≫ w) ∘
        (fun u ↦ hoFunctor.map u) ∘ (fun x ↦ uncurry x) :=
    funext fun x ↦ hoFunctor.map_comp_curry_ihomEval x
  have hh : Function.Bijective (fun u : nerve C ⊗ K ⟶ nerve D ↦ hoFunctor.map u) := by
    have : (fun u : nerve C ⊗ K ⟶ nerve D ↦ hoFunctor.map u) =
        (fun w ↦ w ≫ (counitIso D).inv) ∘ (nerveAdjunction.homEquiv _ (Cat.of D)).symm :=
      funext fun u ↦
        (Iso.eq_comp_inv _).mpr (nerveAdjunction.homEquiv_counit _ (Cat.of D) u).symm
    rw [this]
    exact (Equiv.bijective ⟨fun w ↦ w ≫ (counitIso D).inv, fun w ↦ w ≫ (counitIso D).hom,
      fun w ↦ by simp, fun w ↦ by simp⟩).comp (Equiv.bijective _)
  rw [e]
  refine ((ihom.adjunction _).homEquiv _ _).bijective.comp ?_
  refine (Equiv.bijective ⟨fun w ↦ Functor.LaxMonoidal.μ hoFunctor _ K ≫ w,
    fun w ↦ inv (Functor.LaxMonoidal.μ hoFunctor _ K) ≫ w, fun w ↦ by simp,
    fun w ↦ by simp⟩).comp (hh.comp ((ihom.adjunction _).homEquiv _ _).symm.bijective)

private noncomputable def ihomNerveHom (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (ihom (nerve C)).obj (nerve D) ⟶ nerve (C ⥤ D) :=
  nerveAdjunction.homEquiv _ (Cat.of (C ⥤ D))
    (curry (hoFunctor.ihomEval (nerve C) (nerve D)) ≫ (functorCategoryCounitIso C D).hom)

private instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (ihomNerveHom C D) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro K
  have : (fun x : K ⟶ (ihom (nerve C)).obj (nerve D) ↦ x ≫ ihomNerveHom C D) =
      nerveAdjunction.homEquiv _ (Cat.of (C ⥤ D)) ∘
        (fun v ↦ v ≫ (functorCategoryCounitIso C D).hom) ∘
          (fun x ↦ hoFunctor.map x ≫ curry (hoFunctor.ihomEval (nerve C) (nerve D))) := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, Category.assoc,
      Adjunction.homEquiv_naturality_left]
    rfl
  rw [this]
  exact (Equiv.bijective _).comp ((Equiv.bijective ⟨fun v ↦ v ≫ (functorCategoryCounitIso C D).hom,
    fun v ↦ v ≫ (functorCategoryCounitIso C D).inv, fun v ↦ by simp, fun v ↦ by simp⟩).comp
      (bijective_map_comp_curry_ihomEval C D K))

noncomputable def ihomNerveIso (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (ihom (nerve C)).obj (nerve D) ≅ nerve (C ⥤ D) :=
  asIso (ihomNerveHom C D)

private theorem curry_ihomEval_comp_functorCategoryCounitIso (C D : Type u) [Category.{u} C]
    [Category.{u} D] :
    curry (hoFunctor.ihomEval (nerve C) (nerve D)) ≫ (functorCategoryCounitIso C D).hom =
      hoFunctor.map (ihomNerveHom C D) ≫ (counitIso (C ⥤ D)).hom :=
  ((nerveAdjunction.homEquiv _ (Cat.of (C ⥤ D))).symm_apply_apply _).symm.trans
    (nerveAdjunction.homEquiv_counit _ (Cat.of (C ⥤ D)) (ihomNerveHom C D))

private instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (curry (hoFunctor.ihomEval (nerve C) (nerve D))) := by
  rw [(Iso.eq_comp_inv _).mpr (curry_ihomEval_comp_functorCategoryCounitIso C D)]
  infer_instance

def QCat.nerveObj (C : Type u) [Category.{u} C] : QCat.{u} := ⟨nerve C, inferInstance⟩

def QCat.nerveMap {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    QCat.nerveObj C ⟶ QCat.nerveObj D := ObjectProperty.homMk (CategoryTheory.nerveMap F)

private instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (QCat.homotopyFunctorHom (QCat.nerveObj C) (QCat.nerveObj D)).IsEquivalence := by
  have : (hoFunctor.ihomComparison (QCat.nerveObj C).obj
      (QCat.nerveObj D).obj).IsEquivalence := by
    rw [hoFunctor.ihomComparison_eq_curry]
    exact (Cat.equivOfIso
      (asIso (curry (hoFunctor.ihomEval (nerve C) (nerve D))))).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (QCat.homotopyFunctorHomIso _ _).symm

noncomputable def QCat.nerveHomEquivalence (C D : Type u) [Category.{u} C] [Category.{u} D] :
    (QCat.nerveObj C ⟶ QCat.nerveObj D) ≌ (C ⥤ D) :=
  (QCat.homotopyFunctorHom (QCat.nerveObj C) (QCat.nerveObj D)).asEquivalence.trans
    (Cat.equivOfIso (functorCategoryCounitIso C D))

theorem QCat.nerveHomEquivalence_functor_obj_eq {C D : Type u} [Category.{u} C]
    [Category.{u} D] (F : C ⥤ D) :
    (QCat.nerveHomEquivalence C D).functor.obj (QCat.nerveMap F) = F :=
  (congrArg (fun H ↦ ((counitIso C).inv.toFunctor ⋙ H) ⋙ (counitIso D).hom.toFunctor)
    (toFunctor_map_nerveMap F)).trans (congrArg₂ (fun H K ↦ H ⋙ F ⋙ K)
      (congrArg Cat.Hom.toFunctor (counitIso C).inv_hom_id)
      (congrArg Cat.Hom.toFunctor (counitIso D).inv_hom_id))

@[nolint defsWithUnderscore]
noncomputable def QCat.nerveHomEquivalence_functor_obj {C D : Type u} [Category.{u} C]
    [Category.{u} D] (F : C ⥤ D) :
    (QCat.nerveHomEquivalence C D).functor.obj (QCat.nerveMap F) ≅ F :=
  eqToIso (QCat.nerveHomEquivalence_functor_obj_eq F)

private noncomputable def homotopyNerveAdjunction {C D : Type u} [Category.{u} C]
    [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (hoFunctor.map (nerveMap F)).toFunctor ⊣ (hoFunctor.map (nerveMap G)).toFunctor :=
  ((((Cat.equivOfIso (counitIso C)).toAdjunction.comp adj).comp
    (Cat.equivOfIso (counitIso D)).symm.toAdjunction).ofNatIsoLeft
      (eqToIso (toFunctor_map_nerveMap F).symm)).ofNatIsoRight
        (eqToIso (toFunctor_map_nerveMap G).symm)

private theorem bijective_homotopyFunctor_map₂ (C D : Type u) [Category.{u} C] [Category.{u} D]
    {f g : QCat.nerveObj C ⟶ QCat.nerveObj D} :
    Function.Bijective (QCat.homotopyFunctor.map₂ (f := f) (g := g)) := by
  rw [funext QCat.homotopyFunctor_map₂]
  exact (Function.bijective_iff_has_inverse.mpr
    ⟨Cat.Hom₂.toNatTrans, fun _ ↦ rfl, fun _ ↦ rfl⟩).comp
      ((Functor.FullyFaithful.ofFullyFaithful
        (QCat.homotopyFunctorHom (QCat.nerveObj C) (QCat.nerveObj D))).map_bijective f g)

noncomputable def QCat.nerveAdjunction {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Bicategory.Adjunction (QCat.nerveMap F) (QCat.nerveMap G) :=
  adjunctionOfMap QCat.homotopyFunctor.toPseudofunctor (homotopyNerveAdjunction adj).toCat
    (bijective_homotopyFunctor_map₂ C C) (bijective_homotopyFunctor_map₂ D D)
    (bijective_homotopyFunctor_map₂ C D).1 (bijective_homotopyFunctor_map₂ D C).1

end SSet
