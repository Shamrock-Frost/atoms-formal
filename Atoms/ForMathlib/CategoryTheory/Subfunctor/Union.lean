import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Limits.Set
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

universe w v u

namespace CategoryTheory.Subfunctor

open Limits

section Colimits

variable {C : Type u} [Category.{v} C] (X : C ⥤ Type w)

@[simps]
def toFunctorFunctor : Subfunctor X ⥤ (C ⥤ Type w) where
  obj G := G.toFunctor
  map h := Subfunctor.homOfLe (leOfHom h)

@[simps]
def objFunctor (c : C) : Subfunctor X ⥤ Set (X.obj c) where
  obj G := G.obj c
  map f := homOfLE (leOfHom f c)

instance preservesColimitsOfShape_toFunctorFunctor {J : Type*} [Category* J]
    [IsFilteredOrEmpty J] : PreservesColimitsOfShape J (toFunctorFunctor X) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (Preorder.colimitCoconeOfIsLUB F isLUB_iSup).isColimit
        (evaluationJointlyReflectsColimits _ (fun c ↦ IsColimit.ofIsoColimit
          (isColimitOfPreserves Set.functorToTypes
            ((Preorder.colimitCoconeOfIsLUB (F ⋙ objFunctor X c)
              isLUB_iSup).isColimit))
          (Cocone.ext (Set.functorToTypes.mapIso (CategoryTheory.eqToIso (by cat_disch))))))

end Colimits

variable {C : Type u} [Category.{v} C] {X : C ⥤ Type w}

theorem homOfLe_mem_iff_of_eq (W : MorphismProperty (C ⥤ Type w)) {S₁ S₂ T₁ T₂ : Subfunctor X}
    (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂) (hS : S₁ = S₂) (hT : T₁ = T₂) :
    W (Subfunctor.homOfLe h₁) ↔ W (Subfunctor.homOfLe h₂) := by
  subst hS hT
  rfl

theorem transfiniteCompositionsOfShape_homOfLe {J : Type*} [LinearOrder J] [OrderBot J]
    [OrderTop J] [SuccOrder J] [WellFoundedLT J] (W : MorphismProperty (C ⥤ Type w))
    (G : J → Subfunctor X) (hG : Monotone G)
    (hlim : ∀ m : J, Order.IsSuccLimit m → G m = ⨆ k : Set.Iio m, G k)
    (hstep : ∀ j : J, ¬IsMax j → W (Subfunctor.homOfLe (hG (Order.le_succ j)))) :
    W.transfiniteCompositionsOfShape J (Subfunctor.homOfLe (hG bot_le : G ⊥ ≤ G ⊤)) := by
  have hc : hG.functor.IsWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨Preorder.isColimitOfIsLUB _ _ (by
      change IsLUB (Set.range fun k : Set.Iio m ↦ G k) (G m)
      rw [hlim m hm]
      apply isLUB_iSup)⟩⟩
  exact MorphismProperty.TransfiniteCompositionOfShape.mem _
    { F := hG.functor ⋙ toFunctorFunctor X
      isoBot := Iso.refl _
      isWellOrderContinuous :=
        ⟨fun m hm ↦ ⟨isColimitOfPreserves (toFunctorFunctor X)
          (Functor.isColimitOfIsWellOrderContinuous hG.functor m hm)⟩⟩
      incl := { app j := Subfunctor.homOfLe (hG le_top) }
      isColimit := isColimitOfPreserves (toFunctorFunctor X)
        (Preorder.colimitCoconeOfIsLUB hG.functor (pt := G ⊤)
          ⟨by rintro _ ⟨k, rfl⟩; exact hG le_top, fun _ hu ↦ hu ⟨⊤, rfl⟩⟩).isColimit
      map_mem j hj := hstep j hj }

theorem exists_map_homOfLe_app_eq {D : Type*} [Category D] (F : (C ⥤ Type w) ⥤ D ⥤ Type w)
    {ι : Type w} [Preorder ι] [IsFiltered ι] [PreservesColimitsOfShape ι F]
    (G : ι ⥤ Subfunctor X) {T : Subfunctor X} (hT : IsLUB (Set.range G.obj) T) {b : D}
    (z : (F.obj T.toFunctor).obj b) :
    ∃ (i : ι) (y : (F.obj (G.obj i).toFunctor).obj b),
      (F.map (Subfunctor.homOfLe (hT.1 ⟨i, rfl⟩))).app b y = z := by
  let hc := isColimitOfPreserves ((evaluation D (Type w)).obj b)
    (isColimitOfPreserves F (isColimitOfPreserves (Subfunctor.toFunctorFunctor X)
      (Preorder.colimitCoconeOfIsLUB G hT).isColimit))
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective _ hc z
  exact ⟨i, y, hy⟩

end CategoryTheory.Subfunctor
