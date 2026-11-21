import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Monoidal.DayConvolution
import Mathlib.CategoryTheory.Monoidal.Types.Basic

open CategoryTheory Limits
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace CategoryTheory.MonoidalCategory.DayConvolution

universe v₁ u₁ w

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable (F G : C ⥤ Type w) [DayConvolution F G]

noncomputable def colimitTypeEquiv (c : C) :
    (CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).ColimitType ≃ (F ⊛ G).obj c :=
  ((Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨isPointwiseLeftKanExtensionUnit F G c⟩).equiv

@[simp]
theorem colimitTypeEquiv_ιColimitType (c : C) (j : CostructuredArrow (tensor C) c)
    (z : (CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).obj j) :
    colimitTypeEquiv F G c ((CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).ιColimitType j z) =
      (F ⊛ G).map j.hom ((unit F G).app j.left z) :=
  rfl

theorem map_unit_app_jointly_surjective {c : C} (t : (F ⊛ G).obj c) :
    ∃ (x y : C) (u : x ⊗ y ⟶ c) (a : F.obj x) (b : G.obj y),
      (F ⊛ G).map u ((unit F G).app (x, y) (a, b)) = t := by
  obtain ⟨j, z, rfl⟩ :=
    Types.jointly_surjective_of_isColimit (isPointwiseLeftKanExtensionUnit F G c) t
  exact ⟨j.left.1, j.left.2, j.hom, z.1, z.2, rfl⟩

theorem map_unit_app_eq_map_unit_app_iff {c x y x' y' : C} (u : x ⊗ y ⟶ c)
    (u' : x' ⊗ y' ⟶ c) (a : F.obj x) (b : G.obj y) (a' : F.obj x') (b' : G.obj y') :
    (F ⊛ G).map u ((unit F G).app (x, y) (a, b)) =
        (F ⊛ G).map u' ((unit F G).app (x', y') (a', b')) ↔
      Relation.EqvGen (CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).ColimitTypeRel
        ⟨CostructuredArrow.mk (Y := (x, y)) u, (a, b)⟩
        ⟨CostructuredArrow.mk (Y := (x', y')) u', (a', b')⟩ := by
  have h := (colimitTypeEquiv F G c).apply_eq_iff_eq
    (x := (CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).ιColimitType (.mk (Y := (x, y)) u)
      (a, b))
    (y := (CostructuredArrow.proj (tensor C) c ⋙ F ⊠ G).ιColimitType (.mk (Y := (x', y')) u')
      (a', b'))
  rw [colimitTypeEquiv_ιColimitType, colimitTypeEquiv_ιColimitType,
    Functor.ιColimitType_eq_iff] at h
  exact h

def externalProductHomEquiv (H : C ⥤ Type w) :
    (F ⊠ G ⟶ tensor C ⋙ H) ≃ { φ : ∀ x y : C, F.obj x → G.obj y → H.obj (x ⊗ y) //
      ∀ {x x' y y' : C} (f : x ⟶ x') (g : y ⟶ y') (a : F.obj x) (b : G.obj y),
        φ x' y' (F.map f a) (G.map g b) = H.map (f ⊗ₘ g) (φ x y a b) } where
  toFun α := ⟨fun x y a b ↦ α.app (x, y) ((a, b) : F.obj x × G.obj y),
    fun {x x' y y'} f g a b ↦
      NatTrans.naturality_apply α (X := (x, y)) (Y := (x', y')) (f, g)
        ((a, b) : F.obj x × G.obj y)⟩
  invFun φ :=
    { app p := TypeCat.ofHom fun z ↦ φ.1 p.1 p.2 z.1 z.2
      naturality p q f := by ext z; exact φ.2 f.1 f.2 z.1 z.2 }
  left_inv α := rfl
  right_inv φ := rfl

noncomputable def homEquiv (H : C ⥤ Type w) :
    (F ⊛ G ⟶ H) ≃ { φ : ∀ x y : C, F.obj x → G.obj y → H.obj (x ⊗ y) //
      ∀ {x x' y y' : C} (f : x ⟶ x') (g : y ⟶ y') (a : F.obj x) (b : G.obj y),
        φ x' y' (F.map f a) (G.map g b) = H.map (f ⊗ₘ g) (φ x y a b) } :=
  (corepresentableBy F G).homEquiv.trans (externalProductHomEquiv F G H)

theorem homEquiv_apply (H : C ⥤ Type w) (α : F ⊛ G ⟶ H) (x y : C) (a : F.obj x)
    (b : G.obj y) :
    (homEquiv F G H α).1 x y a b = α.app (x ⊗ y) ((unit F G).app (x, y) (a, b)) :=
  rfl

theorem homEquiv_symm_app_unit_app (H : C ⥤ Type w)
    (φ : { φ : ∀ x y : C, F.obj x → G.obj y → H.obj (x ⊗ y) //
      ∀ {x x' y y' : C} (f : x ⟶ x') (g : y ⟶ y') (a : F.obj x) (b : G.obj y),
        φ x' y' (F.map f a) (G.map g b) = H.map (f ⊗ₘ g) (φ x y a b) })
    (x y : C) (a : F.obj x) (b : G.obj y) :
    ((homEquiv F G H).symm φ).app (x ⊗ y) ((unit F G).app (x, y) (a, b)) = φ.1 x y a b := by
  rw [← homEquiv_apply, Equiv.apply_symm_apply]

end CategoryTheory.MonoidalCategory.DayConvolution
