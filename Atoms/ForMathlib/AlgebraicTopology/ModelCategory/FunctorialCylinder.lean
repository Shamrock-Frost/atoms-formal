import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [CategoryWithWeakEquivalences C]
  [CategoryWithCofibrations C] [HasBinaryCoproducts C]

structure FunctorialCylinder where
  I : C ⥤ C
  i₀ : 𝟭 C ⟶ I
  i₁ : 𝟭 C ⟶ I
  π : I ⟶ 𝟭 C
  i₀_π : i₀ ≫ π = 𝟙 _
  i₁_π : i₁ ≫ π = 𝟙 _
  weakEquivalence_π (X : C) : WeakEquivalence (π.app X)
  cofibration_i (X : C) : Cofibration (coprod.desc (i₀.app X) (i₁.app X))

namespace FunctorialCylinder

variable {C} (P : FunctorialCylinder C)

@[simps]
def cylinder (X : C) : Cylinder X where
  I := P.I.obj X
  i₀ := P.i₀.app X
  i₁ := P.i₁.app X
  π := P.π.app X
  i₀_π := NatTrans.congr_app P.i₀_π X
  i₁_π := NatTrans.congr_app P.i₁_π X
  weakEquivalence_π := P.weakEquivalence_π X

instance isGood_cylinder (X : C) : (P.cylinder X).IsGood where
  cofibration_i := P.cofibration_i X

@[simps]
def symm [(cofibrations C).RespectsIso] : FunctorialCylinder C where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π
  i₀_π := P.i₁_π
  i₁_π := P.i₀_π
  weakEquivalence_π := P.weakEquivalence_π
  cofibration_i X := by
    have h : coprod.desc (P.i₁.app X) (P.i₀.app X) =
        (coprod.braiding X X).hom ≫ coprod.desc (P.i₀.app X) (P.i₁.app X) := by
      ext1
      · rw [coprod.inl_desc, coprod.braiding_hom, coprod.inl_desc_assoc, coprod.inr_desc]
      · rw [coprod.inr_desc, coprod.braiding_hom, coprod.inr_desc_assoc, coprod.inl_desc]
    rw [cofibration_iff, h]
    exact MorphismProperty.RespectsIso.precomp _ _ _ ((cofibration_iff _).1 (P.cofibration_i X))

end FunctorialCylinder

variable {C}

@[simps]
noncomputable def FunctorialCylinder.ofInterval [(weakEquivalences C).RespectsIso]
    [(cofibrations C).RespectsIso] (K : C ⥤ C ⥤ C) {T : C} (hT : IsTerminal T)
    (e : K.obj T ≅ 𝟭 C) {J : C} (v₀ v₁ : T ⟶ J)
    (hK : ∀ X : C, PreservesColimit (pair T T) (K.flip.obj X))
    (hπ : ∀ X : C, WeakEquivalence ((K.map (hT.from J)).app X))
    (hi : ∀ X : C, Cofibration ((K.map (coprod.desc v₀ v₁)).app X)) :
    FunctorialCylinder C where
  I := K.obj J
  i₀ := e.inv ≫ K.map v₀
  i₁ := e.inv ≫ K.map v₁
  π := K.map (hT.from J) ≫ e.hom
  i₀_π := by
    rw [Category.assoc, ← K.map_comp_assoc, hT.hom_ext (v₀ ≫ _) (𝟙 T), K.map_id,
      Category.id_comp, e.inv_hom_id]
  i₁_π := by
    rw [Category.assoc, ← K.map_comp_assoc, hT.hom_ext (v₁ ≫ _) (𝟙 T), K.map_id,
      Category.id_comp, e.inv_hom_id]
  weakEquivalence_π X := by
    rw [weakEquivalence_iff, NatTrans.comp_app]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ ((weakEquivalence_iff _).1 (hπ X))
  cofibration_i X := by
    have := hK X
    have h : coprod.desc ((e.inv ≫ K.map v₀).app X) ((e.inv ≫ K.map v₁).app X) =
        (coprod.map (Y := (K.flip.obj X).obj T) (Z := (K.flip.obj X).obj T) (e.inv.app X)
          (e.inv.app X) ≫ coprodComparison (K.flip.obj X) T T) ≫
          (K.map (coprod.desc v₀ v₁)).app X := by
      ext1
      · rw [coprod.inl_desc, Category.assoc, coprod.inl_map_assoc, coprodComparison_inl_assoc,
          Functor.flip_obj_map, ← NatTrans.comp_app (K.map _), ← K.map_comp, coprod.inl_desc,
          NatTrans.comp_app]
      · rw [coprod.inr_desc, Category.assoc, coprod.inr_map_assoc, coprodComparison_inr_assoc,
          Functor.flip_obj_map, ← NatTrans.comp_app (K.map _), ← K.map_comp, coprod.inr_desc,
          NatTrans.comp_app]
    have : IsIso (coprod.map (Y := (K.flip.obj X).obj T) (Z := (K.flip.obj X).obj T)
        (e.inv.app X) (e.inv.app X)) := inferInstanceAs (IsIso (coprod.map (e.inv.app X) _))
    rw [cofibration_iff, h]
    exact MorphismProperty.RespectsIso.precomp _ _ _ ((cofibration_iff _).1 (hi X))

end HomotopicalAlgebra
