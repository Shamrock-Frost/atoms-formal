import Mathlib.CategoryTheory.Monoidal.DayConvolution

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory.ExternalProduct
  CategoryTheory.MonoidalCategory.DayConvolution

namespace CategoryTheory.MonoidalCategory.DayConvolution

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {V : Type u₂} [Category.{v₂} V] [MonoidalCategory V]

@[instance_reducible]
noncomputable def ofHasPointwiseLeftKanExtension (F G : C ⥤ V)
    [(tensor C).HasPointwiseLeftKanExtension (F ⊠ G)] : DayConvolution F G where
  convolution := (tensor C).pointwiseLeftKanExtension (F ⊠ G)
  unit := (tensor C).pointwiseLeftKanExtensionUnit (F ⊠ G)
  isPointwiseLeftKanExtensionUnit :=
    (tensor C).pointwiseLeftKanExtensionIsPointwiseLeftKanExtension (F ⊠ G)

theorem map_id (F G : C ⥤ V) [DayConvolution F G] :
    DayConvolution.map (𝟙 F) (𝟙 G) = 𝟙 (F ⊛ G) :=
  Functor.hom_ext_of_isLeftKanExtension _ (unit F G) _ _ (by
    ext ⟨x, y⟩
    simp [unit_app_map_app])

theorem map_comp {F F' F'' G G' G'' : C ⥤ V} [DayConvolution F G] [DayConvolution F' G']
    [DayConvolution F'' G''] (f : F ⟶ F') (f' : F' ⟶ F'') (g : G ⟶ G') (g' : G' ⟶ G'') :
    DayConvolution.map (f ≫ f') (g ≫ g') = DayConvolution.map f g ≫ DayConvolution.map f' g' :=
  Functor.hom_ext_of_isLeftKanExtension _ (unit F G) _ _ (by
    ext ⟨x, y⟩
    simp [unit_app_map_app, tensorHom_comp_tensorHom_assoc, unit_app_map_app_assoc])

end CategoryTheory.MonoidalCategory.DayConvolution
