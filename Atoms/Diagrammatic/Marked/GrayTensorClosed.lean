import Atoms.Diagrammatic.Marked.GrayTensor
import Atoms.Homotopical.Marked.Extension

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

def CoversEpi (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u}) : Prop :=
  ∀ x : MarkedSite atomMarking,
    Epi (F.map ((MarkedPresheaf.yoneda atomMarking).map (MarkedSite.toSelf x)))

noncomputable def homFor (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u}) (hF : CoversEpi F) :
    MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} :=
  MarkedPresheaf.nerve (MarkedPresheaf.yoneda atomMarking ⋙ F) hF

private theorem coversEpi_of_isIso_forget_map (F : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u})
    (hF : ∀ {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y), IsIso (MarkedPresheaf.forget.map f) →
      IsIso (MarkedPresheaf.forget.map (F.map f))) :
    CoversEpi F := fun x =>
  have := hF _ (inferInstance : IsIso (MarkedPresheaf.forget.map
    ((MarkedPresheaf.yoneda.{u} atomMarking).map (MarkedSite.toSelf x))))
  MarkedPresheaf.forget.epi_of_epi_map inferInstance

theorem coversEpi_tensorRight (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    CoversEpi (tensorRight pseudo X) :=
  coversEpi_of_isIso_forget_map _ fun f hf =>
    have := (isIso_prod_iff (C := DiagSet.{u}) (D := DiagSet.{u})
      (f := (MarkedPresheaf.forget.map (Prod.mkHom (f) (𝟙 X)).1,
        MarkedPresheaf.forget.map (Prod.mkHom (f) (𝟙 X)).2))).2 ⟨hf, inferInstance⟩
    @Functor.map_isIso _ _ _ _ _ _ grayTensorBifunctor _ this

theorem coversEpi_tensorLeft (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    CoversEpi (tensorLeft pseudo X) :=
  coversEpi_of_isIso_forget_map _ fun f hf =>
    have := (isIso_prod_iff (C := DiagSet.{u}) (D := DiagSet.{u})
      (f := (MarkedPresheaf.forget.map (Prod.mkHom (𝟙 X) (f)).1,
        MarkedPresheaf.forget.map (Prod.mkHom (𝟙 X) (f)).2))).2 ⟨inferInstance, hf⟩
    @Functor.map_isIso _ _ _ _ _ _ grayTensorBifunctor _ this

noncomputable def markedHomRight (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} :=
  homFor (tensorRight pseudo X) (coversEpi_tensorRight pseudo X)

noncomputable def tensorRightAdjunction (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    tensorRight pseudo X ⊣ markedHomRight pseudo X :=
  MarkedPresheaf.adjunctionOfPreservesColimits _ (coversEpi_tensorRight pseudo X)

noncomputable def markedHomLeft (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} :=
  homFor (tensorLeft pseudo X) (coversEpi_tensorLeft pseudo X)

noncomputable def tensorLeftAdjunction (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    tensorLeft pseudo X ⊣ markedHomLeft pseudo X :=
  MarkedPresheaf.adjunctionOfPreservesColimits _ (coversEpi_tensorLeft pseudo X)

instance isLeftAdjoint_tensorRight (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    (tensorRight pseudo X).IsLeftAdjoint :=
  ⟨_, ⟨tensorRightAdjunction pseudo X⟩⟩

instance isLeftAdjoint_tensorLeft (pseudo : Bool) (X : MarkedDiagSet.{u}) :
    (tensorLeft pseudo X).IsLeftAdjoint :=
  ⟨_, ⟨tensorLeftAdjunction pseudo X⟩⟩

noncomputable def markedHomRestrict {A B : MarkedDiagSet.{u}} (i : A ⟶ B) :
    markedHomRight false B ⟶ markedHomRight false A :=
  conjugateEquiv (tensorRightAdjunction false B) (tensorRightAdjunction false A)
    ((Functor.curry.obj (markedTensorBifunctor false)).flip.map i)

theorem markedHomRestrict_id (B : MarkedDiagSet.{u}) :
    markedHomRestrict (𝟙 B) = 𝟙 (markedHomRight false B) :=
  (congrArg (conjugateEquiv _ _) (CategoryTheory.Functor.map_id _ B)).trans (conjugateEquiv_id _)

theorem markedHomRestrict_comp {A B C : MarkedDiagSet.{u}} (i : A ⟶ B) (j : B ⟶ C) :
    markedHomRestrict (i ≫ j) = markedHomRestrict j ≫ markedHomRestrict i :=
  (congrArg (conjugateEquiv _ _) (CategoryTheory.Functor.map_comp _ i j)).trans
    (conjugateEquiv_comp _ _ _ _ _).symm

noncomputable def markedHomRightBifunctor :
    MarkedDiagSet.{u}ᵒᵖ ⥤ MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj B := markedHomRight false B.unop
  map i := markedHomRestrict i.unop
  map_id B := markedHomRestrict_id B.unop
  map_comp i j := markedHomRestrict_comp j.unop i.unop

theorem homEquiv_markedHomRestrict {A B T Z : MarkedDiagSet.{u}} (i : A ⟶ B)
    (g : markedGrayTensor T B ⟶ Z) :
    (tensorRightAdjunction false A).homEquiv T Z (markedTensorMap false (𝟙 T) i ≫ g) =
      (tensorRightAdjunction false B).homEquiv T Z g ≫ (markedHomRestrict i).app Z := by
  have h₁ := (tensorRightAdjunction false A).homEquiv_unit T Z (markedTensorMap false (𝟙 T) i ≫ g)
  have h₂ := (tensorRightAdjunction false B).homEquiv_unit T Z g
  have h₃ := unit_conjugateEquiv (tensorRightAdjunction false B) (tensorRightAdjunction false A)
    ((Functor.curry.obj (markedTensorBifunctor false)).flip.map i) T
  rw [h₁, h₂]
  exact (congrArg _ ((markedHomRight false A).map_comp _ _)).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₃.symm).trans <|
    (Category.assoc _ _ _).trans <| (congrArg _ ((markedHomRestrict i).naturality g).symm).trans
      (Category.assoc _ _ _).symm

noncomputable def markedTensorRightParametrizedAdjunction :
    (Functor.curry.obj (markedTensorBifunctor.{u} false)).flip ⊣₂ markedHomRightBifunctor :=
  ParametrizedAdjunction.mk' (tensorRightAdjunction false) fun {_ _} f {_ _} g =>
    homEquiv_markedHomRestrict f g

end Atoms.Diagrammatic
