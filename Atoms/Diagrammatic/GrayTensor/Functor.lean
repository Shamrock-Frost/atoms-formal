import Atoms.Shape.GrayTensor
import Atoms.Diagrammatic.DiagrammaticSet
import Atoms.ForMathlib.CategoryTheory.Monoidal.ExternalProduct
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

open CategoryTheory Limits Opposite Atoms.Shape
open scoped MonoidalCategory.ExternalProduct

universe w w' u

namespace Atoms.Diagrammatic

abbrev grayTensorIndex : Atomᵒᵖ × Atomᵒᵖ ⥤ Atomᵒᵖ :=
  (prodOpEquiv Atom (D := Atom)).inverse ⋙ Atom.grayTensorFunctor.op

noncomputable def grayTensorBifunctor : DiagSet.{u} × DiagSet.{u} ⥤ DiagSet.{u} :=
  MonoidalCategory.externalProductBifunctor _ _ (Type u) ⋙ grayTensorIndex.lan

noncomputable abbrev grayTensor (X Y : DiagSet.{u}) : DiagSet.{u} :=
  grayTensorBifunctor.obj (X, Y)

noncomputable def grayTensorUnit (X Y : DiagSet.{u}) :
    X ⊠ Y ⟶ grayTensorIndex ⋙ grayTensor X Y :=
  grayTensorIndex.lanUnit.app (X ⊠ Y)

instance isLeftKanExtension_grayTensor (X Y : DiagSet.{u}) :
    (grayTensor X Y).IsLeftKanExtension (grayTensorUnit X Y) :=
  inferInstanceAs ((grayTensorIndex.lan.obj (X ⊠ Y)).IsLeftKanExtension
    (grayTensorIndex.lanUnit.app (X ⊠ Y)))

noncomputable def grayTensorCell {X Y : DiagSet.{u}} {U V : Atom}
    (x : diagram X U) (y : diagram Y V) :
    diagram (grayTensor X Y) (Atom.grayTensor U V) :=
  (grayTensorUnit X Y).app (op U, op V) (x, y)

noncomputable abbrev grayTensorRight (Y : DiagSet.{u}) : DiagSet.{u} ⥤ DiagSet.{u} :=
  (Functor.curry.obj grayTensorBifunctor).flip.obj Y

noncomputable abbrev grayTensorLeft (X : DiagSet.{u}) : DiagSet.{u} ⥤ DiagSet.{u} :=
  (Functor.curry.obj grayTensorBifunctor).obj X

theorem grayTensorCell_restrict {X Y : DiagSet.{u}} {U V U' V' : Atom}
    (f : U ⟶ U') (g : V ⟶ V') (x : diagram X U') (y : diagram Y V') :
    grayTensorCell (X.map f.op x) (Y.map g.op y) =
      (grayTensor X Y).map (Atom.grayTensorMap f g).op (grayTensorCell x y) :=
  NatTrans.naturality_apply (grayTensorUnit X Y) (X := (op U', op V')) (Y := (op U, op V))
    (f.op, g.op) ((x, y) : X.obj (op U') × Y.obj (op V'))

theorem grayTensorCell_naturality {X Y X' Y' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') {U V : Atom} (x : diagram X U) (y : diagram Y V) :
    (grayTensorBifunctor.map (f, g)).app (op (Atom.grayTensor U V)) (grayTensorCell x y) =
      grayTensorCell (f.app (op U) x) (g.app (op V) y) :=
  (ConcreteCategory.congr_hom
    (congr_app (grayTensorIndex.lanUnit.naturality
      ((MonoidalCategory.externalProductBifunctor _ _ (Type u)).map
        (X := (X, Y)) (Y := (X', Y')) (f, g)))
        (op U, op V)) ((x, y) : X.obj (op U) × Y.obj (op V))).symm

private theorem preservesColimitsOfSize_grayTensorLeft_small (X : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (grayTensorLeft X) := by
  have := (grayTensorIndex.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  exact ⟨fun {K} _ => inferInstanceAs (PreservesColimitsOfShape K
    ((Functor.curry.obj (MonoidalCategory.externalProductBifunctor _ _ (Type u))).obj X ⋙
      grayTensorIndex.lan))⟩

private theorem preservesColimitsOfSize_grayTensorRight_small (Y : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (grayTensorRight Y) := by
  have := (grayTensorIndex.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  exact ⟨fun {K} _ => inferInstanceAs (PreservesColimitsOfShape K
    ((Functor.curry.obj (MonoidalCategory.externalProductBifunctor _ _ (Type u))).flip.obj Y ⋙
      grayTensorIndex.lan))⟩

noncomputable def grayHomLeft (X : DiagSet.{u}) : DiagSet.{u} ⥤ DiagSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (uliftYoneda.{u} ⋙ grayTensorLeft X)

noncomputable def grayHomRight (Y : DiagSet.{u}) : DiagSet.{u} ⥤ DiagSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} (uliftYoneda.{u} ⋙ grayTensorRight Y)

noncomputable def grayTensorLeftAdjunction (X : DiagSet.{u}) :
    grayTensorLeft X ⊣ grayHomLeft X :=
  have := preservesColimitsOfSize_grayTensorLeft_small X
  Presheaf.uliftYonedaAdjunction.{0} (grayTensorLeft X) (𝟙 _)

noncomputable def grayTensorRightAdjunction (Y : DiagSet.{u}) :
    grayTensorRight Y ⊣ grayHomRight Y :=
  have := preservesColimitsOfSize_grayTensorRight_small Y
  Presheaf.uliftYonedaAdjunction.{0} (grayTensorRight Y) (𝟙 _)

instance preservesColimitsOfSize_grayTensorLeft (X : DiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (grayTensorLeft X) :=
  (grayTensorLeftAdjunction X).leftAdjoint_preservesColimits

instance preservesColimitsOfSize_grayTensorRight (Y : DiagSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (grayTensorRight Y) :=
  (grayTensorRightAdjunction Y).leftAdjoint_preservesColimits

noncomputable def grayHomLeftCellEquiv (X Z : DiagSet.{u}) (V : Atom) :
    diagram ((grayHomLeft X).obj Z) V ≃ (grayTensor X (ball.{u} V) ⟶ Z) :=
  Equiv.ulift

noncomputable def grayHomRightCellEquiv (Y Z : DiagSet.{u}) (U : Atom) :
    diagram ((grayHomRight Y).obj Z) U ≃ (grayTensor (ball.{u} U) Y ⟶ Z) :=
  Equiv.ulift

theorem exists_eq_map_grayTensorCell {X Y : DiagSet.{u}} {T : Atom}
    (z : diagram (grayTensor X Y) T) :
    ∃ (U V : Atom) (x : diagram X U) (y : diagram Y V) (f : T ⟶ Atom.grayTensor U V),
      z = (grayTensor X Y).map f.op (grayTensorCell x y) := by
  obtain ⟨j, w, hw⟩ := Types.jointly_surjective_of_isColimit
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (grayTensorUnit X Y) (op T)) z
  exact ⟨j.left.1.unop, j.left.2.unop, w.1, w.2, j.hom.unop, hw.symm⟩

theorem grayTensor_hom_ext {X Y Z : DiagSet.{u}} {f g : grayTensor X Y ⟶ Z}
    (h : ∀ (U V : Atom) (x : diagram X U) (y : diagram Y V),
      f.app (Opposite.op (Atom.grayTensor U V)) (grayTensorCell x y) =
        g.app (Opposite.op (Atom.grayTensor U V)) (grayTensorCell x y)) : f = g := by
  apply (grayTensor X Y).hom_ext_of_isLeftKanExtension (grayTensorUnit X Y)
  ext ⟨U, V⟩ ⟨x, y⟩
  exact h U.unop V.unop x y

private noncomputable def grayTensorBallUnit (U V : Atom) :
    ball.{u} U ⊠ ball.{u} V ⟶ grayTensorIndex ⋙ ball.{u} (Atom.grayTensor U V) where
  app p := ↾fun xy => ULift.up (Atom.grayTensorMap xy.1.down xy.2.down)
  naturality p q f := by
    ext ⟨⟨x⟩, ⟨y⟩⟩
    exact congrArg ULift.up (Atom.grayTensorMap_comp f.1.unop f.2.unop x y).symm

private noncomputable def grayTensorBallHom (U V : Atom) :
    grayTensor (ball.{u} U) (ball.{u} V) ⟶ ball.{u} (Atom.grayTensor U V) :=
  (grayTensor _ _).descOfIsLeftKanExtension (grayTensorUnit _ _) _ (grayTensorBallUnit U V)

private theorem grayTensorBallHom_app_grayTensorCell {U V A B : Atom} (x : A ⟶ U) (y : B ⟶ V) :
    (grayTensorBallHom.{u} U V).app (op (Atom.grayTensor A B))
        (grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up x) (ULift.up y)) =
      ULift.up (Atom.grayTensorMap x y) :=
  ConcreteCategory.congr_hom
    ((grayTensor _ _).descOfIsLeftKanExtension_fac_app (grayTensorUnit _ _) _
      (grayTensorBallUnit U V) (op A, op B))
    ((ULift.up x, ULift.up y) : (ball.{u} U).obj (op A) × (ball.{u} V).obj (op B))

noncomputable def grayTensorBallIso (U V : Atom) :
    grayTensor (ball.{u} U) (ball.{u} V) ≅ ball.{u} (Atom.grayTensor U V) where
  hom := grayTensorBallHom U V
  inv := uliftYonedaEquiv.symm
    (grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up (𝟙 U)) (ULift.up (𝟙 V)))
  hom_inv_id := by
    refine grayTensor_hom_ext fun A B ⟨x⟩ ⟨y⟩ => ?_
    rw [NatTrans.comp_app, types_comp_apply, grayTensorBallHom_app_grayTensorCell,
      uliftYonedaEquiv_symm_apply_app, NatTrans.id_app, types_id_apply]
    refine (grayTensorCell_restrict (X := ball.{u} U) (Y := ball.{u} V) x y _ _).symm.trans ?_
    exact congrArg₂ (grayTensorCell (X := ball.{u} U) (Y := ball.{u} V))
      (congrArg ULift.up (Category.comp_id x)) (congrArg ULift.up (Category.comp_id y))
  inv_hom_id := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, grayTensorBallHom_app_grayTensorCell,
      Atom.grayTensorMap_id]
    rfl

@[simp] theorem grayTensorBallIso_hom_app_grayTensorCell {U V A B : Atom} (x : A ⟶ U)
    (y : B ⟶ V) :
    (grayTensorBallIso.{u} U V).hom.app (op (Atom.grayTensor A B))
        (grayTensorCell (X := ball.{u} U) (Y := ball.{u} V) (ULift.up x) (ULift.up y)) =
      ULift.up (Atom.grayTensorMap x y) :=
  grayTensorBallHom_app_grayTensorCell x y

noncomputable def grayTensorYonedaIso :
    (uliftYoneda.{u}.prod uliftYoneda.{u}) ⋙ grayTensorBifunctor.{u} ≅
      Atom.grayTensorFunctor ⋙ uliftYoneda.{u} :=
  NatIso.ofComponents (fun p => grayTensorBallIso p.1 p.2) fun {p q} f => by
    refine grayTensor_hom_ext fun A B ⟨x⟩ ⟨y⟩ => ?_
    rw [NatTrans.comp_app, NatTrans.comp_app, types_comp_apply, types_comp_apply]
    refine (congrArg ((grayTensorBallIso q.1 q.2).hom.app _)
      (grayTensorCell_naturality (uliftYoneda.{u}.map f.1) (uliftYoneda.{u}.map f.2)
        (ULift.up x) (ULift.up y))).trans ?_
    refine (grayTensorBallIso_hom_app_grayTensorCell (x ≫ f.1) (y ≫ f.2)).trans ?_
    refine (congrArg ULift.up (Atom.grayTensorMap_comp x y f.1 f.2).symm).trans ?_
    exact congrArg ((uliftYoneda.{u}.map (Atom.grayTensorMap f.1 f.2)).app _)
      (grayTensorBallIso_hom_app_grayTensorCell x y).symm

end Atoms.Diagrammatic
