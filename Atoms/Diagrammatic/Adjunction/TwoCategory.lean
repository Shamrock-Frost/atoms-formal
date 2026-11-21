import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.CatEnriched
import Atoms.Diagrammatic.Adjunction.HomotopyAdjunction
import Atoms.Diagrammatic.Joyal.GrayTensorModel

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {W X Y Z : DiagSet.{u}}

@[reassoc]
private theorem grayTensorRight_map_comp_associator_hom {A A' : DiagSet.{u}} (f : A ⟶ A')
    (B C : DiagSet.{u}) :
    (grayTensorRight C).map ((grayTensorRight B).map f) ≫ (GrayDiagSet.associator A' B C).hom =
      (GrayDiagSet.associator A B C).hom ≫ (grayTensorRight (grayTensor B C)).map f := by
  have h : grayTensorBifunctor.map ((𝟙 B, 𝟙 C) : (B, C) ⟶ (B, C)) = 𝟙 _ :=
    grayTensorBifunctor.map_id (B, C)
  rw [grayTensorRight_map_eq, grayTensorRight_map_eq, grayTensorRight_map_eq,
    GrayDiagSet.associator_naturality, h]

@[reassoc]
private theorem grayTensorRight_map_grayTensorLeft_map_comp_associator_hom (A : DiagSet.{u})
    {B B' : DiagSet.{u}} (g : B ⟶ B') (C : DiagSet.{u}) :
    (grayTensorRight C).map ((grayTensorLeft A).map g) ≫ (GrayDiagSet.associator A B' C).hom =
      (GrayDiagSet.associator A B C).hom ≫ (grayTensorLeft A).map ((grayTensorRight C).map g) := by
  rw [grayTensorRight_map_eq, grayTensorLeft_map_eq, grayTensorLeft_map_eq, grayTensorRight_map_eq,
    GrayDiagSet.associator_naturality]

@[reassoc]
private theorem associator_hom_comp_grayTensorSnd (A B C : DiagSet.{u}) :
    (GrayDiagSet.associator A B C).hom ≫ grayTensorSnd A (grayTensor B C) =
      (grayTensorRight C).map (grayTensorSnd A B) := by
  let t : GrayDiagSet.toGray.obj A ⟶ MonoidalCategoryStruct.tensorUnit GrayDiagSet.{u} :=
    GrayDiagSet.toGray.map (isTerminalBallAtomPoint.from A)
  have h : (MonoidalCategoryStruct.associator (GrayDiagSet.toGray.obj A)
      (GrayDiagSet.toGray.obj B) (GrayDiagSet.toGray.obj C)).hom ≫
        MonoidalCategoryStruct.whiskerRight t _ ≫ (MonoidalCategoryStruct.leftUnitor _).hom =
      MonoidalCategoryStruct.whiskerRight (MonoidalCategoryStruct.whiskerRight t
        (GrayDiagSet.toGray.obj B) ≫ (MonoidalCategoryStruct.leftUnitor _).hom)
          (GrayDiagSet.toGray.obj C) := by
    rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.leftUnitor_whiskerRight,
      MonoidalCategory.associator_naturality_left_assoc]
  exact h

@[reassoc]
private theorem associator_hom_comp_grayTensorLeft_map_grayTensorSnd (A C : DiagSet.{u}) :
    (GrayDiagSet.associator A (ball.{u} atomPoint) C).hom ≫
        (grayTensorLeft A).map (grayTensorSnd (ball.{u} atomPoint) C) =
      (grayTensorRight C).map (grayTensorFst A (ball.{u} atomPoint)) := by
  have ht : isTerminalBallAtomPoint.from (ball.{u} atomPoint) = 𝟙 _ :=
    isTerminalBallAtomPoint.hom_ext _ _
  have h := MonoidalCategory.triangle (GrayDiagSet.toGray.obj A) (GrayDiagSet.toGray.obj C)
  rw [grayTensorSnd, grayTensorFst, ht, Functor.map_comp, Functor.map_comp]
  have e₁ : grayTensorBifunctor.map
      ((𝟙 (ball.{u} atomPoint), 𝟙 C) : (ball.{u} atomPoint, C) ⟶ (ball.{u} atomPoint, C)) = 𝟙 _ :=
    grayTensorBifunctor.map_id (ball.{u} atomPoint, C)
  have e₂ : grayTensorBifunctor.map
      ((𝟙 A, 𝟙 (ball.{u} atomPoint)) : (A, ball.{u} atomPoint) ⟶ (A, ball.{u} atomPoint)) = 𝟙 _ :=
    grayTensorBifunctor.map_id (A, ball.{u} atomPoint)
  rw [e₁, e₂, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp]
  exact h

private noncomputable def grayEval (X Y : DiagSet.{u}) :
    grayTensor ((grayHomRight X).obj Y) X ⟶ Y :=
  (grayTensorRightAdjunction X).counit.app Y

private theorem homEquiv_symm_eq_grayEval {A : DiagSet.{u}} (g : A ⟶ (grayHomRight X).obj Y) :
    ((grayTensorRightAdjunction X).homEquiv A Y).symm g =
      (grayTensorRight X).map g ≫ grayEval X Y :=
  (grayTensorRightAdjunction X).homEquiv_counit A Y g

private theorem homEquiv_grayEval (X Y : DiagSet.{u}) :
    (grayTensorRightAdjunction X).homEquiv ((grayHomRight X).obj Y) Y (grayEval X Y) = 𝟙 _ :=
  ((grayTensorRightAdjunction X).homEquiv _ _).eq_symm_apply.1
    ((grayTensorRightAdjunction X).homEquiv_symm_id Y).symm

private theorem homEquiv_grayEval_comp (X : DiagSet.{u}) (H : Y ⟶ Z) :
    (grayTensorRightAdjunction X).homEquiv ((grayHomRight X).obj Y) Z (grayEval X Y ≫ H) =
      (grayHomRight X).map H := by
  rw [(grayTensorRightAdjunction X).homEquiv_naturality_right (grayEval X Y) H,
    homEquiv_grayEval, Category.id_comp]

private theorem inv_grayTensorFst_comp_homEquiv_associator_hom (T : DiagSet.{u}) (F : X ⟶ Y)
    (φ : grayTensor T Y ⟶ Z) :
    inv (grayTensorFst T (ball.{u} atomPoint)) ≫
        (grayTensorLeft T).map ((grayTensorRightAdjunction X).homEquiv _ Y
          (grayTensorSnd (ball.{u} atomPoint) X ≫ F)) ≫
        (grayTensorRightAdjunction X).homEquiv (grayTensor T ((grayHomRight X).obj Y)) Z
          ((GrayDiagSet.associator T _ X).hom ≫ (grayTensorLeft T).map (grayEval X Y) ≫ φ) =
      (grayTensorRightAdjunction X).homEquiv T Z ((grayTensorLeft T).map F ≫ φ) := by
  refine ((congrArg (_ ≫ ·) (Adjunction.homEquiv_naturality_left _ _ _).symm).trans
    (Adjunction.homEquiv_naturality_left _ _ _).symm).trans (congrArg _ ?_)
  rw [grayTensorRight_map_grayTensorLeft_map_comp_associator_hom_assoc,
    ← Functor.map_comp_assoc (grayTensorLeft _) ((grayTensorRight X).map _) (grayEval X Y),
    ← homEquiv_symm_eq_grayEval, Equiv.symm_apply_apply,
    Functor.map_comp_assoc, associator_hom_comp_grayTensorLeft_map_grayTensorSnd_assoc,
    ← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

namespace Transformation

variable {H K : Y ⟶ Z}

private noncomputable def postcompAux (X : DiagSet.{u}) (θ : Transformation H K) :
    grayTensor (grayTensor (ball.{u} (atomSimplex 1)) ((grayHomRight X).obj Y)) X ⟶ Z :=
  (GrayDiagSet.associator _ _ X).hom ≫ (grayTensorLeft _).map (grayEval X Y) ≫ θ.toMap

private theorem homEquiv_associator_hom_comp_grayTensorSnd (T : DiagSet.{u}) (M : Y ⟶ Z) :
    (grayTensorRightAdjunction X).homEquiv (grayTensor T ((grayHomRight X).obj Y)) Z
      ((GrayDiagSet.associator T _ X).hom ≫ (grayTensorLeft T).map (grayEval X Y) ≫
        grayTensorSnd T Y ≫ M) =
      grayTensorSnd T ((grayHomRight X).obj Y) ≫ (grayHomRight X).map M := by
  rw [reassoc_of% grayTensorLeft_map_grayTensorSnd, associator_hom_comp_grayTensorSnd_assoc,
    Adjunction.homEquiv_naturality_left, homEquiv_grayEval_comp]

private theorem grayTensorRight_map_comp_homEquiv_postcompAux (X : DiagSet.{u})
    (θ : Transformation H K) {a : ball.{u} atomPoint ⟶ ball.{u} (atomSimplex 1)} {M : Y ⟶ Z}
    (h : (grayTensorRight Y).map a ≫ θ.toMap = grayTensorSnd (ball.{u} atomPoint) Y ≫ M) :
    (grayTensorRight ((grayHomRight X).obj Y)).map a ≫
        (grayTensorRightAdjunction X).homEquiv _ Z (postcompAux X θ) =
      grayTensorSnd (ball.{u} atomPoint) ((grayHomRight X).obj Y) ≫ (grayHomRight X).map M := by
  rw [← Adjunction.homEquiv_naturality_left, postcompAux,
    grayTensorRight_map_comp_associator_hom_assoc,
    ← reassoc_of% grayTensorLeft_map_comp_grayTensorRight_map a (grayEval X Y), h]
  exact homEquiv_associator_hom_comp_grayTensorSnd _ M

noncomputable def postcomp (X : DiagSet.{u}) (θ : Transformation H K) :
    Transformation ((grayHomRight X).map H) ((grayHomRight X).map K) :=
  ofMap ((grayTensorRightAdjunction X).homEquiv _ Z (postcompAux X θ))
    (grayTensorRight_map_comp_homEquiv_postcompAux X θ θ.source_toMap)
    (grayTensorRight_map_comp_homEquiv_postcompAux X θ θ.target_toMap)

private theorem toMap_postcomp (X : DiagSet.{u}) (θ : Transformation H K) :
    (θ.postcomp X).toMap = (grayTensorRightAdjunction X).homEquiv _ Z (postcompAux X θ) :=
  toMap_ofMap _ _ _

theorem cell_app_postcomp (X : DiagSet.{u}) (θ : Transformation H K) (F : X ⟶ Y) :
    ((θ.postcomp X).app (diagramVertex F)).cell =
      (θ.whiskerLeft F).cell := by
  refine cell_eq_of_edgeHom_eq _ _ ?_
  rw [edgeHom_app, edgeHom_eq, toMap_postcomp,
    vertexHom_diagramVertex, postcompAux, toMap_whiskerLeft]
  exact inv_grayTensorFst_comp_homEquiv_associator_hom _ F θ.toMap

theorem homMk_app_postcomp (X : DiagSet.{u}) {H K : Y ⟶ Z}
    (θ : Transformation H K) (F : X ⟶ Y) :
    OneTruncation.globeHomMk ((θ.postcomp X).app (diagramVertex F)) =
      eqToHom (congrArg OneTruncation.mk (grayHomRight_map_app_diagramVertex F H)) ≫
        OneTruncation.globeHomMk (θ.whiskerLeft F) ≫
          eqToHom (congrArg OneTruncation.mk (grayHomRight_map_app_diagramVertex F K)).symm := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1
    (OneTruncation.arrowMk_globeHomMk_eq _ _ (cell_app_postcomp X θ F))
  exact h

theorem postcomp_refl (X : DiagSet.{u}) (H : Y ⟶ Z) :
    (Transformation.refl H).postcomp X = Transformation.refl ((grayHomRight X).map H) :=
  ext (by rw [toMap_postcomp, toMap_refl, postcompAux, toMap_refl,
    homEquiv_associator_hom_comp_grayTensorSnd])

theorem interchange {F G : X ⟶ Y} {H K : Y ⟶ Z} (η : Transformation F G)
    (θ : Transformation H K) :
    OneTruncation.globeHomMk (η.whiskerRight H) ≫ OneTruncation.globeHomMk (θ.whiskerLeft G) =
      OneTruncation.globeHomMk (θ.whiskerLeft F) ≫ OneTruncation.globeHomMk (η.whiskerRight K) :=
  (Arrow.mk_inj _ _).1 ((Arrow.mk_comp_eq_mk_comp
    (OneTruncation.arrowMk_globeHomMk_eq (η.whiskerRight H)
      (η.map ((grayHomRight X).map H)) (η.cell_whiskerRight H))
    (OneTruncation.arrowMk_globeHomMk_eq (θ.whiskerLeft G) ((θ.postcomp X).app _)
      (cell_app_postcomp X θ G).symm)).trans
    ((congrArg Arrow.mk ((θ.postcomp X).naturality η)).trans (Arrow.mk_comp_eq_mk_comp
      (OneTruncation.arrowMk_globeHomMk_eq ((θ.postcomp X).app _) (θ.whiskerLeft F)
        (cell_app_postcomp X θ F))
      (OneTruncation.arrowMk_globeHomMk_eq (η.map ((grayHomRight X).map K))
        (η.whiskerRight K) (η.cell_whiskerRight K).symm))))

private theorem toMap_cast {F G F' G' : X ⟶ Y} (hF : F = F') (hG : G = G')
    (h : Transformation F G = Transformation F' G') (η : Transformation F G) :
    (cast h η).toMap = η.toMap := by
  subst hF hG
  rfl

theorem whiskerLeft_whiskerLeft (J : W ⟶ X) (K : X ⟶ Y) {F G : Y ⟶ Z}
    (η : Transformation F G) :
    (η.whiskerLeft K).whiskerLeft J = cast (by simp) (η.whiskerLeft (J ≫ K)) :=
  ext (by rw [toMap_cast (Category.assoc _ _ _) (Category.assoc _ _ _), toMap_whiskerLeft,
    toMap_whiskerLeft, toMap_whiskerLeft, Functor.map_comp_assoc])

theorem whiskerRight_whiskerRight {F G : W ⟶ X} (η : Transformation F G)
    (H : X ⟶ Y) (K : Y ⟶ Z) :
    (η.whiskerRight H).whiskerRight K = cast (by simp) (η.whiskerRight (H ≫ K)) :=
  ext (by rw [toMap_cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm,
    toMap_whiskerRight, toMap_whiskerRight, toMap_whiskerRight, Category.assoc])

theorem whiskerRight_whiskerLeft (J : W ⟶ X) {F G : X ⟶ Y}
    (η : Transformation F G) (H : Y ⟶ Z) :
    (η.whiskerLeft J).whiskerRight H = cast (by simp) ((η.whiskerRight H).whiskerLeft J) :=
  ext (by rw [toMap_cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm,
    toMap_whiskerRight, toMap_whiskerLeft, toMap_whiskerLeft, toMap_whiskerRight, Category.assoc])

end Transformation

private noncomputable def compAux (X Y Z : DiagSet.{u}) :
    grayTensor (grayTensor ((grayHomRight Y).obj Z) ((grayHomRight X).obj Y)) X ⟶ Z :=
  (GrayDiagSet.associator _ _ X).hom ≫ (grayTensorLeft _).map (grayEval X Y) ≫ grayEval Y Z

private theorem grayTensorRight_map_comp_homEquiv_compAux {T : DiagSet.{u}}
    (t : T ⟶ (grayHomRight Y).obj Z) :
    (grayTensorRight ((grayHomRight X).obj Y)).map t ≫
        (grayTensorRightAdjunction X).homEquiv _ Z (compAux X Y Z) =
      (grayTensorRightAdjunction X).homEquiv _ Z ((GrayDiagSet.associator T _ X).hom ≫
        (grayTensorLeft T).map (grayEval X Y) ≫
          ((grayTensorRightAdjunction Y).homEquiv T Z).symm t) := by
  rw [← Adjunction.homEquiv_naturality_left, compAux, grayTensorRight_map_comp_associator_hom_assoc,
    ← reassoc_of% grayTensorLeft_map_comp_grayTensorRight_map t (grayEval X Y),
    homEquiv_symm_eq_grayEval]
  rfl

noncomputable def grayHomPostcomp (X Y Z : DiagSet.{u}) :
    (grayHomRight Y).obj Z ⟶
      (grayHomRight ((grayHomRight X).obj Y)).obj ((grayHomRight X).obj Z) :=
  (grayTensorRightAdjunction _).homEquiv _ _ ((grayTensorRightAdjunction X).homEquiv _ Z
    (compAux X Y Z))

theorem grayHomPostcomp_app_diagramVertex (H : Y ⟶ Z) :
    (diagramVertex H).map (grayHomPostcomp X Y Z) =
      diagramVertex ((grayHomRight X).map H) := by
  refine vertexHom_injective
    ((vertexHom_comp (diagramVertex H) (grayHomPostcomp X Y Z)).symm.trans ?_)
  rw [vertexHom_diagramVertex, vertexHom_diagramVertex, grayHomPostcomp,
    ← Adjunction.homEquiv_naturality_left, grayTensorRight_map_comp_homEquiv_compAux,
    Equiv.symm_apply_apply]
  exact congrArg _ (Transformation.homEquiv_associator_hom_comp_grayTensorSnd _ H)

noncomputable def homComp (X Y Z : DiagSet.{u}) :
    OneTruncation ((grayHomRight X).obj Y) × OneTruncation ((grayHomRight Y).obj Z) ⥤
      OneTruncation ((grayHomRight X).obj Z) :=
  Functor.uncurry.obj ((oneTruncation.map (grayHomPostcomp X Y Z)).toFunctor ⋙
    homFunctor _ _).flip

theorem homComp_obj_mk (F : X ⟶ Y) (H : Y ⟶ Z) :
    (homComp X Y Z).obj (OneTruncation.mk (diagramVertex F),
        OneTruncation.mk (diagramVertex H)) =
      OneTruncation.mk (X := (grayHomRight X).obj Z) (diagramVertex (F ≫ H)) :=
  (congrArg (fun G => G.obj (OneTruncation.mk (diagramVertex F)))
    ((congrArg (homFunctor _ _).obj
      (congrArg OneTruncation.mk (grayHomPostcomp_app_diagramVertex H))).trans
        (homFunctor_obj_mk ((grayHomRight X).map H)))).trans
    (congrArg OneTruncation.mk (grayHomRight_map_app_diagramVertex F H))

theorem grayHomPostcomp_comp_grayHomEval (F : X ⟶ Y) (Z : DiagSet.{u}) :
    grayHomPostcomp X Y Z ≫ grayHomEval (diagramVertex F) _ =
      (grayHomRestrict F).app Z := by
  have hv : vertexHom (X := (grayHomRight X).obj Y)
      (diagramVertex F) = (grayTensorRightAdjunction X).homEquiv _ Y
        (grayTensorSnd (ball.{u} atomPoint) X ≫ F) := vertexHom_diagramVertex F
  rw [grayHomPostcomp, homEquiv_comp_grayHomEval, hv, compAux]
  refine (inv_grayTensorFst_comp_homEquiv_associator_hom _ F _).trans ?_
  rw [← homEquiv_comp_grayHomRestrict, homEquiv_grayEval, Category.id_comp]

section Products

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

private theorem arrowMk_natTrans_eq {P Q P' Q' : A ⥤ B} (α : P ⟶ Q) (β : P' ⟶ Q')
    (hP : P = P') (hQ : Q = Q') (h : ∀ a, Arrow.mk (α.app a) = Arrow.mk (β.app a)) :
    Arrow.mk α = Arrow.mk β := by
  subst hP hQ
  exact congrArg Arrow.mk (NatTrans.ext (funext fun a => (Arrow.mk_inj _ _).1 (h a)))

private theorem sectL_comp_prod_id (Φ : B ⥤ C) (b : B) :
    Prod.sectL A b ⋙ (𝟭 A).prod Φ = Prod.sectL A (Φ.obj b) :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq (Prod.ext rfl (Φ.map_id b))

private theorem sectR_comp_prod_id (Φ : A ⥤ C) (a : A) :
    Prod.sectR a B ⋙ Φ.prod (𝟭 B) = Prod.sectR (Φ.obj a) B :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq (Prod.ext (Φ.map_id a) rfl)

end Products

private theorem prod_functor_ext {E D : Type*} [Category* E] [Category* D]
    {F₁ F₂ : OneTruncation X × E ⥤ D}
    (hL : ∀ e, Prod.sectL _ e ⋙ F₁ = Prod.sectL _ e ⋙ F₂)
    (hR : ∀ a, Prod.sectR a E ⋙ F₁ = Prod.sectR a E ⋙ F₂) : F₁ = F₂ := by
  have hc : Functor.curry.obj F₁ = Functor.curry.obj F₂ :=
    OneTruncation.functor_ext fun _ _ f => arrowMk_natTrans_eq _ _ (hR _) (hR _) fun e =>
      congrArg (fun H => Arrow.mk (H.map (OneTruncation.homMk f))) (hL e)
  rw [← Functor.uncurry_obj_curry_obj F₁, hc, Functor.uncurry_obj_curry_obj]

section Currying

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]

private theorem sectL_comp_uncurry_flip (G : B ⥤ A ⥤ C) (b : B) :
    Prod.sectL A b ⋙ Functor.uncurry.obj G.flip = G.obj b :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq ((Functor.uncurry_obj_map _ _).trans
    ((congrArg (_ ≫ ·) (congrArg (fun φ => NatTrans.app φ _) (G.map_id b))).trans
      (Category.comp_id _)))

private theorem sectR_comp_uncurry_flip (G : B ⥤ A ⥤ C) (a : A) :
    Prod.sectR a B ⋙ Functor.uncurry.obj G.flip = G ⋙ (evaluation A C).obj a :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq ((Functor.uncurry_obj_map _ _).trans
    ((congrArg (· ≫ _) ((G.obj _).map_id a)).trans (Category.id_comp _)))

end Currying

private noncomputable def truncMap {A B : DiagSet.{u}} (f : A ⟶ B) :
    OneTruncation A ⥤ OneTruncation B :=
  (oneTruncation.map f).toFunctor

private theorem truncMap_comp {A B C : DiagSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    truncMap f ⋙ truncMap g = truncMap (f ≫ g) :=
  congrArg Cat.Hom.toFunctor (oneTruncation.map_comp f g).symm

private theorem truncMap_id (A : DiagSet.{u}) : truncMap (𝟙 A) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (oneTruncation.map_id A)

private theorem sectL_comp_homComp (H : Y ⟶ Z) :
    Prod.sectL _ (OneTruncation.mk (X := (grayHomRight Y).obj Z) (diagramVertex H)) ⋙
        homComp X Y Z =
      truncMap ((grayHomRight X).map H) := by
  refine (sectL_comp_uncurry_flip
    ((oneTruncation.map (grayHomPostcomp X Y Z)).toFunctor ⋙ homFunctor _ _) _).trans ?_
  exact (Functor.comp_obj _ _ _).trans
    ((congrArg (homFunctor _ _).obj
      (oneTruncation_map_obj_mk (grayHomPostcomp X Y Z) (diagramVertex H))).trans
        ((congrArg (homFunctor _ _).obj (congrArg OneTruncation.mk
          (grayHomPostcomp_app_diagramVertex H))).trans (homFunctor_obj_mk _)))

private theorem sectR_comp_homComp (F : X ⟶ Y) (Z : DiagSet.{u}) :
    Prod.sectR (OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex F)) _ ⋙
        homComp X Y Z =
      truncMap ((grayHomRestrict F).app Z) :=
  (sectR_comp_uncurry_flip
    ((oneTruncation.map (grayHomPostcomp X Y Z)).toFunctor ⋙ homFunctor _ _) _).trans
      ((CategoryTheory.Functor.assoc _ _ _).trans
      ((congrArg ((oneTruncation.map (grayHomPostcomp X Y Z)).toFunctor ⋙ ·)
        (homFunctor_comp_evaluation _ _ _)).trans ((truncMap_comp _ _).trans
          (congrArg truncMap (grayHomPostcomp_comp_grayHomEval F Z)))))

private theorem exists_eq_mk_diagramVertex (p : OneTruncation ((grayHomRight X).obj Y)) :
    ∃ F : X ⟶ Y, p = OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex F) := by
  obtain ⟨⟨x⟩⟩ := p
  exact ⟨(diagramVertexEquiv X Y).symm x,
    congrArg OneTruncation.mk ((diagramVertexEquiv X Y).apply_symm_apply x).symm⟩

def HoTwo : Type (u + 1) := DiagSet.{u}

open MonoidalCategory in
private noncomputable def homId (X : DiagSet.{u}) :
    𝟙_ Cat.{u, u} ⟶ Cat.of (OneTruncation ((grayHomRight X).obj X)) :=
  Cat.Hom.ofFunctor ((Functor.const (𝟙_ Cat.{u, u})).obj
    (OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (𝟙 X)))))

private theorem homComp_id_comp (X Y : DiagSet.{u}) :
    Prod.sectR (OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (𝟙 X)))) _ ⋙
      homComp X X Y = 𝟭 _ :=
  (sectR_comp_homComp (𝟙 X) Y).trans (by rw [grayHomRestrict_id, NatTrans.id_app, truncMap_id])

private theorem homComp_comp_id (X Y : DiagSet.{u}) :
    Prod.sectL _ (OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (𝟙 Y)))) ⋙
      homComp X Y Y = 𝟭 _ :=
  (sectL_comp_homComp (𝟙 Y)).trans (by rw [CategoryTheory.Functor.map_id, truncMap_id])

private theorem homComp_assoc (W X Y Z : DiagSet.{u}) :
    Functor.prod' (Functor.prod' (CategoryTheory.Prod.fst _ _)
        (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _))
          (CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _) ⋙
            (homComp W X Y).prod (𝟭 _) ⋙ homComp W Y Z =
      (𝟭 _).prod (homComp X Y Z) ⋙ homComp W X Z := by
  refine prod_functor_ext (fun bc => ?_) fun a => ?_
  · obtain ⟨b, c⟩ := bc
    obtain ⟨G, rfl⟩ := exists_eq_mk_diagramVertex b
    obtain ⟨H, rfl⟩ := exists_eq_mk_diagramVertex c
    calc _ = (Prod.sectL _ (OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex G)) ⋙
          homComp W X Y) ⋙ (Prod.sectL _ (OneTruncation.mk (X := (grayHomRight Y).obj Z)
              (diagramVertex H)) ⋙ homComp W Y Z) := rfl
      _ = truncMap ((grayHomRight W).map (G ≫ H)) := by
        rw [sectL_comp_homComp, sectL_comp_homComp, truncMap_comp,
          Functor.map_comp]
      _ = Prod.sectL _ ((homComp _ _ _).obj
          (OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex G),
            OneTruncation.mk (X := (grayHomRight Y).obj Z) (diagramVertex H))) ⋙
              homComp W X Z := by
        rw [homComp_obj_mk, sectL_comp_homComp]
      _ = _ := congrArg (· ⋙ homComp W X Z) (sectL_comp_prod_id _ _).symm
  · obtain ⟨F, rfl⟩ := exists_eq_mk_diagramVertex a
    refine prod_functor_ext (fun c => ?_) fun b => ?_
    · obtain ⟨H, rfl⟩ := exists_eq_mk_diagramVertex c
      calc _ = (Prod.sectR (OneTruncation.mk (X := (grayHomRight W).obj X) (diagramVertex F)) _ ⋙
            homComp W X Y) ⋙ (Prod.sectL _ (OneTruncation.mk (X := (grayHomRight Y).obj Z)
                (diagramVertex H)) ⋙ homComp W Y Z) := rfl
        _ = (Prod.sectL _ (OneTruncation.mk (X := (grayHomRight Y).obj Z) (diagramVertex H)) ⋙
            homComp X Y Z) ⋙ (Prod.sectR (OneTruncation.mk (X := (grayHomRight W).obj X)
                (diagramVertex F)) _ ⋙ homComp W X Z) := by
          rw [sectL_comp_homComp, sectL_comp_homComp, sectR_comp_homComp, sectR_comp_homComp,
            truncMap_comp, truncMap_comp,
            NatTrans.naturality]
        _ = _ := rfl
    · obtain ⟨G, rfl⟩ := exists_eq_mk_diagramVertex b
      calc _ = Prod.sectR ((homComp _ _ _).obj
            (OneTruncation.mk (X := (grayHomRight W).obj X) (diagramVertex F),
              OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex G))) _ ⋙
                homComp W Y Z := congrArg (· ⋙ homComp W Y Z) (sectR_comp_prod_id _ _)
        _ = (Prod.sectR (OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex G)) _ ⋙
            homComp X Y Z) ⋙ (Prod.sectR (OneTruncation.mk (X := (grayHomRight W).obj X)
                (diagramVertex F)) _ ⋙ homComp W X Z) := by
          rw [homComp_obj_mk, sectR_comp_homComp, sectR_comp_homComp, sectR_comp_homComp,
            truncMap_comp, ← NatTrans.comp_app, ← grayHomRestrict_comp]
        _ = _ := rfl

noncomputable instance : EnrichedCategory Cat.{u, u} HoTwo.{u} where
  Hom X Y := Cat.of (OneTruncation ((grayHomRight (X : DiagSet.{u})).obj Y))
  id X := homId X
  comp X Y Z := (homComp X Y Z).toCatHom
  id_comp X Y := Cat.Hom.ext (homComp_id_comp X Y)
  comp_id X Y := Cat.Hom.ext (homComp_comp_id X Y)
  assoc W X Y Z := Cat.Hom.ext (homComp_assoc W X Y Z)

def HoTwo.of (X : DiagSet.{u}) : CatEnriched HoTwo.{u} := X

theorem HoTwo.eHom_eq (X Y : HoTwo.{u}) :
    (X ⟶[Cat.{u, u}] Y) = Cat.of (OneTruncation ((grayHomRight (X : DiagSet.{u})).obj Y)) :=
  rfl

noncomputable def HoTwo.homOfMap {X Y : DiagSet.{u}} (F : X ⟶ Y) : HoTwo.of X ⟶ HoTwo.of Y :=
  OneTruncation.mk (diagramVertex F)

private theorem HoTwo.eComp_toFunctor (W X Y : DiagSet.{u}) :
    (eComp Cat.{u, u} (HoTwo.of W) (HoTwo.of X) (HoTwo.of Y)).toFunctor = homComp W X Y :=
  (congrArg Cat.Hom.toFunctor (rfl : eComp Cat.{u, u} (HoTwo.of W) (HoTwo.of X) (HoTwo.of Y) =
    (homComp W X Y).toCatHom)).trans (Functor.toCatHom_toFunctor _)

theorem HoTwo.homOfMap_comp (F : X ⟶ Y) (G : Y ⟶ Z) :
    HoTwo.homOfMap (F ≫ G) = HoTwo.homOfMap F ≫ HoTwo.homOfMap G :=
  ((CatEnriched.comp_eq _ _).trans ((congrArg (fun E => E.obj (HoTwo.homOfMap F, HoTwo.homOfMap G))
    (HoTwo.eComp_toFunctor X Y Z)).trans (homComp_obj_mk F G))).symm

theorem HoTwo.homOfMap_id (X : DiagSet.{u}) : HoTwo.homOfMap (𝟙 X) = 𝟙 (HoTwo.of X) :=
  rfl

noncomputable def HoTwo.twoCellOfTransformation {F G : X ⟶ Y} (η : Transformation F G) :
    HoTwo.homOfMap F ⟶ HoTwo.homOfMap G :=
  OneTruncation.globeHomMk η

private theorem HoTwo.whiskerLeft_eq_map {a b c : CatEnriched HoTwo.{u}} (f : a ⟶ b)
    {g g' : b ⟶ c} (θ : g ⟶ g') :
    Bicategory.whiskerLeft f θ = (Prod.sectR f _ ⋙ (eComp Cat a b c).toFunctor).map θ :=
  rfl

private theorem HoTwo.whiskerRight_eq_map {a b c : CatEnriched HoTwo.{u}} {f f' : a ⟶ b}
    (θ : f ⟶ f') (g : b ⟶ c) :
    Bicategory.whiskerRight θ g = (Prod.sectL _ g ⋙ (eComp Cat a b c).toFunctor).map θ :=
  rfl

theorem HoTwo.whiskerLeft_twoCellOfTransformation (K : W ⟶ X) {F G : X ⟶ Y}
    (η : Transformation F G) :
    Bicategory.whiskerLeft (HoTwo.homOfMap K) (HoTwo.twoCellOfTransformation η) =
      eqToHom (by simp [HoTwo.homOfMap_comp]) ≫
        HoTwo.twoCellOfTransformation (η.whiskerLeft K) ≫
          eqToHom (by simp [HoTwo.homOfMap_comp]) := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1
    ((congrArg Arrow.mk (HoTwo.whiskerLeft_eq_map (HoTwo.homOfMap K)
      (HoTwo.twoCellOfTransformation η))).trans
      ((congrArg (fun E => Arrow.mk ((Prod.sectR (HoTwo.homOfMap K) _ ⋙ E).map
        (HoTwo.twoCellOfTransformation η))) (HoTwo.eComp_toFunctor W X Y)).trans
      ((congrArg (fun Φ => Arrow.mk (Φ.map (OneTruncation.globeHomMk η)))
        (sectR_comp_homComp K Y)).trans
      ((congrArg Arrow.mk (globeHomMk_whiskerLeft K η)).trans
        ((Arrow.arrow_mk_eqToHom_comp _ _).trans (Arrow.arrow_mk_comp_eqToHom _ _))).symm)))
  exact h

theorem HoTwo.whiskerRight_twoCellOfTransformation {F G : X ⟶ Y} (η : Transformation F G)
    (H : Y ⟶ Z) :
    Bicategory.whiskerRight (HoTwo.twoCellOfTransformation η) (HoTwo.homOfMap H) =
      eqToHom (by simp [HoTwo.homOfMap_comp]) ≫
        HoTwo.twoCellOfTransformation (η.whiskerRight H) ≫
          eqToHom (by simp [HoTwo.homOfMap_comp]) := by
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).1
    ((congrArg Arrow.mk (HoTwo.whiskerRight_eq_map (HoTwo.twoCellOfTransformation η)
      (HoTwo.homOfMap H))).trans
      ((congrArg (fun E => Arrow.mk ((Prod.sectL _ (HoTwo.homOfMap H) ⋙ E).map
        (HoTwo.twoCellOfTransformation η))) (HoTwo.eComp_toFunctor X Y Z)).trans
      ((congrArg (fun Φ => Arrow.mk (Φ.map (OneTruncation.globeHomMk η)))
        (sectL_comp_homComp H)).trans
      ((congrArg Arrow.mk (globeHomMk_whiskerRight η H)).trans
        ((Arrow.arrow_mk_eqToHom_comp _ _).trans (Arrow.arrow_mk_comp_eqToHom _ _))).symm)))
  exact h

private theorem exists_homMk_eq {S : DiagSet.{u}} (hS : IsInftyCategory 1 S)
    {x y : S.Vertex} (φ : OneTruncation.mk x ⟶ OneTruncation.mk y) :
    ∃ e : S.Edge x y, OneTruncation.globeHomMk e = φ := by
  have := isEquivalence_toHomotopyCategory hS
  obtain ⟨e, he⟩ := HomotopyCategory.homMk_surjective hS.1
    ((OneTruncation.toHomotopyCategory hS).map φ)
  exact ⟨e, (OneTruncation.toHomotopyCategory hS).map_injective
    ((OneTruncation.toHomotopyCategory_map_globeHomMk hS e).trans he)⟩

private theorem eqToHom_comp_comp_eqToHom_eq_iff {C : Type*} [Category* C] {x x' a b b' c y : C}
    (p : a ⟶ b) (q : b' ⟶ c) (h₁ : x = a) (h₂ : b = b') (h₃ : c = x) (k₁ : x' = a) (k₃ : c = y)
    (k : x' = y) :
    eqToHom k₁ ≫ p ≫ eqToHom h₂ ≫ q ≫ eqToHom k₃ = eqToHom k ↔
      eqToHom h₁ ≫ p ≫ eqToHom h₂ ≫ q ≫ eqToHom h₃ = 𝟙 x := by
  cases h₁; cases h₃; cases k₁; cases k₃
  simp

theorem HoTwo.exists_twoCellOfTransformation_eq (hY : IsInftyCategory 1 Y) {F G : X ⟶ Y}
    (φ : HoTwo.homOfMap F ⟶ HoTwo.homOfMap G) :
    ∃ η : Transformation F G, HoTwo.twoCellOfTransformation η = φ :=
  exists_homMk_eq (isInftyCategory_grayHomRight X hY) φ

namespace HomotopyAdjunction

variable {F : X ⟶ Y} {G : Y ⟶ X}

private noncomputable def unitCell (η : Transformation (𝟙 X) (F ≫ G)) :
    𝟙 (HoTwo.of X) ⟶ HoTwo.homOfMap F ≫ HoTwo.homOfMap G :=
  eqToHom (HoTwo.homOfMap_id X).symm ≫ HoTwo.twoCellOfTransformation η ≫
    eqToHom (HoTwo.homOfMap_comp F G)

private noncomputable def counitCell (ε : Transformation (G ≫ F) (𝟙 Y)) :
    HoTwo.homOfMap G ≫ HoTwo.homOfMap F ⟶ 𝟙 (HoTwo.of Y) :=
  eqToHom (HoTwo.homOfMap_comp G F).symm ≫ HoTwo.twoCellOfTransformation ε ≫
    eqToHom (HoTwo.homOfMap_id Y)

open Bicategory in
private theorem leftZigzag_unitCell_counitCell_iff (η : Transformation (𝟙 X) (F ≫ G))
    (ε : Transformation (G ≫ F) (𝟙 Y)) :
    Bicategory.leftZigzag (unitCell η) (counitCell ε) = (λ_ _).hom ≫ (ρ_ _).inv ↔
      eqToHom (by simp) ≫ HoTwo.twoCellOfTransformation (η.whiskerRight F) ≫ eqToHom (by simp) ≫
        HoTwo.twoCellOfTransformation (ε.whiskerLeft F) ≫ eqToHom (by simp) =
          𝟙 (HoTwo.homOfMap F) := by
  simp only [unitCell, counitCell, Bicategory.leftZigzag, bicategoricalComp,
    Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp, Bicategory.eqToHom_whiskerRight,
    Bicategory.whiskerLeft_eqToHom, HoTwo.whiskerRight_twoCellOfTransformation,
    HoTwo.whiskerLeft_twoCellOfTransformation, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.refl_iso, BicategoricalCoherence.whiskerRight_iso, Iso.trans_hom,
    Iso.refl_hom, Bicategory.whiskerRightIso_hom, Bicategory.id_whiskerRight, Category.comp_id,
    Bicategory.Strict.associator_eqToIso, Bicategory.Strict.leftUnitor_eqToIso,
    Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc]
  exact eqToHom_comp_comp_eqToHom_eq_iff _ _ _ _ _ _ _ _

open Bicategory in
private theorem rightZigzag_unitCell_counitCell_iff (η : Transformation (𝟙 X) (F ≫ G))
    (ε : Transformation (G ≫ F) (𝟙 Y)) :
    Bicategory.rightZigzag (unitCell η) (counitCell ε) = (ρ_ _).hom ≫ (λ_ _).inv ↔
      eqToHom (by simp) ≫ HoTwo.twoCellOfTransformation (η.whiskerLeft G) ≫ eqToHom (by simp) ≫
        HoTwo.twoCellOfTransformation (ε.whiskerRight G) ≫ eqToHom (by simp) =
          𝟙 (HoTwo.homOfMap G) := by
  simp only [unitCell, counitCell, Bicategory.rightZigzag, bicategoricalComp,
    Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp, Bicategory.eqToHom_whiskerRight,
    Bicategory.whiskerLeft_eqToHom, HoTwo.whiskerRight_twoCellOfTransformation,
    HoTwo.whiskerLeft_twoCellOfTransformation, BicategoricalCoherence.assoc'_iso,
    BicategoricalCoherence.refl_iso, BicategoricalCoherence.whiskerRight_iso, Iso.trans_hom,
    Iso.symm_hom, Iso.refl_hom, Bicategory.whiskerRightIso_hom, Bicategory.id_whiskerRight,
    Category.id_comp, Bicategory.Strict.associator_eqToIso, Bicategory.Strict.leftUnitor_eqToIso,
    Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc]
  exact eqToHom_comp_comp_eqToHom_eq_iff _ _ _ _ _ _ _ _

noncomputable def toBicategory (a : HomotopyAdjunction F G) :
    Bicategory.Adjunction (HoTwo.homOfMap F) (HoTwo.homOfMap G) where
  unit := unitCell a.unit
  counit := counitCell a.counit
  left_triangle := (leftZigzag_unitCell_counitCell_iff _ _).2 a.left_triangle
  right_triangle := (rightZigzag_unitCell_counitCell_iff _ _).2 a.right_triangle

private theorem exists_unitCell_eq (hX : IsInftyCategory 1 X)
    (θ : 𝟙 (HoTwo.of X) ⟶ HoTwo.homOfMap F ≫ HoTwo.homOfMap G) :
    ∃ η : Transformation (𝟙 X) (F ≫ G), unitCell η = θ := by
  obtain ⟨η, hη⟩ := HoTwo.exists_twoCellOfTransformation_eq hX
    (eqToHom (HoTwo.homOfMap_id X) ≫ θ ≫ eqToHom (HoTwo.homOfMap_comp F G).symm)
  exact ⟨η, by simp [unitCell, hη]⟩

private theorem exists_counitCell_eq (hY : IsInftyCategory 1 Y)
    (θ : HoTwo.homOfMap G ≫ HoTwo.homOfMap F ⟶ 𝟙 (HoTwo.of Y)) :
    ∃ ε : Transformation (G ≫ F) (𝟙 Y), counitCell ε = θ := by
  obtain ⟨ε, hε⟩ := HoTwo.exists_twoCellOfTransformation_eq hY
    (eqToHom (HoTwo.homOfMap_comp G F) ≫ θ ≫ eqToHom (HoTwo.homOfMap_id Y).symm)
  exact ⟨ε, by simp [counitCell, hε]⟩

noncomputable def ofBicategory (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (adj : Bicategory.Adjunction (HoTwo.homOfMap F) (HoTwo.homOfMap G)) :
    HomotopyAdjunction F G where
  unit := (exists_unitCell_eq hX adj.unit).choose
  counit := (exists_counitCell_eq hY adj.counit).choose
  left_triangle := (leftZigzag_unitCell_counitCell_iff _ _).1 (by
    rw [(exists_unitCell_eq hX adj.unit).choose_spec,
      (exists_counitCell_eq hY adj.counit).choose_spec]
    exact adj.left_triangle)
  right_triangle := (rightZigzag_unitCell_counitCell_iff _ _).1 (by
    rw [(exists_unitCell_eq hX adj.unit).choose_spec,
      (exists_counitCell_eq hY adj.counit).choose_spec]
    exact adj.right_triangle)

private theorem unitCell_ofBicategory_unit (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (adj : Bicategory.Adjunction (HoTwo.homOfMap F) (HoTwo.homOfMap G)) :
    unitCell (ofBicategory hX hY adj).unit = adj.unit :=
  (exists_unitCell_eq hX adj.unit).choose_spec

private theorem counitCell_ofBicategory_counit (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (adj : Bicategory.Adjunction (HoTwo.homOfMap F) (HoTwo.homOfMap G)) :
    counitCell (ofBicategory hX hY adj).counit = adj.counit :=
  (exists_counitCell_eq hY adj.counit).choose_spec

private theorem isIso_homMk_of_isIso_unitCell (η : Transformation (𝟙 X) (F ≫ G))
    [IsIso (unitCell η)] : IsIso (OneTruncation.globeHomMk η) := by
  have h : HoTwo.twoCellOfTransformation η =
      eqToHom (HoTwo.homOfMap_id X) ≫ unitCell η ≫ eqToHom (HoTwo.homOfMap_comp F G).symm := by
    simp [unitCell]
  exact (h ▸ inferInstance : IsIso (HoTwo.twoCellOfTransformation η))

private theorem isIso_homMk_of_isIso_counitCell (ε : Transformation (G ≫ F) (𝟙 Y))
    [IsIso (counitCell ε)] : IsIso (OneTruncation.globeHomMk ε) := by
  have h : HoTwo.twoCellOfTransformation ε =
      eqToHom (HoTwo.homOfMap_comp G F) ≫ counitCell ε ≫ eqToHom (HoTwo.homOfMap_id Y).symm := by
    simp [counitCell]
  exact (h ▸ inferInstance : IsIso (HoTwo.twoCellOfTransformation ε))

noncomputable def compOfIsInftyCategory (hX : IsInftyCategory 1 X) (hZ : IsInftyCategory 1 Z)
    {F' : Y ⟶ Z} {G' : Z ⟶ Y} (a : HomotopyAdjunction F G) (b : HomotopyAdjunction F' G') :
    HomotopyAdjunction (F ≫ F') (G' ≫ G) :=
  ofBicategory hX hZ ((HoTwo.homOfMap_comp F F').symm ▸ (HoTwo.homOfMap_comp G' G).symm ▸
    a.toBicategory.comp b.toBicategory)

end HomotopyAdjunction

def IsHomotopyEquivalence (F : X ⟶ Y) : Prop :=
  ∃ G : Y ⟶ X,
    Nonempty (OneTruncation.mk (X := (grayHomRight X).obj X) (diagramVertex (𝟙 X)) ≅
      OneTruncation.mk (X := (grayHomRight X).obj X) (diagramVertex (F ≫ G))) ∧
    Nonempty (OneTruncation.mk (X := (grayHomRight Y).obj Y) (diagramVertex (G ≫ F)) ≅
      OneTruncation.mk (X := (grayHomRight Y).obj Y) (diagramVertex (𝟙 Y)))

namespace IsHomotopyEquivalence

private noncomputable def unitIso {F : X ⟶ Y} {G : Y ⟶ X}
    (i : OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (𝟙 X))) ≅
      OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (F ≫ G)))) :
    𝟙 (HoTwo.of X) ≅ HoTwo.homOfMap F ≫ HoTwo.homOfMap G :=
  i ≪≫ eqToIso (HoTwo.homOfMap_comp F G)

private noncomputable def counitIso {F : X ⟶ Y} {G : Y ⟶ X}
    (j : OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (G ≫ F))) ≅
      OneTruncation.mk (DiagSet.vertexEquivSSet _ (diagramVertex (𝟙 Y)))) :
    HoTwo.homOfMap G ≫ HoTwo.homOfMap F ≅ 𝟙 (HoTwo.of Y) :=
  eqToIso (HoTwo.homOfMap_comp G F).symm ≪≫ j

theorem comp {F : X ⟶ Y} {H : Y ⟶ Z} (hF : IsHomotopyEquivalence F)
    (hH : IsHomotopyEquivalence H) : IsHomotopyEquivalence (F ≫ H) := by
  obtain ⟨G, ⟨i⟩, ⟨j⟩⟩ := hF
  obtain ⟨K, ⟨i'⟩, ⟨j'⟩⟩ := hH
  refine ⟨K ≫ G, ⟨?_⟩, ⟨?_⟩⟩
  · exact (unitIso i ≪≫ eqToIso (by simp) ≪≫ Bicategory.whiskerLeftIso (HoTwo.homOfMap F)
      (Bicategory.whiskerRightIso (unitIso i') (HoTwo.homOfMap G)) ≪≫
        eqToIso (by simp [HoTwo.homOfMap_comp]) :
          𝟙 (HoTwo.of X) ≅ HoTwo.homOfMap ((F ≫ H) ≫ K ≫ G))
  · exact (eqToIso (by simp [HoTwo.homOfMap_comp]) ≪≫
      Bicategory.whiskerLeftIso (HoTwo.homOfMap K)
        (Bicategory.whiskerRightIso (counitIso j) (HoTwo.homOfMap H)) ≪≫
          eqToIso (by simp) ≪≫ counitIso j' :
            HoTwo.homOfMap ((K ≫ G) ≫ F ≫ H) ≅ 𝟙 (HoTwo.of Z))

theorem exists_homotopyAdjunction (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    {F : X ⟶ Y} (hF : IsHomotopyEquivalence F) :
    ∃ (G : Y ⟶ X) (a : HomotopyAdjunction F G), IsIso (OneTruncation.globeHomMk a.unit) ∧
      IsIso (OneTruncation.globeHomMk a.counit) := by
  obtain ⟨G, ⟨i⟩, ⟨j⟩⟩ := hF
  let e := Bicategory.Equivalence.mkOfAdjointifyCounit (unitIso i) (counitIso j)
  let adj : Bicategory.Adjunction (HoTwo.homOfMap F) (HoTwo.homOfMap G) :=
    ⟨e.unit.hom, e.counit.hom, e.left_triangle_hom, e.right_triangle_hom⟩
  refine ⟨G, HomotopyAdjunction.ofBicategory hX hY adj, ?_, ?_⟩
  · have : IsIso (HomotopyAdjunction.unitCell (HomotopyAdjunction.ofBicategory hX hY adj).unit) :=
      (HomotopyAdjunction.unitCell_ofBicategory_unit hX hY adj).symm ▸
        inferInstanceAs (IsIso e.unit.hom)
    exact HomotopyAdjunction.isIso_homMk_of_isIso_unitCell _
  · have : IsIso (HomotopyAdjunction.counitCell
        (HomotopyAdjunction.ofBicategory hX hY adj).counit) :=
      (HomotopyAdjunction.counitCell_ofBicategory_counit hX hY adj).symm ▸
        inferInstanceAs (IsIso e.counit.hom)
    exact HomotopyAdjunction.isIso_homMk_of_isIso_counitCell _

private theorem isEquivalence_truncMap {F : X ⟶ Y} (hF : IsHomotopyEquivalence F) :
    (truncMap F).IsEquivalence := by
  obtain ⟨G, ⟨i⟩, ⟨j⟩⟩ := hF
  exact (CategoryTheory.Equivalence.mk (truncMap F) (truncMap G)
    (eqToIso ((truncMap_id X).symm.trans (homFunctor_obj_mk (𝟙 X)).symm) ≪≫
      (homFunctor X X).mapIso i ≪≫
        eqToIso ((homFunctor_obj_mk (F ≫ G)).trans (truncMap_comp F G).symm))
    (eqToIso ((truncMap_comp G F).trans (homFunctor_obj_mk (G ≫ F)).symm) ≪≫
      (homFunctor Y Y).mapIso j ≪≫
        eqToIso ((homFunctor_obj_mk (𝟙 Y)).trans (truncMap_id Y)))).isEquivalence_functor

theorem isEquivalence_homotopyFunctor (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    {F : X ⟶ Y} (hF : IsHomotopyEquivalence F) : (homotopyFunctor hX.1 hY.1 F).IsEquivalence := by
  have := isEquivalence_toHomotopyCategory hX
  have := isEquivalence_toHomotopyCategory hY
  have := isEquivalence_truncMap hF
  have : (OneTruncation.toHomotopyCategory hX ⋙ homotopyFunctor hX.1 hY.1 F).IsEquivalence :=
    @Functor.isEquivalence_of_iso _ _ _ _ _ _
      (eqToIso (OneTruncation.toHomotopyCategory_naturality hX hY F))
      (Functor.isEquivalence_trans (truncMap F) (OneTruncation.toHomotopyCategory hY))
  exact Functor.isEquivalence_of_comp_left (OneTruncation.toHomotopyCategory hX) _

end IsHomotopyEquivalence

end Atoms.Diagrammatic
