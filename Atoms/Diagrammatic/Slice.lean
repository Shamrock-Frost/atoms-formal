import Atoms.Diagrammatic.Join
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.JoinSlice

open CategoryTheory CategoryTheory.WithInitial Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable def sliceBallObjEquiv (V : Atom) {X : DiagSet.{u}} (x : ball.{u} V ⟶ X) (U : Atom) :
    ((WithInitial.slice (ball.{u} V)).obj (Under.mk x)).obj (op U) ≃
      {t : X.obj (op (atomJoin U V)) //
        X.map (joinInclRightHom U V).op t = uliftYonedaEquiv x} :=
  (sliceObjEquiv (ball.{u} V) (Under.mk x) U).trans
    (((joinBallIso U V).homFromEquiv.trans uliftYonedaEquiv).subtypeEquiv fun f ↦ by
      rw [Equiv.trans_apply, uliftYonedaEquiv_naturality, uliftYonedaEquiv.apply_eq_iff_eq,
        Quiver.Hom.unop_op, Iso.homFromEquiv_apply, ← joinInclRight_comp_joinBallIso_hom_assoc,
        Iso.hom_inv_id_assoc]
      rfl)

noncomputable def cosliceBallObjEquiv (V : Atom) {X : DiagSet.{u}} (x : ball.{u} V ⟶ X)
    (U : Atom) :
    ((WithInitial.coslice (ball.{u} V)).obj (Under.mk x)).obj (op U) ≃
      {t : X.obj (op (atomJoin V U)) //
        X.map (joinInclLeftHom V U).op t = uliftYonedaEquiv x} :=
  (cosliceObjEquiv (ball.{u} V) (Under.mk x) U).trans
    (((joinBallIso V U).homFromEquiv.trans uliftYonedaEquiv).subtypeEquiv fun f ↦ by
      rw [Equiv.trans_apply, uliftYonedaEquiv_naturality, uliftYonedaEquiv.apply_eq_iff_eq,
        Quiver.Hom.unop_op, Iso.homFromEquiv_apply, ← joinInclLeft_comp_joinBallIso_hom_assoc,
        Iso.hom_inv_id_assoc]
      rfl)

noncomputable def sliceProj (A : DiagSet.{u}) : WithInitial.slice A ⟶ Under.forget A where
  app t :=
    { app U := TypeCat.ofHom fun g ↦
        uliftYonedaEquiv (joinInclLeft (ball.{u} U.unop) A ≫ (sliceObjEquiv A t U.unop g).1)
      naturality U U' f := by
        ext g
        refine (congrArg uliftYonedaEquiv ?_).trans (uliftYonedaEquiv_naturality _ f).symm
        exact joinInclLeft_comp_joinMap_assoc (uliftYoneda.{u}.map f.unop) (𝟙 A)
          (sliceObjEquiv A t U.unop g).1 }
  naturality t t' φ := by
    ext U g
    exact (uliftYonedaEquiv_comp
      (joinInclLeft (ball.{u} U.unop) A ≫ (sliceObjEquiv A t U.unop g).1) φ.right).symm

theorem sliceProj_app_app_eq (V : Atom) {X : DiagSet.{u}} (x : ball.{u} V ⟶ X) (U : Atom)
    (c : ((WithInitial.slice (ball.{u} V)).obj (Under.mk x)).obj (op U)) :
    ((sliceProj (ball.{u} V)).app (Under.mk x)).app (op U) c =
      X.map (joinInclLeftHom U V).op (sliceBallObjEquiv V x U c).1 := by
  refine (congrArg uliftYonedaEquiv ?_).trans (uliftYonedaEquiv_naturality
    ((joinBallIso U V).inv ≫ (sliceObjEquiv (ball.{u} V) (Under.mk x) U c).1)
    (joinInclLeftHom U V).op).symm
  exact (congrArg (joinInclLeft (ball.{u} U) (ball.{u} V) ≫ ·)
    (Iso.hom_inv_id_assoc (joinBallIso U V) _).symm).trans
      (joinInclLeft_comp_joinBallIso_hom_assoc U V _)

theorem sliceProj_app_eq (A : DiagSet.{u}) (t : Under A) :
    (sliceProj A).app t =
      joinInclLeft ((WithInitial.slice A).obj t) A ≫
        ((WithInitial.joinRightUnderAdjunction A).counit.app t).right := by
  ext U g
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder A) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0} (joinRightUnder A) (Iso.refl _)
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} (joinRightUnder A) (Iso.refl _).hom
    ((WithInitial.joinRightUnderAdjunction A).counit.app t) g
  have e := ((WithInitial.joinRightUnderAdjunction A).homEquiv_unit _ _ _).trans
    ((WithInitial.joinRightUnderAdjunction A).right_triangle_components t)
  have hg : g.down = (joinRightUnder A).map (uliftYonedaEquiv.symm g) ≫
      (WithInitial.joinRightUnderAdjunction A).counit.app t :=
    (congrArg ULift.down ((congrArg (fun f ↦ f.app U g) e).symm.trans h)).trans
      (Category.id_comp _)
  refine (congrArg (fun f ↦ uliftYonedaEquiv (joinInclLeft (ball.{u} U.unop) A ≫ f.right))
    hg).trans ?_
  exact (congrArg uliftYonedaEquiv (joinInclLeft_comp_joinMap_assoc _ _ _)).trans
    ((uliftYonedaEquiv_comp _ _).trans (congrArg _ (uliftYonedaEquiv.apply_symm_apply g)))

noncomputable def sliceRestrict {A' A : DiagSet.{u}} (i : A' ⟶ A) :
    WithInitial.slice A ⟶ Under.map i ⋙ WithInitial.slice A' where
  app t :=
    { app U := TypeCat.ofHom fun c ↦ (sliceObjEquiv A' ((Under.map i).obj t) U.unop).symm
        ⟨joinMap (𝟙 _) i ≫ (sliceObjEquiv A t U.unop c).1, (joinInclRight_comp_joinMap_assoc (𝟙 _) i
          (sliceObjEquiv A t U.unop c).1).trans
            (congrArg (i ≫ ·) (sliceObjEquiv A t U.unop c).2)⟩
      naturality U U' f := by
        ext c
        refine ULift.ext _ _ (Under.UnderMorphism.ext ?_)
        have key : joinMap (𝟙 (ball.{u} U'.unop)) i ≫ joinMap (uliftYoneda.{u}.map f.unop) (𝟙 A) =
            joinMap (uliftYoneda.{u}.map f.unop) (𝟙 A') ≫ joinMap (𝟙 (ball.{u} U.unop)) i :=
          by rw [joinMap_comp_joinMap, joinMap_comp_joinMap, Category.id_comp, Category.comp_id,
            Category.id_comp, Category.comp_id]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (sliceObjEquiv A t U.unop c).1) key).trans (Category.assoc _ _ _)) }
  naturality t t' φ := by
    ext U c
    rfl

@[reassoc] theorem sliceRestrict_app_comp_sliceProj_app {A' A : DiagSet.{u}} (i : A' ⟶ A)
    (t : Under A) :
    (sliceRestrict i).app t ≫ (sliceProj A').app ((Under.map i).obj t) = (sliceProj A).app t := by
  ext U c
  exact congrArg uliftYonedaEquiv
    ((joinInclLeft_comp_joinMap_assoc (𝟙 (ball.{u} U.unop)) i
      (sliceObjEquiv A t U.unop c).1).trans (Category.id_comp _))

private theorem isEmpty_obj_of_isInitial {E : DiagSet.{u}} (hE : IsInitial E) (c : Atomᵒᵖ) :
    IsEmpty (E.obj c) :=
  ⟨fun e ↦ PEmpty.elim ((hE.to ((Functor.const Atomᵒᵖ).obj PEmpty)).app c e)⟩

private noncomputable def sliceEmptyObjEquiv {E : DiagSet.{u}} (hE : IsInitial E) (X : Under E)
    (U : Atom) : ((WithInitial.slice E).obj X).obj (op U) ≃ X.right.obj (op U) :=
  have := isEmpty_obj_of_isInitial hE
  have := isIso_joinInclLeft_of_isEmpty (ball.{u} U) E
  (sliceObjEquiv E X U).trans ((Equiv.subtypeUnivEquiv fun _ ↦ hE.hom_ext _ _).trans
    ((asIso (joinInclLeft (ball.{u} U) E)).symm.homFromEquiv.trans uliftYonedaEquiv))

noncomputable def sliceEmptyIso {E : DiagSet.{u}} (hE : IsInitial E) (X : Under E) :
    (WithInitial.slice E).obj X ≅ X.right :=
  NatIso.ofComponents (fun U ↦ (sliceEmptyObjEquiv hE X U.unop).toIso)
    fun f ↦ ((sliceProj E).app X).naturality f

theorem sliceEmptyIso_hom {E : DiagSet.{u}} (hE : IsInitial E) (X : Under E) :
    (sliceEmptyIso hE X).hom = (sliceProj E).app X :=
  rfl

end Atoms.Diagrammatic
