import Atoms.Diagrammatic.Marked.GrayTensorMonoidal
import Atoms.Diagrammatic.Vertex
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open MarkedPresheaf (forget)

variable {S A B Y : MarkedDiagSet.{u}}

noncomputable def markedHomRightPoint (a : A ⟶ S) :
    markedTensorUnit.{u} ⟶ (markedHomRight false A).obj S :=
  (tensorRightAdjunction false A).homEquiv _ _ ((markedTensorLeftUnitor false A).hom ≫ a)

@[reassoc]
theorem markedHomRightPoint_comp_markedHomRestrict (i : A ⟶ B) (b : B ⟶ S) :
    markedHomRightPoint b ≫ (markedHomRestrict i).app S = markedHomRightPoint (i ≫ b) :=
  (homEquiv_markedHomRestrict i _).symm.trans
    (congrArg _ (markedTensorLeftUnitor_naturality_assoc false i b))

noncomputable def markedGrayMapOver (a : A ⟶ S) (y : Y ⟶ S) : DiagSet.{u} :=
  forget.obj (pullback ((markedHomRight false A).map y) (markedHomRightPoint a))

noncomputable def markedHomRightFibreRestrict (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S) :
    pullback ((markedHomRight false B).map y) (markedHomRightPoint b) ⟶
      pullback ((markedHomRight false A).map y) (markedHomRightPoint (i ≫ b)) :=
  pullback.map _ _ _ _ ((markedHomRestrict i).app Y) (𝟙 _) ((markedHomRestrict i).app S)
    ((markedHomRestrict i).naturality y)
    ((markedHomRightPoint_comp_markedHomRestrict i b).trans (Category.id_comp _).symm)

@[reassoc]
theorem markedHomRightFibreRestrict_fst (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S) :
    markedHomRightFibreRestrict i b y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (markedHomRestrict i).app Y :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem markedHomRightFibreRestrict_snd (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S) :
    markedHomRightFibreRestrict i b y ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

noncomputable def markedGrayMapOverRestrict (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S) :
    markedGrayMapOver b y ⟶ markedGrayMapOver (i ≫ b) y :=
  forget.map (markedHomRightFibreRestrict i b y)

theorem isPullback_markedHomRightFibreRestrict (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S) :
    IsPullback (pullback.fst _ _) (markedHomRightFibreRestrict i b y)
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i y).π
      ((Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i y).isPullback.lift
        (pullback.fst _ _) (pullback.snd _ _ ≫ markedHomRightPoint b)
        ((pullback.condition.trans (congrArg (_ ≫ ·)
          (markedHomRightPoint_comp_markedHomRestrict i b).symm)).trans
            (Category.assoc _ _ _).symm)) := by
  let sq := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i y
  refine IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := sq.snd)
    (h₃₁ := markedHomRightPoint b) ?_ ?_ ?_
  · convert IsPullback.of_hasPullback ((markedHomRight false B).map y) (markedHomRightPoint b)
      using 1
    · exact markedHomRightFibreRestrict_snd i b y
    · exact sq.π_snd
  · refine sq.isPullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.π_fst).trans
        ((markedHomRightFibreRestrict_fst i b y).symm.trans
          ((congrArg (_ ≫ ·) (IsPullback.lift_fst _ _ _ _).symm).trans
            (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq.π_snd).trans
        (pullback.condition.trans ((markedHomRightFibreRestrict_snd_assoc i b y _).symm.trans
          ((congrArg (_ ≫ ·) (IsPullback.lift_snd _ _ _ _).symm).trans
            (Category.assoc _ _ _).symm))))
  · refine IsPullback.of_right (h₁₂ := sq.fst) (h₂₂ := (markedHomRestrict i).app S)
      (v₁₃ := (markedHomRight false A).map y) ?_ (IsPullback.lift_snd _ _ _ _) sq.isPullback
    have h := IsPullback.of_hasPullback ((markedHomRight false A).map y)
      (markedHomRightPoint (i ≫ b))
    have e₁ := sq.isPullback.lift_fst (pullback.fst _ _)
      (pullback.snd _ _ ≫ markedHomRightPoint b)
      ((pullback.condition.trans (congrArg (_ ≫ ·)
        (markedHomRightPoint_comp_markedHomRestrict i b).symm)).trans (Category.assoc _ _ _).symm)
    exact e₁.symm ▸ (markedHomRightPoint_comp_markedHomRestrict i b).symm ▸ h

theorem hasLiftingProperty_markedGrayMapOverRestrict (i : A ⟶ B) (b : B ⟶ S) (y : Y ⟶ S)
    {K L : DiagSet.{u}} (m : K ⟶ L)
    (h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
        ((MarkedPresheaf.flat atomMarking).map m) i).ι y) :
    HasLiftingProperty m (markedGrayMapOverRestrict i b y) := by
  refine ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff m
    (markedHomRightFibreRestrict i b y)).1 ?_
  have : HasLiftingProperty ((MarkedPresheaf.flat atomMarking).map m)
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i y).π :=
    (markedTensorRightParametrizedAdjunction.hasLiftingProperty_iff
      (Functor.PushoutObjObj.ofHasPushout _ ((MarkedPresheaf.flat atomMarking).map m) i).flip
      (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u} i y)).1 h
  exact @IsPullback.hasLiftingProperty _ _ _ _ _ _ _ _ _ _
    (isPullback_markedHomRightFibreRestrict i b y) _ _ _ this

private theorem tensorRight_map_comp_leftUnitor_hom {T : MarkedDiagSet.{u}}
    (k : T ⟶ markedTensorUnit) (A : MarkedDiagSet.{u}) :
    (tensorRight false A).map k ≫ (markedTensorLeftUnitor false A).hom =
      markedTensorSnd false T A := by
  obtain rfl := isTerminalMarkedTensorUnit.hom_ext k (isTerminalMarkedTensorUnit.from T)
  exact MarkedPresheaf.hom_ext rfl

private theorem homEquiv_symm_comp_markedHomRightPoint {T : MarkedDiagSet.{u}}
    (k : T ⟶ markedTensorUnit) (a : A ⟶ S) :
    ((tensorRightAdjunction false A).homEquiv T S).symm (k ≫ markedHomRightPoint a) =
      markedTensorSnd false T A ≫ a :=
  (congrArg _ ((tensorRightAdjunction false A).homEquiv_naturality_left k _).symm).trans
    ((Equiv.symm_apply_apply _ _).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ a) (tensorRight_map_comp_leftUnitor_hom k A))))

noncomputable def markedHomRightFibreHomEquiv (a : A ⟶ S) (y : Y ⟶ S) (T : MarkedDiagSet.{u}) :
    (T ⟶ pullback ((markedHomRight false A).map y) (markedHomRightPoint a)) ≃
      {f : markedGrayTensor T A ⟶ Y // f ≫ y = markedTensorSnd false T A ≫ a} where
  toFun g := ⟨((tensorRightAdjunction false A).homEquiv T Y).symm (g ≫ pullback.fst _ _),
    ((tensorRightAdjunction false A).homEquiv_naturality_right_symm _ _).symm.trans
      ((congrArg _ ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm))).trans (homEquiv_symm_comp_markedHomRightPoint _ a))⟩
  invFun f := pullback.lift ((tensorRightAdjunction false A).homEquiv T Y f.1)
    (isTerminalMarkedTensorUnit.from T)
    ((((tensorRightAdjunction false A).homEquiv_naturality_right _ _).symm.trans
      (congrArg _ f.2)).trans ((congrArg _ (homEquiv_symm_comp_markedHomRightPoint
        (isTerminalMarkedTensorUnit.from T) a)).symm.trans (Equiv.apply_symm_apply _ _)))
  left_inv _ := pullback.hom_ext
    ((pullback.lift_fst _ _ _).trans (Equiv.apply_symm_apply _ _))
    (isTerminalMarkedTensorUnit.hom_ext _ _)
  right_inv _ := Subtype.ext ((congrArg _ (pullback.lift_fst _ _ _)).trans
    (Equiv.symm_apply_apply _ _))

noncomputable def markedGrayMapOverHomEquiv (a : A ⟶ S) (y : Y ⟶ S) (K : DiagSet.{u}) :
    (K ⟶ markedGrayMapOver a y) ≃
      {f : markedGrayTensor ((MarkedPresheaf.flat atomMarking).obj K) A ⟶ Y //
        f ≫ y = markedTensorSnd false _ A ≫ a} :=
  ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv K _).symm.trans
    (markedHomRightFibreHomEquiv a y _)

noncomputable def markedGrayMapOverVertexEquiv (a : A ⟶ S) (y : Y ⟶ S) :
    (markedGrayMapOver a y).Vertex ≃ {f : A ⟶ Y // f ≫ y = a} :=
  (uliftYonedaEquiv.symm.trans (markedGrayMapOverHomEquiv a y (ball.{u} atomPoint))).trans
    (Equiv.subtypeEquiv (markedTensorLeftUnitor false A).homFromEquiv fun f ↦ by
      have hsnd : markedTensorSnd false _ A = (markedTensorLeftUnitor false A).hom :=
        (tensorRight_map_comp_leftUnitor_hom (𝟙 _) A).symm.trans
          ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))
      rw [Iso.homFromEquiv_apply, Category.assoc, hsnd]
      exact ⟨fun h ↦ by rw [h, Iso.inv_hom_id_assoc],
        fun h ↦ by rw [← h, Iso.hom_inv_id_assoc]⟩)

private noncomputable def tensorRightUnitIso :
    tensorRight false markedTensorUnit.{u} ≅ 𝟭 MarkedDiagSet.{u} :=
  NatIso.ofComponents (markedTensorRightUnitor false) (markedTensorRightUnitor_naturality false)

noncomputable def markedHomRightUnitIso :
    markedHomRight false markedTensorUnit.{u} ≅ 𝟭 MarkedDiagSet.{u} :=
  conjugateIsoEquiv (tensorRightAdjunction false markedTensorUnit) Adjunction.id
    tensorRightUnitIso.symm

theorem homEquiv_comp_markedHomRightUnitIso_hom_app {T Y : MarkedDiagSet.{u}}
    (g : markedGrayTensor T markedTensorUnit ⟶ Y) :
    (tensorRightAdjunction false markedTensorUnit).homEquiv T Y g ≫
        markedHomRightUnitIso.hom.app Y =
      (markedTensorRightUnitor false T).inv ≫ g :=
  (congrArg (· ≫ markedHomRightUnitIso.hom.app Y)
    ((tensorRightAdjunction false markedTensorUnit).homEquiv_unit T Y g)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (markedHomRightUnitIso.hom.naturality g)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) ((unit_conjugateEquiv (tensorRightAdjunction false markedTensorUnit)
          Adjunction.id tensorRightUnitIso.symm.hom T).trans (Category.id_comp _))))))

theorem markedHomRightPoint_comp_markedHomRightUnitIso_hom_app (c : markedTensorUnit ⟶ S) :
    markedHomRightPoint c ≫ markedHomRightUnitIso.hom.app S = c :=
  (homEquiv_comp_markedHomRightUnitIso_hom_app _).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ c) (isTerminalMarkedTensorUnit.hom_ext _ (𝟙 _))).trans (Category.id_comp _)))

theorem isPullback_markedGrayMapOver_unit (c : markedTensorUnit ⟶ S) (y : Y ⟶ S) :
    IsPullback
      (forget.map (pullback.fst ((markedHomRight false markedTensorUnit).map y)
        (markedHomRightPoint c) ≫ markedHomRightUnitIso.hom.app Y))
      (forget.map (pullback.snd ((markedHomRight false markedTensorUnit).map y)
        (markedHomRightPoint c)))
      (forget.map y) (forget.map c) :=
  IsPullback.of_iso ((IsPullback.of_hasPullback _ _).map forget) (Iso.refl _)
    (forget.mapIso (markedHomRightUnitIso.app Y)) (Iso.refl _)
    (forget.mapIso (markedHomRightUnitIso.app S))
    ((forget.map_comp _ _).symm.trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((forget.map_comp _ _).symm.trans ((congrArg forget.map
      (markedHomRightUnitIso.hom.naturality y)).trans (forget.map_comp _ _)))
    ((forget.map_comp _ _).symm.trans ((congrArg forget.map
      (markedHomRightPoint_comp_markedHomRightUnitIso_hom_app c)).trans (Category.id_comp _).symm))

noncomputable def markedGrayMapOverUnitIso (c : markedTensorUnit ⟶ S) (y : Y ⟶ S) :
    markedGrayMapOver c y ≅ pullback (forget.map y) (forget.map c) :=
  (isPullback_markedGrayMapOver_unit c y).isoPullback

@[reassoc]
theorem markedGrayMapOverUnitIso_hom_fst (c : markedTensorUnit ⟶ S) (y : Y ⟶ S) :
    (markedGrayMapOverUnitIso c y).hom ≫ pullback.fst _ _ =
      forget.map (pullback.fst ((markedHomRight false markedTensorUnit).map y)
        (markedHomRightPoint c) ≫ markedHomRightUnitIso.hom.app Y) :=
  IsPullback.isoPullback_hom_fst _

end Atoms.Diagrammatic
