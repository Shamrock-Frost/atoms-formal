import Atoms.Diagrammatic.Dual
import Atoms.Diagrammatic.Slice

open CategoryTheory CategoryTheory.WithInitial Limits Opposite Atoms.Shape
open Atoms.Diagrammatic.DiagSet (dual)

universe u

namespace Atoms.Diagrammatic

private instance preservesColimitsOfSize_dual :
    PreservesColimitsOfSize.{0, u} (dual.{u} Nat.bodd) :=
  (DiagSet.dualEquivalence Nat.bodd).toAdjunction.leftAdjoint_preservesColimits

private theorem ext_of_preservesColimits {F G : DiagSet.{u} ⥤ DiagSet.{u}}
    [PreservesColimitsOfSize.{0, u} F] {α β : ∀ X, F.obj X ⟶ G.obj X}
    (hα : ∀ {X X'} (f : X ⟶ X'), F.map f ≫ α X' = α X ≫ G.map f)
    (hβ : ∀ {X X'} (f : X ⟶ X'), F.map f ≫ β X' = β X ≫ G.map f)
    (h : ∀ U : Atom, α (ball U) = β (ball U)) (X : DiagSet.{u}) : α X = β X :=
  congr_app (hom_ext_of_preservesColimits (α := ⟨α, fun _ _ f ↦ hα f⟩)
    (β := ⟨β, fun _ _ f ↦ hβ f⟩) h) X

private theorem under_ext {A : DiagSet.{u}} (F : DiagSet.{u} ⥤ Under A)
    [PreservesColimitsOfSize.{0, u} F] {G : DiagSet.{u} ⥤ DiagSet.{u}}
    {α β : ∀ X, (F.obj X).right ⟶ G.obj X}
    (hα : ∀ {X X'} (f : X ⟶ X'), (F.map f).right ≫ α X' = α X ≫ G.map f)
    (hβ : ∀ {X X'} (f : X ⟶ X'), (F.map f).right ≫ β X' = β X ≫ G.map f)
    (hA : ∀ X, (F.obj X).hom ≫ α X = (F.obj X).hom ≫ β X)
    (h : ∀ U : Atom, α (ball U) = β (ball U)) (X : DiagSet.{u}) : α X = β X := by
  let G' : DiagSet.{u} ⥤ Under A :=
    { obj X := Under.mk ((F.obj X).hom ≫ α X)
      map {X X'} f := Under.homMk (G.map f) ((Category.assoc _ _ _).trans
        ((congrArg _ (hα f).symm).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ α X') (Under.w (F.map f))))))
      map_id X := Under.UnderMorphism.ext (G.map_id X)
      map_comp f g := Under.UnderMorphism.ext (G.map_comp f g) }
  exact congrArg CommaMorphism.right (congr_app (hom_ext_of_preservesColimits
    (α := (⟨fun X ↦ Under.homMk (α X) rfl, fun _ _ f ↦ Under.UnderMorphism.ext (hα f)⟩ : F ⟶ G'))
    (β := ⟨fun X ↦ Under.homMk (β X) (hA X).symm, fun _ _ f ↦ Under.UnderMorphism.ext (hβ f)⟩)
    fun U ↦ Under.UnderMorphism.ext (h U)) X)

private noncomputable def ballIso (U V : Atom) :
    (dual Nat.bodd).obj (WithInitial.join (ball.{u} U) (ball.{u} V)) ≅
      WithInitial.join ((dual Nat.bodd).obj (ball.{u} V))
        ((dual Nat.bodd).obj (ball.{u} U)) :=
  (dual Nat.bodd).mapIso (joinBallIso U V) ≪≫ DiagSet.dualBallIso Nat.bodd _ ≪≫
    uliftYoneda.mapIso (Atom.joinDualIso U V) ≪≫ (joinBallIso _ _).symm ≪≫
      joinMapIso (DiagSet.dualBallIso Nat.bodd V).symm (DiagSet.dualBallIso Nat.bodd U).symm

private theorem ballIso_naturality {U U' V V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    (dual Nat.bodd).map
        (WithInitial.joinMap (uliftYoneda.{u}.map f) (uliftYoneda.{u}.map g)) ≫
        (ballIso U' V').hom =
      (ballIso U V).hom ≫ WithInitial.joinMap ((dual Nat.bodd).map (uliftYoneda.map g))
        ((dual Nat.bodd).map (uliftYoneda.map f)) := by
  simp only [ballIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom,
    Category.assoc]
  rw [← Functor.map_comp_assoc, joinMap_uliftYoneda_map_comp_joinBallIso_hom,
    Functor.map_comp_assoc,
    DiagSet.dual_map_uliftYoneda_map_comp_dualBallIso_hom_assoc, ← Functor.map_comp_assoc,
    Atom.dualMap_joinHom_comp_joinDualIso_hom, Functor.map_comp_assoc]
  have h₁ : ∀ {U U' : Atom} (f : U ⟶ U'), uliftYoneda.{u}.map (Atom.dualMap Nat.bodd f) ≫
      (DiagSet.dualBallIso Nat.bodd U').inv =
        (DiagSet.dualBallIso Nat.bodd U).inv ≫ (dual Nat.bodd).map (uliftYoneda.map f) :=
    fun f ↦ by
      rw [Iso.comp_inv_eq, Category.assoc, DiagSet.dual_map_uliftYoneda_map_comp_dualBallIso_hom,
        Iso.inv_hom_id_assoc]
  have h₂ : uliftYoneda.{u}.map (joinHom (Atom.dualMap Nat.bodd g) (Atom.dualMap Nat.bodd f)) ≫
      (joinBallIso _ _).inv = (joinBallIso _ _).inv ≫ WithInitial.joinMap
        (uliftYoneda.map (Atom.dualMap Nat.bodd g))
        (uliftYoneda.map (Atom.dualMap Nat.bodd f)) := by
    rw [Iso.comp_inv_eq, Category.assoc, joinMap_uliftYoneda_map_comp_joinBallIso_hom,
      Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₂, joinMap_comp_joinMap, joinMap_comp_joinMap, h₁, h₁]

private theorem dual_map_joinInclLeft_comp_ballIso_hom (U V : Atom) :
    (dual Nat.bodd).map (WithInitial.joinInclLeft (ball.{u} U) (ball.{u} V)) ≫
        (ballIso U V).hom = WithInitial.joinInclRight _ _ := by
  simp only [ballIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom]
  rw [← Functor.map_comp_assoc, joinInclLeft_comp_joinBallIso_hom,
    DiagSet.dual_map_uliftYoneda_map_comp_dualBallIso_hom_assoc, ← Functor.map_comp_assoc,
    Atom.dualMap_joinInclLeftHom_comp_joinDualIso_hom, ← joinInclRight_comp_joinBallIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, joinInclRight_comp_joinMap, Iso.hom_inv_id_assoc]

private theorem dual_map_joinInclRight_comp_ballIso_hom (U V : Atom) :
    (dual Nat.bodd).map (WithInitial.joinInclRight (ball.{u} U) (ball.{u} V)) ≫
        (ballIso U V).hom = WithInitial.joinInclLeft _ _ := by
  simp only [ballIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, joinMapIso_hom]
  rw [← Functor.map_comp_assoc, joinInclRight_comp_joinBallIso_hom,
    DiagSet.dual_map_uliftYoneda_map_comp_dualBallIso_hom_assoc, ← Functor.map_comp_assoc,
    Atom.dualMap_joinInclRightHom_comp_joinDualIso_hom, ← joinInclLeft_comp_joinBallIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc, joinInclLeft_comp_joinMap, Iso.hom_inv_id_assoc]

private instance preservesColimitsOfSize_joinRightUnder_post (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinRightUnder A ⋙ Under.post (dual Nat.bodd)) :=
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder A) := preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, u} (Under.post (X := A) (dual.{u} Nat.bodd)) :=
    (Under.postAdjunctionLeft
      (DiagSet.dualEquivalence Nat.bodd).toAdjunction).leftAdjoint_preservesColimits
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_joinLeftUnder_post (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinLeftUnder A ⋙ Under.post (dual Nat.bodd)) :=
  have : PreservesColimitsOfSize.{0, u} (joinLeftUnder A) := preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, u} (Under.post (X := A) (dual.{u} Nat.bodd)) :=
    (Under.postAdjunctionLeft
      (DiagSet.dualEquivalence Nat.bodd).toAdjunction).leftAdjoint_preservesColimits
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_dual_joinLeftUnder (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (dual Nat.bodd ⋙ joinLeftUnder A) :=
  have : PreservesColimitsOfSize.{0, u} (joinLeftUnder A) := preservesColimitsOfSize_shrink _
  comp_preservesColimits _ _

private instance preservesColimitsOfSize_dual_joinRightUnder (A : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (dual Nat.bodd ⋙ joinRightUnder A) :=
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder A) := preservesColimitsOfSize_shrink _
  comp_preservesColimits _ _

private noncomputable def ballJoinRightUnderIso (V : Atom) :
    uliftYoneda.{u} ⋙ joinRightUnder (ball.{u} V) ⋙ Under.post (dual Nat.bodd) ≅
      uliftYoneda.{u} ⋙ dual Nat.bodd ⋙
        joinLeftUnder ((dual Nat.bodd).obj (ball.{u} V)) :=
  NatIso.ofComponents
    (fun U ↦ Under.isoMk (ballIso U V) (dual_map_joinInclRight_comp_ballIso_hom U V))
    fun {U U'} f ↦ Under.UnderMorphism.ext (by
      have h := ballIso_naturality.{u} f (𝟙 V)
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
      exact h)

private noncomputable def joinRightUnderBallIso (V : Atom) :
    joinRightUnder (ball.{u} V) ⋙ Under.post (dual Nat.bodd) ≅
      dual Nat.bodd ⋙ joinLeftUnder ((dual Nat.bodd).obj (ball.{u} V)) :=
  isoOfPreservesColimits _ _ (ballJoinRightUnderIso V)

private noncomputable def joinBallDualIso (X : DiagSet.{u}) (V : Atom) :
    (dual Nat.bodd).obj (WithInitial.join X (ball.{u} V)) ≅
      WithInitial.join ((dual Nat.bodd).obj (ball.{u} V)) ((dual Nat.bodd).obj X) :=
  (Under.forget _).mapIso ((joinRightUnderBallIso V).app X)

@[reassoc] private theorem dual_map_joinInclRight_comp_joinBallDualIso_hom (X : DiagSet.{u})
    (V : Atom) :
    (dual Nat.bodd).map (WithInitial.joinInclRight X (ball.{u} V)) ≫
        (joinBallDualIso X V).hom = WithInitial.joinInclLeft _ _ :=
  Under.w ((joinRightUnderBallIso V).hom.app X)

@[reassoc] private theorem joinBallDualIso_naturality {X X' : DiagSet.{u}} (f : X ⟶ X') (V : Atom) :
    (dual Nat.bodd).map (WithInitial.joinMap f (𝟙 (ball.{u} V))) ≫
        (joinBallDualIso X' V).hom =
      (joinBallDualIso X V).hom ≫ WithInitial.joinMap (𝟙 _) ((dual Nat.bodd).map f) :=
  congrArg CommaMorphism.right ((joinRightUnderBallIso V).hom.naturality f)

private theorem joinBallDualIso_ball (U V : Atom) :
    (joinBallDualIso (ball.{u} U) V).hom = (ballIso U V).hom :=
  congrArg CommaMorphism.right (isoOfPreservesColimits_hom_app _ _ (ballJoinRightUnderIso V) U)

private theorem dual_map_joinInclLeft_comp_joinBallDualIso_hom (X : DiagSet.{u}) (V : Atom) :
    (dual Nat.bodd).map (WithInitial.joinInclLeft X (ball.{u} V)) ≫
        (joinBallDualIso X V).hom = WithInitial.joinInclRight _ _ :=
  ext_of_preservesColimits (F := dual Nat.bodd)
    (G := dual Nat.bodd ⋙ joinLeftUnder _ ⋙ Under.forget _)
    (α := fun X ↦ (dual Nat.bodd).map (WithInitial.joinInclLeft X (ball.{u} V)) ≫
      (joinBallDualIso X V).hom) (β := fun _ ↦ WithInitial.joinInclRight _ _)
    (fun {X X'} f ↦ by
      change (dual Nat.bodd).map f ≫ (dual Nat.bodd).map (joinInclLeft X' _) ≫
          (joinBallDualIso X' V).hom = ((dual Nat.bodd).map (joinInclLeft X _) ≫
            (joinBallDualIso X V).hom) ≫ joinMap (𝟙 _) ((dual Nat.bodd).map f)
      rw [← Functor.map_comp_assoc, ← joinInclLeft_comp_joinMap f (𝟙 (ball.{u} V)),
        Functor.map_comp_assoc, joinBallDualIso_naturality, Category.assoc])
    (fun f ↦ (joinInclRight_comp_joinMap _ _).symm)
    (fun U ↦ by
      rw [joinBallDualIso_ball]
      exact dual_map_joinInclLeft_comp_ballIso_hom U V) X

private theorem joinBallDualIso_naturality_ball (X : DiagSet.{u}) {V V' : Atom} (g : V ⟶ V') :
    (dual Nat.bodd).map (WithInitial.joinMap (𝟙 X) (uliftYoneda.{u}.map g)) ≫
        (joinBallDualIso X V').hom =
      (joinBallDualIso X V).hom ≫
        WithInitial.joinMap ((dual Nat.bodd).map (uliftYoneda.map g)) (𝟙 _) :=
  under_ext (joinRightUnder (ball.{u} V) ⋙ Under.post (dual Nat.bodd))
    (G := dual Nat.bodd ⋙ joinLeftUnder _ ⋙ Under.forget _)
    (α := fun X ↦ (dual Nat.bodd).map (WithInitial.joinMap (𝟙 X) (uliftYoneda.map g)) ≫
      (joinBallDualIso X V').hom)
    (β := fun X ↦ (joinBallDualIso X V).hom ≫
      WithInitial.joinMap ((dual Nat.bodd).map (uliftYoneda.map g)) (𝟙 _))
    (fun {X X'} f ↦ by
      change (dual Nat.bodd).map (joinMap f (𝟙 _)) ≫
          (dual Nat.bodd).map (joinMap (𝟙 X') (uliftYoneda.map g)) ≫ (joinBallDualIso X' V').hom =
        ((dual Nat.bodd).map (joinMap (𝟙 X) (uliftYoneda.map g)) ≫
          (joinBallDualIso X V').hom) ≫ joinMap (𝟙 _) ((dual Nat.bodd).map f)
      rw [← Functor.map_comp_assoc, ← WithInitial.joinMap_exchange, Functor.map_comp_assoc,
        joinBallDualIso_naturality, Category.assoc])
    (fun {X X'} f ↦ by
      change (dual Nat.bodd).map (joinMap f (𝟙 _)) ≫ (joinBallDualIso X' V).hom ≫
          joinMap ((dual Nat.bodd).map (uliftYoneda.map g)) (𝟙 _) = ((joinBallDualIso X V).hom ≫
            joinMap ((dual Nat.bodd).map (uliftYoneda.map g)) (𝟙 _)) ≫
              joinMap (𝟙 _) ((dual Nat.bodd).map f)
      rw [joinBallDualIso_naturality_assoc, Category.assoc, ← WithInitial.joinMap_exchange])
    (fun X ↦ by
      change (dual Nat.bodd).map (joinInclRight X (ball V)) ≫
          (dual Nat.bodd).map (joinMap (𝟙 X) (uliftYoneda.map g)) ≫ (joinBallDualIso X V').hom =
        (dual Nat.bodd).map (joinInclRight X (ball V)) ≫ (joinBallDualIso X V).hom ≫
          joinMap ((dual Nat.bodd).map (uliftYoneda.map g)) (𝟙 _)
      rw [← Functor.map_comp_assoc, joinInclRight_comp_joinMap, Functor.map_comp_assoc,
        dual_map_joinInclRight_comp_joinBallDualIso_hom,
        dual_map_joinInclRight_comp_joinBallDualIso_hom_assoc, joinInclLeft_comp_joinMap])
    (fun U ↦ by
      have h := ballIso_naturality.{u} (𝟙 U) g
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
      rw [joinBallDualIso_ball, joinBallDualIso_ball]
      exact h) X

private noncomputable def ballJoinLeftUnderIso (X : DiagSet.{u}) :
    uliftYoneda.{u} ⋙ joinLeftUnder X ⋙ Under.post (dual Nat.bodd) ≅
      uliftYoneda.{u} ⋙ dual Nat.bodd ⋙ joinRightUnder ((dual Nat.bodd).obj X) :=
  NatIso.ofComponents (fun V ↦ Under.isoMk (joinBallDualIso X V)
      (dual_map_joinInclLeft_comp_joinBallDualIso_hom X V))
    fun g ↦ Under.UnderMorphism.ext (joinBallDualIso_naturality_ball X g)

noncomputable def joinLeftUnderDualIso (X : DiagSet.{u}) :
    joinLeftUnder X ⋙ Under.post (dual Nat.bodd) ≅
      dual Nat.bodd ⋙ joinRightUnder ((dual Nat.bodd).obj X) :=
  isoOfPreservesColimits _ _ (ballJoinLeftUnderIso X)

noncomputable def joinDualIso (X Y : DiagSet.{u}) :
    (dual Nat.bodd).obj (WithInitial.join X Y) ≅
      WithInitial.join ((dual Nat.bodd).obj Y) ((dual Nat.bodd).obj X) :=
  (Under.forget _).mapIso ((joinLeftUnderDualIso X).app Y)

@[reassoc] theorem dual_map_joinInclLeft_comp_joinDualIso_hom (X Y : DiagSet.{u}) :
    (dual Nat.bodd).map (WithInitial.joinInclLeft X Y) ≫ (joinDualIso X Y).hom =
      WithInitial.joinInclRight ((dual Nat.bodd).obj Y) ((dual Nat.bodd).obj X) :=
  Under.w ((joinLeftUnderDualIso X).hom.app Y)

@[reassoc] private theorem joinDualIso_naturality_right (X : DiagSet.{u}) {Y Y' : DiagSet.{u}}
    (g : Y ⟶ Y') :
    (dual Nat.bodd).map (joinMap (𝟙 X) g) ≫ (joinDualIso X Y').hom =
      (joinDualIso X Y).hom ≫ joinMap ((dual Nat.bodd).map g) (𝟙 _) :=
  congrArg CommaMorphism.right ((joinLeftUnderDualIso X).hom.naturality g)

private theorem joinDualIso_ball (X : DiagSet.{u}) (V : Atom) :
    (joinDualIso X (ball.{u} V)).hom = (joinBallDualIso X V).hom :=
  congrArg CommaMorphism.right (isoOfPreservesColimits_hom_app _ _ (ballJoinLeftUnderIso X) V)

@[reassoc] theorem dual_map_joinInclRight_comp_joinDualIso_hom (X Y : DiagSet.{u}) :
    (dual Nat.bodd).map (WithInitial.joinInclRight X Y) ≫ (joinDualIso X Y).hom =
      WithInitial.joinInclLeft ((dual Nat.bodd).obj Y) ((dual Nat.bodd).obj X) :=
  ext_of_preservesColimits (F := dual Nat.bodd)
    (G := dual Nat.bodd ⋙ joinRightUnder _ ⋙ Under.forget _)
    (α := fun Y ↦ (dual Nat.bodd).map (joinInclRight X Y) ≫ (joinDualIso X Y).hom)
    (β := fun _ ↦ joinInclLeft _ _)
    (fun {Y Y'} g ↦ by
      change (dual Nat.bodd).map g ≫ (dual Nat.bodd).map (joinInclRight X Y') ≫
          (joinDualIso X Y').hom = ((dual Nat.bodd).map (joinInclRight X Y) ≫
            (joinDualIso X Y).hom) ≫ joinMap ((dual Nat.bodd).map g) (𝟙 _)
      rw [← Functor.map_comp_assoc, ← joinInclRight_comp_joinMap (𝟙 X) g,
        Functor.map_comp_assoc, joinDualIso_naturality_right, Category.assoc])
    (fun g ↦ (joinInclLeft_comp_joinMap _ _).symm)
    (fun V ↦ by
      rw [joinDualIso_ball]
      exact dual_map_joinInclRight_comp_joinBallDualIso_hom X V) Y

@[reassoc] private theorem joinDualIso_naturality_left {X X' : DiagSet.{u}} (f : X ⟶ X')
    (Y : DiagSet.{u}) :
    (dual Nat.bodd).map (joinMap f (𝟙 Y)) ≫ (joinDualIso X' Y).hom =
      (joinDualIso X Y).hom ≫ joinMap (𝟙 _) ((dual Nat.bodd).map f) :=
  under_ext (joinLeftUnder X ⋙ Under.post (dual Nat.bodd))
    (G := dual Nat.bodd ⋙ joinRightUnder _ ⋙ Under.forget _)
    (α := fun Y ↦ (dual Nat.bodd).map (joinMap f (𝟙 Y)) ≫ (joinDualIso X' Y).hom)
    (β := fun Y ↦ (joinDualIso X Y).hom ≫ joinMap (𝟙 _) ((dual Nat.bodd).map f))
    (fun {Y Y'} g ↦ by
      change (dual Nat.bodd).map (joinMap (𝟙 X) g) ≫ (dual Nat.bodd).map (joinMap f (𝟙 Y')) ≫
          (joinDualIso X' Y').hom = ((dual Nat.bodd).map (joinMap f (𝟙 Y)) ≫
            (joinDualIso X' Y).hom) ≫ joinMap ((dual Nat.bodd).map g) (𝟙 _)
      rw [← Functor.map_comp_assoc, WithInitial.joinMap_exchange, Functor.map_comp_assoc,
        joinDualIso_naturality_right, Category.assoc])
    (fun {Y Y'} g ↦ by
      change (dual Nat.bodd).map (joinMap (𝟙 X) g) ≫ (joinDualIso X Y').hom ≫
          joinMap (𝟙 _) ((dual Nat.bodd).map f) = ((joinDualIso X Y).hom ≫
            joinMap (𝟙 _) ((dual Nat.bodd).map f)) ≫ joinMap ((dual Nat.bodd).map g) (𝟙 _)
      rw [joinDualIso_naturality_right_assoc, Category.assoc, WithInitial.joinMap_exchange])
    (fun Y ↦ by
      change (dual Nat.bodd).map (joinInclLeft X Y) ≫ (dual Nat.bodd).map (joinMap f (𝟙 Y)) ≫
          (joinDualIso X' Y).hom =
        (dual Nat.bodd).map (joinInclLeft X Y) ≫ (joinDualIso X Y).hom ≫
          joinMap (𝟙 _) ((dual Nat.bodd).map f)
      rw [← Functor.map_comp_assoc, joinInclLeft_comp_joinMap, Functor.map_comp_assoc,
        dual_map_joinInclLeft_comp_joinDualIso_hom,
        dual_map_joinInclLeft_comp_joinDualIso_hom_assoc, joinInclRight_comp_joinMap])
    (fun V ↦ by
      rw [joinDualIso_ball, joinDualIso_ball]
      exact joinBallDualIso_naturality f V) Y

@[reassoc] theorem dual_map_joinMap_comp_joinDualIso_hom {X X' Y Y' : DiagSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (dual Nat.bodd).map (WithInitial.joinMap f g) ≫ (joinDualIso X' Y').hom =
      (joinDualIso X Y).hom ≫
        WithInitial.joinMap ((dual Nat.bodd).map g) ((dual Nat.bodd).map f) := by
  have h : joinMap f g = joinMap f (𝟙 Y) ≫ joinMap (𝟙 X') g := by
    rw [joinMap_comp_joinMap, Category.comp_id, Category.id_comp]
  rw [h, Functor.map_comp_assoc, joinDualIso_naturality_right, joinDualIso_naturality_left_assoc,
    joinMap_comp_joinMap, Category.comp_id, Category.id_comp]

noncomputable def joinRightUnderDualIso (A : DiagSet.{u}) :
    joinRightUnder A ⋙ Under.post (dual Nat.bodd) ≅
      dual Nat.bodd ⋙ joinLeftUnder ((dual Nat.bodd).obj A) :=
  NatIso.ofComponents (fun X ↦ Under.isoMk (joinDualIso X A)
      (dual_map_joinInclRight_comp_joinDualIso_hom X A))
    fun f ↦ Under.UnderMorphism.ext (joinDualIso_naturality_left f A)

end Atoms.Diagrammatic
