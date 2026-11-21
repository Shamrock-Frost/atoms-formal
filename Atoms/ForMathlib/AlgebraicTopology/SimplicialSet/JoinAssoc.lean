import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Join

open CategoryTheory MonoidalCategory Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution

universe u

namespace SSet

open AugmentedSimplexCategory (inclusion)

private noncomputable def dayConvolutionMapIso {P P' Q Q' : AugmentedSimplexCategoryᵒᵖ ⥤ Type u}
    (e : P ≅ P') (e' : Q ≅ Q') : P ⊛ Q ≅ P' ⊛ Q' where
  hom := DayConvolution.map e.hom e'.hom
  inv := DayConvolution.map e.inv e'.inv
  hom_inv_id := by
    rw [← DayConvolution.map_comp, e.hom_inv_id, e'.hom_inv_id, DayConvolution.map_id]
  inv_hom_id := by
    rw [← DayConvolution.map_comp, e.inv_hom_id, e'.inv_hom_id, DayConvolution.map_id]

private def trivialAugmentationIsoOfUnique (P : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)
    [Unique (P.obj (op .star))] : trivialAugmentation.obj (inclusion.op ⋙ P) ≅ P :=
  NatIso.ofComponents
    (fun ⟨x⟩ ↦ match x with
      | .of _ => Iso.refl _
      | .star => (Equiv.ofUnique PUnit (P.obj (op .star))).toIso)
    (by
      rintro ⟨x⟩ ⟨y⟩ ⟨g⟩
      cases x <;> cases y
      · rfl
      · ext a
        exact Subsingleton.elim _ _
      · exact (WithInitial.false_of_to_star g).elim
      · ext a
        exact Subsingleton.elim _ _)

private lemma map_tensorHom_unit_app (P Q : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)
    {x x' y y' : AugmentedSimplexCategoryᵒᵖ} (f : x ⟶ x') (g : y ⟶ y') (a : P.obj x)
    (b : Q.obj y) :
    (P ⊛ Q).map (f ⊗ₘ g) ((DayConvolution.unit P Q).app (x, y) ((a, b) : P.obj x × Q.obj y)) =
      (DayConvolution.unit P Q).app (x', y') ((P.map f a, Q.map g b) : P.obj x' × Q.obj y') :=
  (NatTrans.naturality_apply (DayConvolution.unit P Q) (X := (x, y)) (Y := (x', y')) (f, g)
    ((a, b) : P.obj x × Q.obj y)).symm

private noncomputable instance uniqueDayConvolutionObjStar
    (P Q : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) [Unique (P.obj (op .star))]
    [Unique (Q.obj (op .star))] : Unique ((P ⊛ Q).obj (op .star)) where
  default := (DayConvolution.unit P Q).app (op .star, op .star)
      ((default, default) : P.obj (op .star) × Q.obj (op .star))
  uniq t := by
    obtain ⟨x, y, v, a, b, rfl⟩ := DayConvolution.map_unit_app_jointly_surjective P Q t
    obtain rfl : v = (((WithInitial.starInitial.to x.unop).op : x ⟶ op .star) ⊗ₘ
        ((WithInitial.starInitial.to y.unop).op : y ⟶ op .star)) :=
      Quiver.Hom.unop_inj (WithInitial.starInitial.hom_ext _ _)
    exact (map_tensorHom_unit_app P Q _ _ a b).trans
      (congrArg _ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))

private noncomputable def trivialAugmentationJoinIso (X Y : SSet.{u}) :
    trivialAugmentation.obj (join X Y) ≅ trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y :=
  trivialAugmentationIsoOfUnique _

private lemma trivialAugmentation_map_joinMap_comp_trivialAugmentationJoinIso_hom
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    trivialAugmentation.map (joinMap f g) ≫ (trivialAugmentationJoinIso X' Y').hom =
      (trivialAugmentationJoinIso X Y).hom ≫
        DayConvolution.map (trivialAugmentation.map f) (trivialAugmentation.map g) := by
  ext ⟨x⟩ a
  cases x with
  | of _ => rfl
  | star => exact Subsingleton.elim (α := (trivialAugmentation.obj X' ⊛
      trivialAugmentation.obj Y').obj (op .star)) _ _

private noncomputable def joinAssocAug (X Y Z : SSet.{u}) :
    trivialAugmentation.obj (join X Y) ⊛ trivialAugmentation.obj Z ≅
      trivialAugmentation.obj X ⊛ trivialAugmentation.obj (join Y Z) :=
  dayConvolutionMapIso (trivialAugmentationJoinIso X Y) (Iso.refl _) ≪≫
    DayConvolution.associator _ _ _ ≪≫
      dayConvolutionMapIso (Iso.refl _) (trivialAugmentationJoinIso Y Z).symm

noncomputable def joinAssoc (X Y Z : SSet.{u}) : join (join X Y) Z ≅ join X (join Y Z) :=
  Functor.isoWhiskerLeft inclusion.op (joinAssocAug X Y Z)

private lemma joinAssocAug_hom_app_unit {X Y Z : SSet.{u}} (a b c : AugmentedSimplexCategory)
    (x : (trivialAugmentation.obj X).obj (op a)) (y : (trivialAugmentation.obj Y).obj (op b))
    (z : (trivialAugmentation.obj Z).obj (op c))
    (s : (trivialAugmentation.obj (join X Y)).obj (op (a ⊗ b)))
    (hs : (trivialAugmentationJoinIso X Y).hom.app _ s =
      (DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj Y)).app
        (op a, op b) ((x, y) : _ × _))
    (t : (trivialAugmentation.obj (join Y Z)).obj (op (b ⊗ c)))
    (ht : (trivialAugmentationJoinIso Y Z).hom.app _ t =
      (DayConvolution.unit (trivialAugmentation.obj Y) (trivialAugmentation.obj Z)).app
        (op b, op c) ((y, z) : _ × _)) :
    (joinAssocAug X Y Z).hom.app (op ((a ⊗ b) ⊗ c))
        ((DayConvolution.unit (trivialAugmentation.obj (join X Y)) (trivialAugmentation.obj Z)).app
          (op (a ⊗ b), op c) ((s, z) : _ × _)) =
      (trivialAugmentation.obj X ⊛ trivialAugmentation.obj (join Y Z)).map
        (α_ (op a) (op b) (op c)).inv
        ((DayConvolution.unit (trivialAugmentation.obj X) (trivialAugmentation.obj (join Y Z))).app
          (op a, op (b ⊗ c)) ((x, t) : _ × _)) := by
  have h1 := ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (trivialAugmentationJoinIso X Y).hom
    (Iso.refl (trivialAugmentation.obj Z)).hom (op (a ⊗ b)) (op c)) ((s, z) : _ × _)
  have h2 := ConcreteCategory.congr_hom (DayConvolution.associator_hom_unit_unit
    (trivialAugmentation.obj X) (trivialAugmentation.obj Y) (trivialAugmentation.obj Z)
    (op a) (op b) (op c)) (((x, y), z) : _)
  have h3 := ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (Iso.refl (trivialAugmentation.obj X)).hom
    (trivialAugmentationJoinIso Y Z).inv
    (op a) (op (b ⊗ c))) ((x, (DayConvolution.unit (trivialAugmentation.obj Y)
      (trivialAugmentation.obj Z)).app (op b, op c) ((y, z) : _ × _)) : _ × _)
  have h4 : (trivialAugmentationJoinIso Y Z).inv.app _
        ((DayConvolution.unit (trivialAugmentation.obj Y) (trivialAugmentation.obj Z)).app
          (op b, op c) ((y, z) : _ × _)) = t := by
    rw [← ht]
    exact ConcreteCategory.congr_hom ((trivialAugmentationJoinIso Y Z).hom_inv_id_app _) t
  refine (congrArg (fun w ↦ (DayConvolution.map (Iso.refl (trivialAugmentation.obj X)).hom
    (trivialAugmentationJoinIso Y Z).inv).app _
      ((DayConvolution.associator (trivialAugmentation.obj X) (trivialAugmentation.obj Y)
        (trivialAugmentation.obj Z)).hom.app (op ((a ⊗ b) ⊗ c)) w))
    (h1.trans (congrArg (fun w ↦ (DayConvolution.unit
      (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y) (trivialAugmentation.obj Z)).app
        (op (a ⊗ b), op c) ((w, z) : _ × _)) hs))).trans ?_
  refine (congrArg _ h2).trans ((NatTrans.naturality_apply _ _ _).trans (congrArg _ ?_))
  exact h3.trans (congrArg (fun w ↦ (DayConvolution.unit (trivialAugmentation.obj X)
    (trivialAugmentation.obj (join Y Z))).app (op a, op (b ⊗ c)) ((x, w) : _ × _)) h4)

@[reassoc]
theorem joinInclLeft_comp_joinInclLeft_comp_joinAssoc_hom (X Y Z : SSet.{u}) :
    joinInclLeft X Y ≫ joinInclLeft (join X Y) Z ≫ (joinAssoc X Y Z).hom =
      joinInclLeft X (join Y Z) := by
  ext n x
  exact (joinAssocAug_hom_app_unit (X := X) (Y := Y) (Z := Z) (.of n.unop) .star .star x
    (default : (trivialAugmentation.obj Y).obj (op .star))
    (default : (trivialAugmentation.obj Z).obj (op .star)) _ rfl
    (default : (trivialAugmentation.obj (join Y Z)).obj (op .star))
    (Subsingleton.elim (α := (trivialAugmentation.obj Y ⊛ trivialAugmentation.obj Z).obj
      (op .star)) _ _)).trans (Functor.map_id_apply _ _ _)

@[reassoc]
theorem joinInclRight_comp_joinAssoc_hom (X Y Z : SSet.{u}) :
    joinInclRight (join X Y) Z ≫ (joinAssoc X Y Z).hom =
      joinInclRight Y Z ≫ joinInclRight X (join Y Z) := by
  ext n z
  exact (joinAssocAug_hom_app_unit (X := X) (Y := Y) (Z := Z) .star .star (.of n.unop)
    (default : (trivialAugmentation.obj X).obj (op .star))
    (default : (trivialAugmentation.obj Y).obj (op .star)) z
    (default : (trivialAugmentation.obj (join X Y)).obj (op .star))
    (Subsingleton.elim (α := (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y).obj
      (op .star)) _ _) _ rfl).trans (Functor.map_id_apply _ _ _)

private lemma join_hom_ext {Y Z W : SSet.{u}} {f g : join Y Z ⟶ W}
    (hl : joinInclLeft Y Z ≫ f = joinInclLeft Y Z ≫ g)
    (hr : joinInclRight Y Z ≫ f = joinInclRight Y Z ≫ g)
    (h : ∀ (a b : SimplexCategory) (y : Y.obj (op a)) (z : Z.obj (op b)),
      f.app (op (AugmentedSimplexCategory.tensorObjOf a b))
          ((DayConvolution.unit (trivialAugmentation.obj Y) (trivialAugmentation.obj Z)).app
            (op (.of a), op (.of b)) ((y, z) : _ × _)) =
        g.app (op (AugmentedSimplexCategory.tensorObjOf a b))
          ((DayConvolution.unit (trivialAugmentation.obj Y) (trivialAugmentation.obj Z)).app
            (op (.of a), op (.of b)) ((y, z) : _ × _))) :
    f = g := by
  let P := trivialAugmentation.obj Y ⊛ trivialAugmentation.obj Z
  ext ⟨n⟩ t
  obtain ⟨⟨⟨⟨a, b⟩, hab⟩, y, z⟩, rfl⟩ :=
    (AugmentedSimplexCategory.bijective_map_unit_app _ _ (.of n)).2 t
  cases a with
  | star =>
    cases b with
    | star => cases hab
    | of b =>
      obtain rfl : b = n := WithInitial.of.inj hab
      obtain rfl := Subsingleton.elim (α := (trivialAugmentation.obj Y).obj (op .star)) y default
      exact (congrArg (f.app _) (Functor.map_id_apply P _ _)).trans
        ((ConcreteCategory.congr_hom (congr_app hr (op b)) z).trans
          (congrArg (g.app _) (Functor.map_id_apply P _ _).symm))
  | of a =>
    cases b with
    | star =>
      obtain rfl : a = n := WithInitial.of.inj hab
      obtain rfl := Subsingleton.elim (α := (trivialAugmentation.obj Z).obj (op .star)) z default
      exact (congrArg (f.app _) (Functor.map_id_apply P _ _)).trans
        ((ConcreteCategory.congr_hom (congr_app hl (op a)) y).trans
          (congrArg (g.app _) (Functor.map_id_apply P _ _).symm))
    | of b =>
      obtain rfl : AugmentedSimplexCategory.tensorObjOf a b = n := WithInitial.of.inj hab
      exact (congrArg (f.app _) (Functor.map_id_apply P _ _)).trans
        ((h a b y z).trans (congrArg (g.app _) (Functor.map_id_apply P _ _).symm))

@[reassoc]
theorem joinMap_joinInclRight_comp_joinAssoc_hom (X Y Z : SSet.{u}) :
    joinMap (joinInclRight X Y) (𝟙 Z) ≫ (joinAssoc X Y Z).hom = joinInclRight X (join Y Z) := by
  refine join_hom_ext ?_ ?_ fun a b y z ↦ ?_
  · rw [joinInclLeft_comp_joinMap_assoc]
    ext n y
    exact (joinAssocAug_hom_app_unit (X := X) (Y := Y) (Z := Z) .star (.of n.unop) .star
      (default : (trivialAugmentation.obj X).obj (op .star)) y
      (default : (trivialAugmentation.obj Z).obj (op .star)) _ rfl _ rfl).trans
      (Functor.map_id_apply _ _ _)
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_joinAssoc_hom]
  · exact (congrArg ((joinAssoc X Y Z).hom.app _) (ConcreteCategory.congr_hom
      (DayConvolution.unit_app_map_app (trivialAugmentation.map (joinInclRight X Y))
        (trivialAugmentation.map (𝟙 Z)) (op (.of a)) (op (.of b))) ((y, z) : _ × _))).trans
      ((joinAssocAug_hom_app_unit (X := X) (Y := Y) (Z := Z) .star (.of a) (.of b)
        (default : (trivialAugmentation.obj X).obj (op .star)) y z _ rfl _ rfl).trans
        (Functor.map_id_apply _ _ _))

@[reassoc]
theorem joinMap_joinInclLeft_comp_joinAssoc_hom (X Y Z : SSet.{u}) :
    joinMap (joinInclLeft X Y) (𝟙 Z) ≫ (joinAssoc X Y Z).hom =
      joinMap (𝟙 X) (joinInclRight Y Z) := by
  refine join_hom_ext ?_ ?_ fun a b x z ↦ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_joinInclLeft_comp_joinAssoc_hom,
      joinInclLeft_comp_joinMap, Category.id_comp]
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_joinAssoc_hom,
      joinInclRight_comp_joinMap]
  · exact (congrArg ((joinAssoc X Y Z).hom.app _) (ConcreteCategory.congr_hom
      (DayConvolution.unit_app_map_app (trivialAugmentation.map (joinInclLeft X Y))
        (trivialAugmentation.map (𝟙 Z)) (op (.of a)) (op (.of b))) ((x, z) : _ × _))).trans
      ((joinAssocAug_hom_app_unit (X := X) (Y := Y) (Z := Z) (.of a) .star (.of b) x
        (default : (trivialAugmentation.obj Y).obj (op .star)) z _ rfl _ rfl).trans
        ((Functor.map_id_apply _ _ _).trans (ConcreteCategory.congr_hom
          (DayConvolution.unit_app_map_app (trivialAugmentation.map (𝟙 X))
            (trivialAugmentation.map (joinInclRight Y Z)) (op (.of a)) (op (.of b)))
              ((x, z) : _ × _)).symm))

@[reassoc]
theorem joinMap_joinMap_comp_joinAssoc_hom {X X' Y Y' Z Z' : SSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') (h : Z ⟶ Z') :
    joinMap (joinMap f g) h ≫ (joinAssoc X' Y' Z').hom =
      (joinAssoc X Y Z).hom ≫ joinMap f (joinMap g h) := by
  have key : DayConvolution.map (trivialAugmentation.map (joinMap f g))
      (trivialAugmentation.map h) ≫ (joinAssocAug X' Y' Z').hom =
        (joinAssocAug X Y Z).hom ≫ DayConvolution.map (trivialAugmentation.map f)
          (trivialAugmentation.map (joinMap g h)) := by
    have h₁ := trivialAugmentation_map_joinMap_comp_trivialAugmentationJoinIso_hom f g
    have h₂ := (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
      (trivialAugmentation_map_joinMap_comp_trivialAugmentationJoinIso_hom g h)).trans
        (Category.assoc _ _ _))
    simp only [joinAssocAug, Iso.trans_hom, dayConvolutionMapIso, Iso.refl_hom, Iso.symm_hom,
      Category.assoc]
    rw [← reassoc_of% DayConvolution.map_comp, h₁, Category.comp_id,
      ← Category.id_comp (trivialAugmentation.map h), DayConvolution.map_comp, Category.assoc,
      reassoc_of% DayConvolution.associator_naturality, ← DayConvolution.map_comp,
      Category.comp_id, ← h₂, ← DayConvolution.map_comp, Category.id_comp]
  exact congrArg (Functor.whiskerLeft inclusion.op) key

end SSet
