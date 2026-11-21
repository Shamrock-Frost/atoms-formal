import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.Basic
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.Types
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.WithTerminal.Basic

open CategoryTheory MonoidalCategory Opposite Limits
open scoped MonoidalCategory.DayConvolution

universe w u v₁ u₁

namespace CategoryTheory.MonoidalCategory.DayConvolution

variable {C : Type w} [SmallCategory C]

@[ext]
structure NatFamily (B : C ⥤ C ⥤ C) (Q H : C ⥤ Type (max w u)) (x : C) : Type (max w u) where
  toFun (y : C) : Q.obj y → H.obj ((B.obj x).obj y)
  naturality {y y' : C} (g : y ⟶ y') (b : Q.obj y) :
    toFun y' (Q.map g b) = H.map ((B.obj x).map g) (toFun y b)

def natFamilies (B : C ⥤ C ⥤ C) (Q H : C ⥤ Type (max w u)) : C ⥤ Type (max w u) where
  obj x := NatFamily B Q H x
  map f := TypeCat.ofHom fun ψ ↦ ⟨fun y b ↦ H.map ((B.map f).app y) (ψ.toFun y b),
    fun g b ↦ by
      rw [ψ.naturality, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        NatTrans.naturality]⟩
  map_id x := by
    ext ψ y b
    simp
  map_comp f g := by
    ext ψ y b
    simp

def natFamiliesFunctor (B : C ⥤ C ⥤ C) (Q : C ⥤ Type (max w u)) :
    (C ⥤ Type (max w u)) ⥤ (C ⥤ Type (max w u)) where
  obj H := natFamilies B Q H
  map α :=
    { app x := TypeCat.ofHom fun ψ ↦ ⟨fun y b ↦ α.app _ (ψ.toFun y b), fun g b ↦ by
        rw [ψ.naturality, NatTrans.naturality_apply]⟩
      naturality x x' f := by
        ext ψ
        refine NatFamily.ext (funext fun y ↦ funext fun b ↦ ?_)
        exact NatTrans.naturality_apply α _ _ }

variable [MonoidalCategory C] [∀ P Q : C ⥤ Type (max w u), DayConvolution P Q]

noncomputable def convolutionLeft (Q : C ⥤ Type (max w u)) :
    (C ⥤ Type (max w u)) ⥤ (C ⥤ Type (max w u)) where
  obj P := P ⊛ Q
  map f := DayConvolution.map f (𝟙 Q)
  map_id P := DayConvolution.map_id P Q
  map_comp f g := by
    rw [← DayConvolution.map_comp, Category.comp_id]

private lemma map_unit_app_apply {P P' Q Q' : C ⥤ Type (max w u)} (f : P ⟶ P') (g : Q ⟶ Q')
    (x y : C)
    (a : P.obj x) (b : Q.obj y) :
    (DayConvolution.map f g).app (x ⊗ y) ((DayConvolution.unit P Q).app (x, y) (a, b)) =
      (DayConvolution.unit P' Q').app (x, y) (f.app x a, g.app y b) :=
  ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app f g x y) ((a, b) : P.obj x × Q.obj y)

private lemma homEquiv_map_comp_apply {P P' Q Q' H : C ⥤ Type (max w u)} (f : P ⟶ P')
    (g : Q ⟶ Q')
    (k : P' ⊛ Q' ⟶ H) (x y : C) (a : P.obj x) (b : Q.obj y) :
    (DayConvolution.homEquiv P Q H (DayConvolution.map f g ≫ k)).1 x y a b =
      (DayConvolution.homEquiv P' Q' H k).1 x y (f.app x a) (g.app y b) := by
  rw [DayConvolution.homEquiv_apply, DayConvolution.homEquiv_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, map_unit_app_apply]

noncomputable def convolutionRight (Q : C ⥤ Type (max w u)) :
    (C ⥤ Type (max w u)) ⥤ (C ⥤ Type (max w u)) where
  obj P := Q ⊛ P
  map f := DayConvolution.map (𝟙 Q) f
  map_id P := DayConvolution.map_id Q P
  map_comp f g := by
    rw [← DayConvolution.map_comp, Category.comp_id]

noncomputable def convolutionLeftAdjunction (Q : C ⥤ Type (max w u)) :
    convolutionLeft Q ⊣ natFamiliesFunctor (curriedTensor C) Q :=
  Adjunction.mkOfHomEquiv
    { homEquiv P H := (DayConvolution.homEquiv P Q H).trans
        { toFun φ :=
            { app x := TypeCat.ofHom fun a ↦ ⟨fun y b ↦ φ.1 x y a b, fun g b ↦ by
                have := φ.2 (𝟙 x) g a b
                rwa [Functor.map_id_apply, id_tensorHom] at this⟩
              naturality x x' f := by
                ext a
                refine NatFamily.ext (funext fun y ↦ funext fun b ↦ ?_)
                have := φ.2 f (𝟙 y) a b
                rw [Functor.map_id_apply, tensorHom_id] at this
                exact this }
          invFun α := ⟨fun x y a b ↦ (α.app x a).toFun y b, fun {x x' y y'} f g a b ↦
            calc (α.app x' (P.map f a)).toFun y' (Q.map g b)
                _ = H.map (f ▷ y') ((α.app x a).toFun y' (Q.map g b)) :=
                  congrArg (fun ψ ↦ NatFamily.toFun ψ y' (Q.map g b))
                    (NatTrans.naturality_apply α f a)
                _ = H.map (f ▷ y') (H.map (x ◁ g) ((α.app x a).toFun y b)) :=
                  congrArg (H.map (f ▷ y')) ((α.app x a).naturality g b)
                _ = H.map (f ⊗ₘ g) ((α.app x a).toFun y b) := by
                  rw [← Functor.map_comp_apply, tensorHom_def']⟩
          left_inv φ := rfl
          right_inv α := rfl }
      homEquiv_naturality_left_symm {P P' H} f g := by
        refine (Equiv.symm_apply_eq _).2 ?_
        ext x a
        refine NatFamily.ext (funext fun y ↦ funext fun b ↦ ?_)
        exact ((homEquiv_map_comp_apply f (𝟙 Q) _ x y a b).trans (congrArg
          (fun φ ↦ φ.1 x y (f.app x a) b)
          ((DayConvolution.homEquiv P' Q H).apply_symm_apply _))).symm
      homEquiv_naturality_right f g := rfl }

noncomputable def convolutionRightAdjunction (Q : C ⥤ Type (max w u)) :
    convolutionRight Q ⊣ natFamiliesFunctor (curriedTensor C).flip Q :=
  Adjunction.mkOfHomEquiv
    { homEquiv P H := (DayConvolution.homEquiv Q P H).trans
        { toFun φ :=
            { app x := TypeCat.ofHom fun a ↦ ⟨fun y b ↦ φ.1 y x b a, fun g b ↦ by
                have := φ.2 g (𝟙 x) b a
                rwa [Functor.map_id_apply, tensorHom_id] at this⟩
              naturality x x' f := by
                ext a
                refine NatFamily.ext (funext fun y ↦ funext fun b ↦ ?_)
                have := φ.2 (𝟙 y) f b a
                rw [Functor.map_id_apply, id_tensorHom] at this
                exact this }
          invFun α := ⟨fun x y b a ↦ (α.app y a).toFun x b, fun {x x' y y'} f g b a ↦
            calc (α.app y' (P.map g a)).toFun x' (Q.map f b)
                _ = H.map (x' ◁ g) ((α.app y a).toFun x' (Q.map f b)) :=
                  congrArg (fun ψ ↦ NatFamily.toFun ψ x' (Q.map f b))
                    (NatTrans.naturality_apply α g a)
                _ = H.map (x' ◁ g) (H.map (f ▷ y) ((α.app y a).toFun x b)) :=
                  congrArg (H.map (x' ◁ g)) ((α.app y a).naturality f b)
                _ = H.map (f ⊗ₘ g) ((α.app y a).toFun x b) := by
                  rw [← Functor.map_comp_apply, tensorHom_def]⟩
          left_inv φ := rfl
          right_inv α := rfl }
      homEquiv_naturality_left_symm {P P' H} f g := by
        refine (Equiv.symm_apply_eq _).2 ?_
        ext x a
        refine NatFamily.ext (funext fun y ↦ funext fun b ↦ ?_)
        exact ((homEquiv_map_comp_apply (𝟙 Q) f _ y x b a).trans (congrArg
          (fun φ ↦ φ.1 y x b (f.app x a))
          ((DayConvolution.homEquiv Q P' H).apply_symm_apply _))).symm
      homEquiv_naturality_right f g := rfl }

section Representable

variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] (a b : D)
  [DayConvolution (uliftYoneda.{w}.obj a) (uliftYoneda.{w}.obj b)]

private noncomputable def uliftYonedaTensorHom :
    uliftYoneda.{w}.obj a ⊛ uliftYoneda.{w}.obj b ⟶ uliftYoneda.{w}.obj (a ⊗ b) :=
  (homEquiv _ _ _).symm ⟨fun _ _ f g ↦ ULift.up (f.down ⊗ₘ g.down), fun _ _ _ _ ↦
    congrArg ULift.up (tensorHom_comp_tensorHom _ _ _ _).symm⟩

private def uliftYonedaTensorInv :
    uliftYoneda.{w}.obj (a ⊗ b) ⟶ uliftYoneda.{w}.obj a ⊛ uliftYoneda.{w}.obj b :=
  uliftYonedaEquiv.symm ((unit (uliftYoneda.{w}.obj a) (uliftYoneda.{w}.obj b)).app (op a, op b)
    ((ULift.up (𝟙 a), ULift.up (𝟙 b)) : _ × _))

noncomputable def uliftYonedaIso :
    uliftYoneda.{w}.obj a ⊛ uliftYoneda.{w}.obj b ≅ uliftYoneda.{w}.obj (a ⊗ b) where
  hom := uliftYonedaTensorHom a b
  inv := uliftYonedaTensorInv a b
  hom_inv_id := by
    refine (homEquiv _ _ _).injective (Subtype.ext ?_)
    funext x y f g
    rw [homEquiv_apply, homEquiv_apply, NatTrans.comp_app, ConcreteCategory.comp_apply,
      uliftYonedaTensorHom, homEquiv_symm_app_unit_app, NatTrans.id_app,
      ConcreteCategory.id_apply]
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    refine (NatTrans.naturality_apply (unit (uliftYoneda.{w}.obj a) (uliftYoneda.{w}.obj b))
      (X := (op a, op b)) (Y := (x, y)) (f.op, g.op) _).symm.trans
      (congrArg _ (Prod.ext (congrArg ULift.up (Category.comp_id f))
        (congrArg ULift.up (Category.comp_id g))))
  inv_hom_id := by
    refine uliftYonedaEquiv.injective ?_
    rw [uliftYonedaEquiv_comp, uliftYonedaTensorInv, Equiv.apply_symm_apply]
    exact (homEquiv_symm_app_unit_app _ _ _ _ (op a) (op b) _ _).trans
      (congrArg ULift.up (id_tensorHom_id a b))

theorem uliftYonedaIso_hom_app_unit_app {x y : Dᵒᵖ} (f : x.unop ⟶ a) (g : y.unop ⟶ b) :
    (uliftYonedaIso a b).hom.app (x ⊗ y)
        ((unit (uliftYoneda.{w}.obj a) (uliftYoneda.{w}.obj b)).app (x, y)
          ((ULift.up f, ULift.up g) : _ × _)) =
      ULift.up (f ⊗ₘ g) :=
  homEquiv_symm_app_unit_app _ _ _ _ x y _ _

end Representable

@[reassoc]
theorem map_uliftYoneda_map_comp_uliftYonedaIso_hom {D : Type u₁} [Category.{v₁} D]
    [MonoidalCategory D] {a a' b b' : D} (f : a ⟶ a') (g : b ⟶ b')
    [DayConvolution (uliftYoneda.{w}.obj a) (uliftYoneda.{w}.obj b)]
    [DayConvolution (uliftYoneda.{w}.obj a') (uliftYoneda.{w}.obj b')] :
    map (uliftYoneda.{w}.map f) (uliftYoneda.{w}.map g) ≫ (uliftYonedaIso a' b').hom =
      (uliftYonedaIso a b).hom ≫ uliftYoneda.map (f ⊗ₘ g) := by
  refine (homEquiv _ _ _).injective (Subtype.ext ?_)
  funext x y f' g'
  have h := ConcreteCategory.congr_hom (unit_app_map_app (uliftYoneda.{w}.map f)
    (uliftYoneda.{w}.map g) x y) ((f', g') : _ × _)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [homEquiv_apply, homEquiv_apply, NatTrans.comp_app, NatTrans.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]
  exact (uliftYonedaIso_hom_app_unit_app a' b' (f'.down ≫ f) (g'.down ≫ g)).trans
    ((congrArg ULift.up (tensorHom_comp_tensorHom _ _ _ _).symm).trans
      (congrArg ((uliftYoneda.{w}.map (f ⊗ₘ g)).app (x ⊗ y))
        (uliftYonedaIso_hom_app_unit_app a b f'.down g'.down)).symm)

end CategoryTheory.MonoidalCategory.DayConvolution

namespace CategoryTheory.WithInitial

private lemma map_tensorHom_unit_app {D : Type*} [Category* D] [MonoidalCategory D]
    (P Q : D ⥤ Type u) [DayConvolution P Q] {x x' y y' : D} (f : x ⟶ x') (g : y ⟶ y')
    (a : P.obj x) (b : Q.obj y) :
    (P ⊛ Q).map (f ⊗ₘ g)
        ((DayConvolution.unit P Q).app (x, y) ((a, b) : P.obj x × Q.obj y)) =
      (DayConvolution.unit P Q).app (x', y') ((P.map f a, Q.map g b) : P.obj x' × Q.obj y') :=
  (NatTrans.naturality_apply (DayConvolution.unit P Q) (X := (x, y)) (Y := (x', y')) (f, g)
    ((a, b) : P.obj x × Q.obj y)).symm

private noncomputable def dayConvolutionMapIso {D : Type*} [Category* D]
    [MonoidalCategory D] {P P' Q Q' : D ⥤ Type u} [DayConvolution P Q]
    [DayConvolution P' Q'] (e : P ≅ P') (e' : Q ≅ Q') : P ⊛ Q ≅ P' ⊛ Q' where
  hom := DayConvolution.map e.hom e'.hom
  inv := DayConvolution.map e.inv e'.inv
  hom_inv_id := by
    rw [← DayConvolution.map_comp, e.hom_inv_id, e'.hom_inv_id, DayConvolution.map_id]
  inv_hom_id := by
    rw [← DayConvolution.map_comp, e.inv_hom_id, e'.inv_hom_id, DayConvolution.map_id]

variable {C : Type w} [SmallCategory C]

def trivialAugmentation :
    (Cᵒᵖ ⥤ Type (max w u)) ⥤ ((WithInitial C)ᵒᵖ ⥤ Type (max w u)) where
  obj X := (opEquiv C).functor ⋙ WithTerminal.liftToTerminal X Types.isTerminalPUnit
  map {X Y} f :=
    { app := fun ⟨x⟩ ↦ match x with
        | of c => f.app (op c)
        | star => 𝟙 _
      naturality := by
        rintro ⟨x⟩ ⟨y⟩ ⟨g⟩
        cases x <;> cases y
        · exact f.naturality _
        · rfl
        · exact (false_of_to_star g).elim
        · rfl }
  map_id X := by
    ext ⟨x⟩ a
    cases x <;> rfl
  map_comp f g := by
    ext ⟨x⟩ a
    cases x <;> rfl

def trivialAugmentationCompIso :
    trivialAugmentation.{w, u} ⋙ (Functor.whiskeringLeft _ _ _).obj (incl.op : Cᵒᵖ ⥤ _) ≅
      𝟭 _ :=
  Iso.refl _

instance (X : Cᵒᵖ ⥤ Type (max w u)) : Unique ((trivialAugmentation.obj X).obj (op star)) :=
  inferInstanceAs (Unique PUnit)

instance (K : Type (max w u)) [Category.{max w u} K] [IsConnected K] :
    PreservesColimitsOfShape K (trivialAugmentation.{w, u} (C := C)) := by
  apply preservesColimitsOfShape_of_evaluation
  rintro ⟨c⟩
  cases c with
  | of k =>
    exact preservesColimitsOfShape_of_natIso (F := (evaluation _ (Type (max w u))).obj (op k))
      (NatIso.ofComponents (fun X ↦ Iso.refl _) (fun f ↦ rfl))
  | star =>
    refine ⟨fun {F} ↦ ⟨fun {c} _ ↦ ⟨?_⟩⟩⟩
    let φ : F ⋙ trivialAugmentation ⋙ (evaluation _ (Type (max w u))).obj (op star) ≅
        Types.constPUnitFunctor.{max w u} K :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
        ext x
        rfl)
    refine IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv φ _).symm (Types.isColimitPUnitCocone K))
      (Cocone.ext (Iso.refl _) (fun j ↦ ?_))
    ext x
    rfl

def trivialAugmentationIsoOfUnique (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    [Unique (P.obj (op star))] : trivialAugmentation.obj (incl.op ⋙ P) ≅ P :=
  NatIso.ofComponents
    (fun ⟨x⟩ ↦ match x with
      | of c => Iso.refl _
      | star => (Equiv.ofUnique PUnit (P.obj (op star))).toIso)
    (by
      rintro ⟨x⟩ ⟨y⟩ ⟨g⟩
      cases x <;> cases y
      · rfl
      · ext a
        exact Subsingleton.elim _ _
      · exact (false_of_to_star g).elim
      · ext a
        exact Subsingleton.elim _ _)

def trivialAugmentationULiftYonedaIso (c : C) :
    trivialAugmentation.obj (uliftYoneda.{u}.obj c) ≅ uliftYoneda.{u}.obj (of c) :=
  have : Unique ((uliftYoneda.{u}.obj (of c)).obj (op star)) :=
    inferInstanceAs (Unique (ULift PUnit))
  trivialAugmentationIsoOfUnique (uliftYoneda.{u}.obj (of c))

private lemma trivialAugmentation_map_comp_trivialAugmentationULiftYonedaIso_hom {c c' : C}
    (f : c ⟶ c') :
    trivialAugmentation.map (uliftYoneda.{u}.map f) ≫
        (trivialAugmentationULiftYonedaIso.{w, u} c').hom =
      (trivialAugmentationULiftYonedaIso c).hom ≫
        uliftYoneda.{u}.map (incl.map f : of c ⟶ of c') := by
  ext ⟨x⟩ a
  cases x with
  | of _ => rfl
  | star => exact Subsingleton.elim (α := ULift (star ⟶ of c')) _ _

section Monoidal

variable [MonoidalCategory (WithInitial C)]

variable (C) in
class TensorUnitIsStar : Prop where
  tensorUnit_eq : 𝟙_ (WithInitial C) = star

private def toTensorUnit (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    ∀ y : (WithInitial C)ᵒᵖ,
      (trivialAugmentation.obj Y).obj y → (y.unop ⟶ 𝟙_ (WithInitial C))
  | op star, _ => starInitial.to _
  | op (of c), b => isEmptyElim (α := Y.obj (op c)) b

private lemma toTensorUnit_map (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)]
    {y y' : (WithInitial C)ᵒᵖ} (g : y ⟶ y') (b : (trivialAugmentation.obj Y).obj y) :
    toTensorUnit Y y' ((trivialAugmentation.obj Y).map g b) = g.unop ≫ toTensorUnit Y y b := by
  obtain ⟨y'⟩ := y'
  cases y' with
  | star => exact starInitial.hom_ext _ _
  | of c => exact isEmptyElim (α := Y.obj (op c)) ((trivialAugmentation.obj Y).map g b)

section TensorUnitIsStar

variable [TensorUnitIsStar C]

private def isInitialTensorUnit : IsInitial (𝟙_ (WithInitial C)) :=
  starInitial.ofIso (eqToIso TensorUnitIsStar.tensorUnit_eq.symm)

private def toTensorStar (d : WithInitial C) : d ⟶ d ⊗ star :=
  (ρ_ d).inv ≫ d ◁ isInitialTensorUnit.to star

private def toStarTensor (d : WithInitial C) : d ⟶ star ⊗ d :=
  (λ_ d).inv ≫ isInitialTensorUnit.to star ▷ d

private lemma toTensorStar_naturality {d d' : WithInitial C} (f : d ⟶ d') :
    f ≫ toTensorStar d' = toTensorStar d ≫ f ▷ star := by
  simp only [toTensorStar, Category.assoc, ← whisker_exchange, rightUnitor_inv_naturality_assoc]

private lemma toStarTensor_naturality {d d' : WithInitial C} (f : d ⟶ d') :
    f ≫ toStarTensor d' = toStarTensor d ≫ star ◁ f := by
  simp only [toStarTensor, Category.assoc, whisker_exchange, leftUnitor_inv_naturality_assoc]

end TensorUnitIsStar

variable [∀ P Q : (WithInitial C)ᵒᵖ ⥤ Type (max w u), DayConvolution P Q]

def join (X Y : Cᵒᵖ ⥤ Type (max w u)) : Cᵒᵖ ⥤ Type (max w u) :=
  incl.op ⋙ (trivialAugmentation.obj X ⊛ trivialAugmentation.obj Y)

noncomputable def joinMap {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (f : X ⟶ X') (g : Y ⟶ Y') :
    join X Y ⟶ join X' Y' :=
  Functor.whiskerLeft _ (DayConvolution.map (trivialAugmentation.map f) (trivialAugmentation.map g))

noncomputable def joinFunctor :
    (Cᵒᵖ ⥤ Type (max w u)) × (Cᵒᵖ ⥤ Type (max w u)) ⥤
      (Cᵒᵖ ⥤ Type (max w u)) where
  obj p := join p.1 p.2
  map f := joinMap f.1 f.2
  map_id p := by
    have h : DayConvolution.map (trivialAugmentation.map (𝟙 p.1))
        (trivialAugmentation.map (𝟙 p.2)) = 𝟙 _ := by
      rw [trivialAugmentation.map_id, trivialAugmentation.map_id, DayConvolution.map_id]
    exact congrArg (Functor.whiskerLeft _) h
  map_comp f g := by
    have h : DayConvolution.map (trivialAugmentation.map (f.1 ≫ g.1))
        (trivialAugmentation.map (f.2 ≫ g.2)) = DayConvolution.map
          (trivialAugmentation.map f.1) (trivialAugmentation.map f.2) ≫ DayConvolution.map
          (trivialAugmentation.map g.1) (trivialAugmentation.map g.2) := by
      rw [trivialAugmentation.map_comp, trivialAugmentation.map_comp, DayConvolution.map_comp]
    exact congrArg (Functor.whiskerLeft _) h

@[reassoc]
theorem joinMap_comp_joinMap {X X' X'' Y Y' Y'' : Cᵒᵖ ⥤ Type (max w u)} (f : X ⟶ X')
    (g : Y ⟶ Y') (f' : X' ⟶ X'') (g' : Y' ⟶ Y'') :
    joinMap f g ≫ joinMap f' g' = joinMap (f ≫ f') (g ≫ g') :=
  (joinFunctor.map_comp (X := (X, Y)) (Y := (X', Y')) (Z := (X'', Y'')) (f, g) (f', g')).symm

@[reassoc]
theorem joinMap_exchange {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (f : X ⟶ X') (g : Y ⟶ Y') :
    joinMap (𝟙 X) g ≫ joinMap f (𝟙 Y') =
      joinMap f (𝟙 Y) ≫ joinMap (𝟙 X') g := by
  rw [joinMap_comp_joinMap, joinMap_comp_joinMap, Category.id_comp, Category.comp_id,
    Category.id_comp, Category.comp_id]

@[simp]
theorem joinMap_id (X Y : Cᵒᵖ ⥤ Type (max w u)) : joinMap (𝟙 X) (𝟙 Y) = 𝟙 (join X Y) :=
  joinFunctor.map_id (X, Y)

noncomputable def joinMapIso {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (e : X ≅ X') (e' : Y ≅ Y') :
    join X Y ≅ join X' Y' where
  hom := joinMap e.hom e'.hom
  inv := joinMap e.inv e'.inv
  hom_inv_id := by rw [joinMap_comp_joinMap, e.hom_inv_id, e'.hom_inv_id, joinMap_id]
  inv_hom_id := by rw [joinMap_comp_joinMap, e.inv_hom_id, e'.inv_hom_id, joinMap_id]

@[simp]
theorem joinMapIso_hom {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (e : X ≅ X') (e' : Y ≅ Y') :
    (joinMapIso e e').hom = joinMap e.hom e'.hom :=
  rfl

noncomputable instance uniqueDayConvolutionObjStar (P Q : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    [DayConvolution P Q] [Unique (P.obj (op star))] [Unique (Q.obj (op star))] :
    Unique ((P ⊛ Q).obj (op star)) where
  default := (P ⊛ Q).map (starInitial.to (star ⊗ star)).op
    ((DayConvolution.unit P Q).app (op star, op star)
      ((default, default) : P.obj (op star) × Q.obj (op star)))
  uniq t := by
    obtain ⟨x, y, v, a, b, rfl⟩ := DayConvolution.map_unit_app_jointly_surjective P Q t
    have hv : v = ((starInitial.to x.unop).op ⊗ₘ (starInitial.to y.unop).op) ≫
        (starInitial.to (star ⊗ star)).op :=
      Quiver.Hom.unop_inj (starInitial.hom_ext _ _)
    rw [hv, Functor.map_comp_apply, map_tensorHom_unit_app,
      Subsingleton.elim (P.map _ a) default, Subsingleton.elim (Q.map _ b) default]

noncomputable def joinAssoc (X Y Z : Cᵒᵖ ⥤ Type (max w u)) :
    join (join X Y) Z ≅ join X (join Y Z) :=
  Functor.isoWhiskerLeft incl.op
    (dayConvolutionMapIso (trivialAugmentationIsoOfUnique _) (Iso.refl _) ≪≫
      DayConvolution.associator _ _ _ ≪≫
        dayConvolutionMapIso (Iso.refl _) (trivialAugmentationIsoOfUnique _).symm)

noncomputable def joinULiftYonedaIso (a b : C) :
    join (uliftYoneda.{u}.obj a) (uliftYoneda.{u}.obj b) ≅
      incl.op ⋙ uliftYoneda.{u}.obj (of a ⊗ of b) :=
  Functor.isoWhiskerLeft incl.op
    (dayConvolutionMapIso (trivialAugmentationULiftYonedaIso a)
      (trivialAugmentationULiftYonedaIso b) ≪≫ DayConvolution.uliftYonedaIso (of a) (of b))

@[reassoc]
theorem joinMap_uliftYoneda_map_comp_joinULiftYonedaIso_hom {a a' b b' : C}
    (f : a ⟶ a') (g : b ⟶ b') :
    joinMap (uliftYoneda.{u}.map f) (uliftYoneda.{u}.map g) ≫ (joinULiftYonedaIso a' b').hom =
      (joinULiftYonedaIso a b).hom ≫
        Functor.whiskerLeft incl.op
          (uliftYoneda.{u}.map (incl.map f ⊗ₘ incl.map g : of a ⊗ of b ⟶ of a' ⊗ of b')) := by
  have key : DayConvolution.map (trivialAugmentation.map (uliftYoneda.{u}.map f))
      (trivialAugmentation.map (uliftYoneda.{u}.map g)) ≫
        (dayConvolutionMapIso (trivialAugmentationULiftYonedaIso a')
          (trivialAugmentationULiftYonedaIso b') ≪≫
            DayConvolution.uliftYonedaIso (of a') (of b')).hom =
      (dayConvolutionMapIso (trivialAugmentationULiftYonedaIso a)
          (trivialAugmentationULiftYonedaIso b) ≪≫
            DayConvolution.uliftYonedaIso (of a) (of b)).hom ≫
        uliftYoneda.{u}.map (incl.map f ⊗ₘ incl.map g : of a ⊗ of b ⟶ of a' ⊗ of b') := by
    dsimp only [dayConvolutionMapIso, Iso.trans_hom]
    let eA := trivialAugmentationULiftYonedaIso.{w, u} a
    let eB := trivialAugmentationULiftYonedaIso.{w, u} b
    let eA' := trivialAugmentationULiftYonedaIso.{w, u} a'
    let eB' := trivialAugmentationULiftYonedaIso.{w, u} b'
    let φ : uliftYoneda.{u}.obj (of a) ⟶ uliftYoneda.{u}.obj (of a') :=
      uliftYoneda.{u}.map (incl.map f : of a ⟶ of a')
    let ψ : uliftYoneda.{u}.obj (of b) ⟶ uliftYoneda.{u}.obj (of b') :=
      uliftYoneda.{u}.map (incl.map g : of b ⟶ of b')
    calc _ = DayConvolution.map (trivialAugmentation.map (uliftYoneda.{u}.map f) ≫ eA'.hom)
          (trivialAugmentation.map (uliftYoneda.{u}.map g) ≫ eB'.hom) ≫
            (DayConvolution.uliftYonedaIso (of a') (of b')).hom := by
          rw [DayConvolution.map_comp, Category.assoc]
      _ = DayConvolution.map (eA.hom ≫ φ) (eB.hom ≫ ψ) ≫
            (DayConvolution.uliftYonedaIso (of a') (of b')).hom :=
          congrArg₂ (fun x y ↦ DayConvolution.map x y ≫ _)
            (trivialAugmentation_map_comp_trivialAugmentationULiftYonedaIso_hom f)
            (trivialAugmentation_map_comp_trivialAugmentationULiftYonedaIso_hom g)
      _ = _ := by
          rw [DayConvolution.map_comp, Category.assoc]
          exact (congrArg (_ ≫ ·) (DayConvolution.map_uliftYoneda_map_comp_uliftYonedaIso_hom
            (incl.map f : of a ⟶ of a') (incl.map g : of b ⟶ of b'))).trans
              (Category.assoc _ _ _).symm
  exact congrArg (Functor.whiskerLeft (incl.op : Cᵒᵖ ⥤ (WithInitial C)ᵒᵖ)) key

variable [TensorUnitIsStar C]

private def unitLeft (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) :
    P ⟶ P ⊛ trivialAugmentation.obj Y where
  app x := TypeCat.ofHom fun a ↦ (P ⊛ trivialAugmentation.obj Y).map (toTensorStar x.unop).op
    ((DayConvolution.unit P (trivialAugmentation.obj Y)).app (x, op star)
      ((a, default) : P.obj x × (trivialAugmentation.obj Y).obj (op star)))
  naturality x x' f := by
    ext a
    have h := map_tensorHom_unit_app P (trivialAugmentation.obj Y) f (𝟙 (op star)) a default
    rw [Subsingleton.elim ((trivialAugmentation.obj Y).map (𝟙 _) default) default] at h
    change (P ⊛ _).map (toTensorStar x'.unop).op _ =
      (P ⊛ _).map f ((P ⊛ _).map (toTensorStar x.unop).op _)
    refine (congrArg _ h.symm).trans ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    refine congrArg (fun g ↦ (P ⊛ _).map g _) (Quiver.Hom.unop_inj ?_)
    simpa using (toTensorStar_naturality f.unop).symm

private def unitRight (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) :
    P ⟶ trivialAugmentation.obj Y ⊛ P where
  app x := TypeCat.ofHom fun a ↦ (trivialAugmentation.obj Y ⊛ P).map (toStarTensor x.unop).op
    ((DayConvolution.unit (trivialAugmentation.obj Y) P).app (op star, x)
      ((default, a) : (trivialAugmentation.obj Y).obj (op star) × P.obj x))
  naturality x x' f := by
    ext a
    have h := map_tensorHom_unit_app (trivialAugmentation.obj Y) P (𝟙 (op star)) f default a
    rw [Subsingleton.elim ((trivialAugmentation.obj Y).map (𝟙 _) default) default] at h
    change (_ ⊛ P).map (toStarTensor x'.unop).op _ =
      (_ ⊛ P).map f ((_ ⊛ P).map (toStarTensor x.unop).op _)
    refine (congrArg _ h.symm).trans ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    refine congrArg (fun g ↦ (_ ⊛ P).map g _) (Quiver.Hom.unop_inj ?_)
    simpa using (toStarTensor_naturality f.unop).symm

private noncomputable def counitLeft (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    P ⊛ trivialAugmentation.obj Y ⟶ P :=
  (DayConvolution.homEquiv _ _ _).symm
    ⟨fun x y a b ↦ P.map (x.unop ◁ toTensorUnit Y y b ≫ (ρ_ x.unop).hom).op a,
      fun {x x' y y'} f g a b ↦ by
        dsimp only
        rw [toTensorUnit_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
        refine congrArg (fun h ↦ P.map h a) (Quiver.Hom.unop_inj ?_)
        simp only [unop_comp, Quiver.Hom.unop_op, unop_whiskerLeft, unop_whiskerRight,
          tensorHom_def,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, ← rightUnitor_naturality,
          whisker_exchange_assoc]⟩

private noncomputable def counitRight (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    trivialAugmentation.obj Y ⊛ P ⟶ P :=
  (DayConvolution.homEquiv _ _ _).symm
    ⟨fun y x b a ↦ P.map (toTensorUnit Y y b ▷ x.unop ≫ (λ_ x.unop).hom).op a,
      fun {y y' x x'} g f b a ↦ by
        dsimp only
        rw [toTensorUnit_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
        refine congrArg (fun h ↦ P.map h a) (Quiver.Hom.unop_inj ?_)
        simp only [unop_comp, Quiver.Hom.unop_op, unop_whiskerLeft, unop_whiskerRight,
          tensorHom_def', comp_whiskerRight, Category.assoc, ← leftUnitor_naturality,
          whisker_exchange_assoc]⟩

private lemma unitLeft_comp_counitLeft (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    unitLeft P Y ≫ counitLeft P Y = 𝟙 P := by
  ext x a
  change (counitLeft P Y).app x ((P ⊛ _).map (toTensorStar x.unop).op _) = a
  rw [NatTrans.naturality_apply]
  refine (congrArg _ (DayConvolution.homEquiv_symm_app_unit_app _ _ _ _ x (op star) a
    default)).trans ?_
  refine (Functor.map_comp_apply _ _ _ _).symm.trans ((congrArg (fun h ↦ P.map h a)
    (Quiver.Hom.unop_inj ?_)).trans (Functor.map_id_apply P x a))
  have : isInitialTensorUnit.to star ≫ starInitial.to (𝟙_ (WithInitial C)) = 𝟙 _ :=
    isInitialTensorUnit.hom_ext _ _
  simp only [toTensorStar, toTensorUnit, unop_comp, Quiver.Hom.unop_op, unop_id,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, this,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

private lemma counitLeft_comp_unitLeft (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    counitLeft P Y ≫ unitLeft P Y = 𝟙 _ := by
  refine (DayConvolution.homEquiv _ _ _).injective (Subtype.ext ?_)
  funext x y a b
  rw [DayConvolution.homEquiv_apply, DayConvolution.homEquiv_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, counitLeft, DayConvolution.homEquiv_symm_app_unit_app,
    NatTrans.id_app, ConcreteCategory.id_apply]
  obtain ⟨y⟩ := y
  cases y with
  | of c => exact isEmptyElim (α := Y.obj (op c)) b
  | star =>
    obtain rfl := Subsingleton.elim b default
    have h := map_tensorHom_unit_app P (trivialAugmentation.obj Y)
      (x.unop ◁ toTensorUnit Y (op star) default ≫ (ρ_ x.unop).hom).op (𝟙 (op star))
      a default
    rw [Subsingleton.elim ((trivialAugmentation.obj Y).map (𝟙 _) default) default] at h
    change (P ⊛ _).map (toTensorStar _).op _ = _
    refine (congrArg _ h.symm).trans ((Functor.map_comp_apply _ _ _ _).symm.trans
      ((congrArg (fun h ↦ (P ⊛ _).map h _) (Quiver.Hom.unop_inj ?_)).trans
        (Functor.map_id_apply _ _ _)))
    have : starInitial.to (𝟙_ (WithInitial C)) ≫ isInitialTensorUnit.to star = 𝟙 _ :=
      starInitial.hom_ext _ _
    simp only [toTensorStar, toTensorUnit, unop_comp, Quiver.Hom.unop_op, unop_id,
      unop_whiskerRight, tensorHom_id, Category.assoc]
    rw [whisker_exchange, ← rightUnitor_inv_naturality_assoc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp, this,
      MonoidalCategory.whiskerLeft_id]
    rfl

private lemma unitRight_comp_counitRight (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    unitRight P Y ≫ counitRight P Y = 𝟙 P := by
  ext x a
  change (counitRight P Y).app x ((_ ⊛ P).map (toStarTensor x.unop).op _) = a
  rw [NatTrans.naturality_apply]
  refine (congrArg _ (DayConvolution.homEquiv_symm_app_unit_app _ _ _ _ (op star) x default
    a)).trans ?_
  refine (Functor.map_comp_apply _ _ _ _).symm.trans ((congrArg (fun h ↦ P.map h a)
    (Quiver.Hom.unop_inj ?_)).trans (Functor.map_id_apply P x a))
  have : isInitialTensorUnit.to star ≫ starInitial.to (𝟙_ (WithInitial C)) = 𝟙 _ :=
    isInitialTensorUnit.hom_ext _ _
  simp only [toStarTensor, toTensorUnit, unop_comp, Quiver.Hom.unop_op, unop_id,
    Category.assoc, ← comp_whiskerRight_assoc, this, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id]

private lemma counitRight_comp_unitRight (P : (WithInitial C)ᵒᵖ ⥤ Type (max w u))
    (Y : Cᵒᵖ ⥤ Type (max w u)) [∀ c, IsEmpty (Y.obj c)] :
    counitRight P Y ≫ unitRight P Y = 𝟙 _ := by
  refine (DayConvolution.homEquiv _ _ _).injective (Subtype.ext ?_)
  funext y x b a
  rw [DayConvolution.homEquiv_apply, DayConvolution.homEquiv_apply, NatTrans.comp_app,
    ConcreteCategory.comp_apply, counitRight, DayConvolution.homEquiv_symm_app_unit_app,
    NatTrans.id_app, ConcreteCategory.id_apply]
  obtain ⟨y⟩ := y
  cases y with
  | of c => exact isEmptyElim (α := Y.obj (op c)) b
  | star =>
    obtain rfl := Subsingleton.elim b default
    have h := map_tensorHom_unit_app (trivialAugmentation.obj Y) P (𝟙 (op star))
      (toTensorUnit Y (op star) default ▷ x.unop ≫ (λ_ x.unop).hom).op default a
    rw [Subsingleton.elim ((trivialAugmentation.obj Y).map (𝟙 _) default) default] at h
    change (_ ⊛ P).map (toStarTensor _).op _ = _
    refine (congrArg _ h.symm).trans ((Functor.map_comp_apply _ _ _ _).symm.trans
      ((congrArg (fun h ↦ (_ ⊛ P).map h _) (Quiver.Hom.unop_inj ?_)).trans
        (Functor.map_id_apply _ _ _)))
    have : starInitial.to (𝟙_ (WithInitial C)) ≫ isInitialTensorUnit.to star = 𝟙 _ :=
      starInitial.hom_ext _ _
    simp only [toStarTensor, toTensorUnit, unop_comp, Quiver.Hom.unop_op, unop_id,
      unop_whiskerLeft, id_tensorHom, Category.assoc]
    rw [← whisker_exchange, ← leftUnitor_inv_naturality_assoc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, this,
      id_whiskerRight]
    rfl

private lemma unitLeft_naturality {P P' : (WithInitial C)ᵒᵖ ⥤ Type (max w u)} (α : P ⟶ P')
    {Y Y' : Cᵒᵖ ⥤ Type (max w u)} (g : Y ⟶ Y') :
    unitLeft P Y ≫ DayConvolution.map α (trivialAugmentation.map g) = α ≫ unitLeft P' Y' := by
  ext x a
  change (DayConvolution.map α _).app x ((P ⊛ _).map (toTensorStar x.unop).op _) =
    (P' ⊛ _).map _ _
  rw [NatTrans.naturality_apply]
  exact congrArg _ ((ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app α
    (trivialAugmentation.map g) x (op star))
      ((a, default) : P.obj x × (trivialAugmentation.obj Y).obj (op star))).trans
      (congrArg _ (Prod.ext rfl (Subsingleton.elim _ _))))

private lemma unitRight_naturality {P P' : (WithInitial C)ᵒᵖ ⥤ Type (max w u)} (α : P ⟶ P')
    {Y Y' : Cᵒᵖ ⥤ Type (max w u)} (g : Y ⟶ Y') :
    unitRight P Y ≫ DayConvolution.map (trivialAugmentation.map g) α =
      α ≫ unitRight P' Y' := by
  ext x a
  change (DayConvolution.map _ α).app x ((_ ⊛ P).map (toStarTensor x.unop).op _) =
    (_ ⊛ P').map _ _
  rw [NatTrans.naturality_apply]
  exact congrArg _ ((ConcreteCategory.congr_hom (DayConvolution.unit_app_map_app
    (trivialAugmentation.map g) α (op star) x)
      ((default, a) : (trivialAugmentation.obj Y).obj (op star) × P.obj x)).trans
      (congrArg _ (Prod.ext (Subsingleton.elim _ _) rfl)))

def joinInclLeft (X Y : Cᵒᵖ ⥤ Type (max w u)) : X ⟶ join X Y :=
  Functor.whiskerLeft incl.op (unitLeft (trivialAugmentation.obj X) Y)

def joinInclRight (X Y : Cᵒᵖ ⥤ Type (max w u)) : Y ⟶ join X Y :=
  Functor.whiskerLeft incl.op (unitRight (trivialAugmentation.obj Y) X)

@[reassoc]
theorem joinInclLeft_comp_joinMap {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (f : X ⟶ X')
    (g : Y ⟶ Y') : joinInclLeft X Y ≫ joinMap f g = f ≫ joinInclLeft X' Y' :=
  congrArg (Functor.whiskerLeft incl.op) (unitLeft_naturality (trivialAugmentation.map f) g)

@[reassoc]
theorem joinInclRight_comp_joinMap {X X' Y Y' : Cᵒᵖ ⥤ Type (max w u)} (f : X ⟶ X')
    (g : Y ⟶ Y') : joinInclRight X Y ≫ joinMap f g = g ≫ joinInclRight X' Y' :=
  congrArg (Functor.whiskerLeft incl.op) (unitRight_naturality (trivialAugmentation.map g) f)

theorem isIso_joinInclLeft_of_isEmpty (X Y : Cᵒᵖ ⥤ Type (max w u))
    [∀ c, IsEmpty (Y.obj c)] :
    IsIso (joinInclLeft X Y) :=
  have : IsIso (unitLeft (trivialAugmentation.obj X) Y) :=
    ⟨counitLeft _ Y, unitLeft_comp_counitLeft _ _, counitLeft_comp_unitLeft _ _⟩
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

theorem isIso_joinInclRight_of_isEmpty (X Y : Cᵒᵖ ⥤ Type (max w u))
    [∀ c, IsEmpty (X.obj c)] :
    IsIso (joinInclRight X Y) :=
  have : IsIso (unitRight (trivialAugmentation.obj Y) X) :=
    ⟨counitRight _ X, unitRight_comp_counitRight _ _, counitRight_comp_unitRight _ _⟩
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

theorem uliftYonedaEquiv_joinInclLeft_comp_joinULiftYonedaIso_hom (a b : C)
    (f : 𝟙_ (WithInitial C) ⟶ of b) :
    uliftYonedaEquiv (joinInclLeft (uliftYoneda.{u}.obj a) (uliftYoneda.{u}.obj b) ≫
      (joinULiftYonedaIso a b).hom) =
      (ULift.up ((ρ_ (of a)).inv ≫ of a ◁ f) : (uliftYoneda.{u}.obj (of a ⊗ of b)).obj _) := by
  let eA := trivialAugmentationULiftYonedaIso.{w, u} a
  let eB := trivialAugmentationULiftYonedaIso.{w, u} b
  let d := (eB.hom.app (op star) default).down
  have key : toTensorStar (of a) ≫ (𝟙 (of a) ⊗ₘ d) = (ρ_ (of a)).inv ≫ of a ◁ f := by
    rw [toTensorStar, Category.assoc, id_tensorHom, ← MonoidalCategory.whiskerLeft_comp,
      isInitialTensorUnit.hom_ext (_ ≫ d) f]
  refine (NatTrans.naturality_apply ((dayConvolutionMapIso eA eB).hom ≫
    (DayConvolution.uliftYonedaIso (of a) (of b)).hom) (toTensorStar (of a)).op
      ((DayConvolution.unit (trivialAugmentation.obj (uliftYoneda.{u}.obj a))
        (trivialAugmentation.obj (uliftYoneda.{u}.obj b))).app (op (of a), op star)
          ((ULift.up (𝟙 a), default) : _ × _))).trans ?_
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  refine (congrArg (fun z ↦ (uliftYoneda.{u}.obj (of a ⊗ of b)).map (toTensorStar (of a)).op
    ((DayConvolution.uliftYonedaIso (of a) (of b)).hom.app _ z))
    (DayConvolution.map_unit_app_apply eA.hom eB.hom _ _ _ _)).trans ?_
  refine (congrArg ((uliftYoneda.{u}.obj (of a ⊗ of b)).map (toTensorStar (of a)).op)
    (DayConvolution.uliftYonedaIso_hom_app_unit_app (of a) (of b) (x := op (of a))
      (y := op star) (𝟙 (of a)) d)).trans ?_
  exact congrArg ULift.up key

theorem uliftYonedaEquiv_joinInclRight_comp_joinULiftYonedaIso_hom (a b : C)
    (f : 𝟙_ (WithInitial C) ⟶ of a) :
    uliftYonedaEquiv (joinInclRight (uliftYoneda.{u}.obj a) (uliftYoneda.{u}.obj b) ≫
      (joinULiftYonedaIso a b).hom) =
      (ULift.up ((λ_ (of b)).inv ≫ f ▷ of b) : (uliftYoneda.{u}.obj (of a ⊗ of b)).obj _) := by
  let eA := trivialAugmentationULiftYonedaIso.{w, u} a
  let eB := trivialAugmentationULiftYonedaIso.{w, u} b
  let d := (eA.hom.app (op star) default).down
  have key : toStarTensor (of b) ≫ (d ⊗ₘ 𝟙 (of b)) = (λ_ (of b)).inv ≫ f ▷ of b := by
    rw [toStarTensor, Category.assoc, tensorHom_id, ← comp_whiskerRight,
      isInitialTensorUnit.hom_ext (_ ≫ d) f]
  refine (NatTrans.naturality_apply ((dayConvolutionMapIso eA eB).hom ≫
    (DayConvolution.uliftYonedaIso (of a) (of b)).hom) (toStarTensor (of b)).op
      ((DayConvolution.unit (trivialAugmentation.obj (uliftYoneda.{u}.obj a))
        (trivialAugmentation.obj (uliftYoneda.{u}.obj b))).app (op star, op (of b))
          ((default, ULift.up (𝟙 b)) : _ × _))).trans ?_
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  refine (congrArg (fun z ↦ (uliftYoneda.{u}.obj (of a ⊗ of b)).map (toStarTensor (of b)).op
    ((DayConvolution.uliftYonedaIso (of a) (of b)).hom.app _ z))
    (DayConvolution.map_unit_app_apply eA.hom eB.hom _ _ _ _)).trans ?_
  refine (congrArg ((uliftYoneda.{u}.obj (of a ⊗ of b)).map (toStarTensor (of b)).op)
    (DayConvolution.uliftYonedaIso_hom_app_unit_app (of a) (of b) (x := op star)
      (y := op (of b)) d (𝟙 (of b)))).trans ?_
  exact congrArg ULift.up key

end Monoidal

end CategoryTheory.WithInitial
