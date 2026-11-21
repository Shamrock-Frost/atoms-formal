import Atoms.ForMathlib.CategoryTheory.Bicategory.StrongTransEquivalence

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

def Bicategory.Equivalence.ofEq {a b : B} (h : a = b) : Bicategory.Equivalence a b where
  hom := eqToHom h
  inv := eqToHom h.symm
  unit := by
    subst h
    exact (Equivalence.id a).unit
  counit := by
    subst h
    exact (Equivalence.id a).counit
  left_triangle := by
    subst h
    exact (Equivalence.id a).left_triangle

namespace Pseudofunctor

open StrongTrans

section CopyMap

variable (P : B ⥤ᵖ C) (M : ∀ {a b : B}, (a ⟶ b) → (P.obj a ⟶ P.obj b))
  (κ : ∀ {a b : B} (f : a ⟶ b), M f ≅ P.map f)

abbrev copyMapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : M (f ≫ g) ≅ M f ≫ M g :=
  κ (f ≫ g) ≪≫ P.mapComp f g ≪≫ whiskerLeftIso (P.map f) (κ g).symm ≪≫
    whiskerRightIso (κ f).symm (M g)

theorem copyMapComp_hom {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (copyMapComp P M κ f g).hom =
      (κ (f ≫ g)).hom ≫ (P.mapComp f g).hom ≫ P.map f ◁ (κ g).inv ≫ (κ f).inv ▷ M g :=
  rfl

theorem copyMapComp_inv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (copyMapComp P M κ f g).inv =
      (κ f).hom ▷ M g ≫ P.map f ◁ (κ g).hom ≫ (P.mapComp f g).inv ≫ (κ (f ≫ g)).inv := by
  simp [copyMapComp]

private theorem copyMap_whisker_left {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (θ : g ⟶ h) :
    (κ (f ≫ g)).hom ≫ P.map₂ (f ◁ θ) ≫ (κ (f ≫ h)).inv =
      (copyMapComp P M κ f g).hom ≫ M f ◁ ((κ g).hom ≫ P.map₂ θ ≫ (κ h).inv) ≫
        (copyMapComp P M κ f h).inv := by
  rw [copyMapComp_hom, copyMapComp_inv, P.map₂_whisker_left]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, inv_hom_whiskerRight_assoc]
  simp

private theorem copyMap_whisker_right {a b c : B} {f g : a ⟶ b} (θ : f ⟶ g) (h : b ⟶ c) :
    (κ (f ≫ h)).hom ≫ P.map₂ (θ ▷ h) ≫ (κ (g ≫ h)).inv =
      (copyMapComp P M κ f h).hom ≫ ((κ f).hom ≫ P.map₂ θ ≫ (κ g).inv) ▷ M h ≫
        (copyMapComp P M κ g h).inv := by
  rw [copyMapComp_hom, copyMapComp_inv, P.map₂_whisker_right]
  simp only [Category.assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc]
  rw [whisker_exchange_assoc]
  simp

private theorem copyMap_left_unitor {a b : B} (f : a ⟶ b) :
    (κ (𝟙 a ≫ f)).hom ≫ P.map₂ (λ_ f).hom ≫ (κ f).inv =
      (copyMapComp P M κ (𝟙 a) f).hom ≫ (κ (𝟙 a)).hom ▷ M f ≫ (P.mapId a).hom ▷ M f ≫
        (λ_ (M f)).hom := by
  rw [copyMapComp_hom, P.map₂_left_unitor]
  simp only [Category.assoc, inv_hom_whiskerRight_assoc]
  rw [whisker_exchange_assoc]
  simp

private theorem copyMap_right_unitor {a b : B} (f : a ⟶ b) :
    (κ (f ≫ 𝟙 b)).hom ≫ P.map₂ (ρ_ f).hom ≫ (κ f).inv =
      (copyMapComp P M κ f (𝟙 b)).hom ≫ M f ◁ (κ (𝟙 b)).hom ≫ M f ◁ (P.mapId b).hom ≫
        (ρ_ (M f)).hom := by
  rw [copyMapComp_hom, P.map₂_right_unitor]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  simp

private theorem copyMap_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (κ ((f ≫ g) ≫ h)).hom ≫ P.map₂ (α_ f g h).hom ≫ (κ (f ≫ g ≫ h)).inv =
      (copyMapComp P M κ (f ≫ g) h).hom ≫ (copyMapComp P M κ f g).hom ▷ M h ≫
        (α_ (M f) (M g) (M h)).hom ≫ M f ◁ (copyMapComp P M κ g h).inv ≫
          (copyMapComp P M κ f (g ≫ h)).inv := by
  rw [copyMapComp_hom, copyMapComp_hom, copyMapComp_inv, copyMapComp_inv, P.map₂_associator]
  symm
  calc
    _ = (κ ((f ≫ g) ≫ h)).hom ≫ (P.mapComp (f ≫ g) h).hom ≫
          (P.map (f ≫ g) ◁ (κ h).inv ⊗≫ ((κ (f ≫ g)).inv ≫ (κ (f ≫ g)).hom) ▷ M h ⊗≫
            (P.mapComp f g).hom ▷ M h ⊗≫ P.map f ◁ (κ g).inv ▷ M h ⊗≫
              (κ f).inv ▷ M g ▷ M h ⊗≫
                (M f ◁ ((κ g).hom ▷ M h ≫ P.map g ◁ (κ h).hom ≫ (P.mapComp g h).inv ≫
                  (κ (g ≫ h)).inv) ≫ (κ f).hom ▷ M (g ≫ h)) ⊗≫
                  P.map f ◁ (κ (g ≫ h)).hom ⊗≫ 𝟙 _) ≫
            (P.mapComp f (g ≫ h)).inv ≫ (κ (f ≫ g ≫ h)).inv := by
      bicategory
    _ = (κ ((f ≫ g) ≫ h)).hom ≫ (P.mapComp (f ≫ g) h).hom ≫
          (P.map (f ≫ g) ◁ (κ h).inv ⊗≫ (P.mapComp f g).hom ▷ M h ⊗≫
            P.map f ◁ (κ g).inv ▷ M h ⊗≫ ((κ f).inv ≫ (κ f).hom) ▷ (M g ≫ M h) ⊗≫
              P.map f ◁ ((κ g).hom ▷ M h ≫ P.map g ◁ (κ h).hom ≫ (P.mapComp g h).inv ≫
                (κ (g ≫ h)).inv ≫ (κ (g ≫ h)).hom)) ≫
            (P.mapComp f (g ≫ h)).inv ≫ (κ (f ≫ g ≫ h)).inv := by
      rw [Iso.inv_hom_id (κ (f ≫ g)), whisker_exchange (κ f).hom]
      bicategory
    _ = (κ ((f ≫ g) ≫ h)).hom ≫ (P.mapComp (f ≫ g) h).hom ≫
          ((P.map (f ≫ g) ◁ (κ h).inv ≫ (P.mapComp f g).hom ▷ M h) ⊗≫
            P.map f ◁ ((κ g).inv ≫ (κ g).hom) ▷ M h ⊗≫ P.map f ◁ P.map g ◁ (κ h).hom ⊗≫
              P.map f ◁ (P.mapComp g h).inv) ≫
            (P.mapComp f (g ≫ h)).inv ≫ (κ (f ≫ g ≫ h)).inv := by
      rw [Iso.inv_hom_id (κ f), Iso.inv_hom_id (κ (g ≫ h))]
      bicategory
    _ = (κ ((f ≫ g) ≫ h)).hom ≫ (P.mapComp (f ≫ g) h).hom ≫
          ((P.mapComp f g).hom ▷ P.map h ⊗≫
            (P.map f ≫ P.map g) ◁ ((κ h).inv ≫ (κ h).hom) ⊗≫
              P.map f ◁ (P.mapComp g h).inv) ≫
            (P.mapComp f (g ≫ h)).inv ≫ (κ (f ≫ g ≫ h)).inv := by
      rw [Iso.inv_hom_id (κ g), whisker_exchange]
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

end CopyMap

section Conj

variable {X : C → C}
  (e : ∀ c, Bicategory.Equivalence (X c) c)

def conjMapComp {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (e a).hom ≫ (g ≫ h) ≫ (e c).inv ≅ ((e a).hom ≫ g ≫ (e b).inv) ≫ (e b).hom ≫ h ≫ (e c).inv :=
  Iso.refl _ ≪⊗≫ whiskerLeftIso ((e a).hom ≫ g) (whiskerRightIso (e b).counit.symm (h ≫ (e c).inv))
    ≪⊗≫ Iso.refl _

theorem conjMapComp_hom {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (conjMapComp e g h).hom =
      𝟙 _ ⊗≫ ((e a).hom ≫ g) ◁ (e b).counit.inv ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ :=
  rfl

theorem conjMapComp_inv {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (conjMapComp e g h).inv =
      𝟙 _ ⊗≫ ((e a).hom ≫ g) ◁ (e b).counit.hom ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
  simp [conjMapComp, bicategoricalIsoComp, bicategoricalComp]

def conjMapId (a : C) : (e a).hom ≫ 𝟙 a ≫ (e a).inv ≅ 𝟙 (X a) :=
  whiskerLeftIso (e a).hom (λ_ (e a).inv) ≪≫ (e a).unit.symm

theorem conjMapId_hom (a : C) :
    (conjMapId e a).hom = (e a).hom ◁ (λ_ (e a).inv).hom ≫ (e a).unit.inv :=
  rfl

private theorem conj_whisker_left {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (θ : g ⟶ h) :
    (e a).hom ◁ (f ◁ θ) ▷ (e c).inv =
      (conjMapComp e f g).hom ≫ ((e a).hom ≫ f ≫ (e b).inv) ◁ ((e b).hom ◁ θ ▷ (e c).inv) ≫
        (conjMapComp e f h).inv := by
  rw [conjMapComp_hom, conjMapComp_inv]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f) ◁ ((e b).counit.inv ▷ (g ≫ (e c).inv) ≫
            ((e b).inv ≫ (e b).hom) ◁ (θ ▷ (e c).inv)) ⊗≫
          ((e a).hom ≫ f) ◁ (e b).counit.hom ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f) ◁ (𝟙 _ ◁ (θ ▷ (e c).inv) ≫
            (e b).counit.inv ▷ (h ≫ (e c).inv)) ⊗≫
          ((e a).hom ≫ f) ◁ (e b).counit.hom ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f) ◁ 𝟙 _ ◁ θ ▷ (e c).inv ⊗≫
          ((e a).hom ≫ f) ◁ ((e b).counit.inv ≫ (e b).counit.hom) ▷ (h ≫ (e c).inv) ⊗≫
            𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

private theorem conj_whisker_right {a b c : C} {f g : a ⟶ b} (θ : f ⟶ g) (h : b ⟶ c) :
    (e a).hom ◁ (θ ▷ h) ▷ (e c).inv =
      (conjMapComp e f h).hom ≫ ((e a).hom ◁ θ ▷ (e b).inv) ▷ ((e b).hom ≫ h ≫ (e c).inv) ≫
        (conjMapComp e g h).inv := by
  rw [conjMapComp_hom, conjMapComp_inv]
  symm
  calc
    _ = 𝟙 _ ⊗≫ (((e a).hom ≫ f) ◁ ((e b).counit.inv ▷ (h ≫ (e c).inv)) ≫
            ((e a).hom ◁ θ) ▷ (((e b).inv ≫ (e b).hom) ≫ h ≫ (e c).inv)) ⊗≫
          ((e a).hom ≫ g) ◁ (e b).counit.hom ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (((e a).hom ◁ θ) ▷ (𝟙 _ ≫ h ≫ (e c).inv) ≫
            ((e a).hom ≫ g) ◁ ((e b).counit.inv ▷ (h ≫ (e c).inv))) ⊗≫
          ((e a).hom ≫ g) ◁ (e b).counit.hom ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((e a).hom ◁ θ) ▷ (𝟙 _ ≫ h ≫ (e c).inv) ⊗≫
          ((e a).hom ≫ g) ◁ ((e b).counit.inv ≫ (e b).counit.hom) ▷ (h ≫ (e c).inv) ⊗≫
            𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

private theorem conj_associator {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (e a).hom ◁ (α_ f g h).hom ▷ (e d).inv =
      (conjMapComp e (f ≫ g) h).hom ≫ (conjMapComp e f g).hom ▷ ((e c).hom ≫ h ≫ (e d).inv) ≫
        (α_ _ _ _).hom ≫ ((e a).hom ≫ f ≫ (e b).inv) ◁ (conjMapComp e g h).inv ≫
          (conjMapComp e f (g ≫ h)).inv := by
  rw [conjMapComp_hom, conjMapComp_hom, conjMapComp_inv, conjMapComp_inv]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f ≫ g) ◁ (e c).counit.inv ▷ (h ≫ (e d).inv) ⊗≫
          ((e a).hom ≫ f) ◁ ((e b).counit.inv ▷ (g ≫ ((e c).inv ≫ (e c).hom) ≫ h ≫ (e d).inv) ≫
            ((e b).inv ≫ (e b).hom) ◁ (g ◁ (e c).counit.hom ▷ (h ≫ (e d).inv))) ⊗≫
            ((e a).hom ≫ f) ◁ (e b).counit.hom ▷ (g ≫ h ≫ (e d).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f ≫ g) ◁ (e c).counit.inv ▷ (h ≫ (e d).inv) ⊗≫
          ((e a).hom ≫ f) ◁ (𝟙 _ ◁ (g ◁ (e c).counit.hom ▷ (h ≫ (e d).inv)) ≫
            (e b).counit.inv ▷ (g ≫ 𝟙 _ ≫ h ≫ (e d).inv)) ⊗≫
            ((e a).hom ≫ f) ◁ (e b).counit.hom ▷ (g ≫ h ≫ (e d).inv) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f ≫ g) ◁ ((e c).counit.inv ≫ (e c).counit.hom) ▷ (h ≫ (e d).inv) ⊗≫
          ((e a).hom ≫ f) ◁ ((e b).counit.inv ≫ (e b).counit.hom) ▷ (g ≫ h ≫ (e d).inv) ⊗≫
            𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id, Iso.inv_hom_id]
      bicategory

private theorem conj_left_unitor {a b : C} (f : a ⟶ b) :
    (e a).hom ◁ (λ_ f).hom ▷ (e b).inv =
      (conjMapComp e (𝟙 a) f).hom ≫ (conjMapId e a).hom ▷ ((e a).hom ≫ f ≫ (e b).inv) ≫
        (λ_ _).hom := by
  rw [conjMapComp_hom, conjMapId_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ rightZigzag (e a).counit.inv (e a).unit.inv ▷ (f ≫ (e b).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← leftZigzagIso_inv, (e a).left_triangle]
      simp only [Iso.trans_inv, Iso.symm_inv]
      bicategory

private theorem conj_right_unitor {a b : C} (f : a ⟶ b) :
    (e a).hom ◁ (ρ_ f).hom ▷ (e b).inv =
      (conjMapComp e f (𝟙 b)).hom ≫ ((e a).hom ≫ f ≫ (e b).inv) ◁ (conjMapId e b).hom ≫
        (ρ_ _).hom := by
  rw [conjMapComp_hom, conjMapId_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ f) ◁ leftZigzag (e b).counit.inv (e b).unit.inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [← rightZigzagIso_inv, (e b).right_triangle]
      simp only [Iso.trans_inv, Iso.symm_inv]
      bicategory

def conj : C ⥤ᵖ C where
  obj := X
  map {a b} g := (e a).hom ≫ g ≫ (e b).inv
  map₂ {a b _ _} θ := (e a).hom ◁ θ ▷ (e b).inv
  mapId := conjMapId e
  mapComp := conjMapComp e
  map₂_whisker_left f _ _ θ := conj_whisker_left e f θ
  map₂_whisker_right θ h := conj_whisker_right e θ h
  map₂_associator f g h := conj_associator e f g h
  map₂_left_unitor f := conj_left_unitor e f
  map₂_right_unitor f := conj_right_unitor e f

def conjTransNaturality {a b : C} (g : a ⟶ b) :
    ((e a).hom ≫ g ≫ (e b).inv) ≫ (e b).hom ≅ (e a).hom ≫ g :=
  Iso.refl _ ≪⊗≫ whiskerLeftIso ((e a).hom ≫ g) (e b).counit ≪⊗≫ Iso.refl ((e a).hom ≫ g)

theorem conjTransNaturality_hom {a b : C} (g : a ⟶ b) :
    (conjTransNaturality e g).hom = 𝟙 _ ⊗≫ ((e a).hom ≫ g) ◁ (e b).counit.hom ⊗≫ 𝟙 _ :=
  rfl

private theorem conjTrans_naturality_naturality {a b : C} {g h : a ⟶ b} (θ : g ⟶ h) :
    ((e a).hom ◁ θ ▷ (e b).inv) ▷ (e b).hom ≫ (conjTransNaturality e h).hom =
      (conjTransNaturality e g).hom ≫ (e a).hom ◁ θ := by
  rw [conjTransNaturality_hom, conjTransNaturality_hom]
  calc
    _ = 𝟙 _ ⊗≫ (((e a).hom ◁ θ) ▷ ((e b).inv ≫ (e b).hom) ≫
          ((e a).hom ≫ h) ◁ (e b).counit.hom) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (((e a).hom ≫ g) ◁ (e b).counit.hom ≫ ((e a).hom ◁ θ) ▷ 𝟙 _) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = _ := by
      bicategory

private theorem conjTrans_naturality_id (a : C) :
    (conjTransNaturality e (𝟙 a)).hom ≫ (e a).hom ◁ (Iso.refl (𝟙 a)).hom =
      (conjMapId e a).hom ▷ (e a).hom ≫ (λ_ (e a).hom).hom ≫ (ρ_ (e a).hom).inv := by
  rw [conjTransNaturality_hom, conjMapId_hom, Iso.refl_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ (e a).unit.inv ▷ (e a).hom ⊗≫ leftZigzag (e a).unit.hom (e a).counit.hom ⊗≫
          𝟙 _ := by
      rw [(e a).left_triangle_hom]
      bicategory
    _ = 𝟙 _ ⊗≫ ((e a).unit.inv ≫ (e a).unit.hom) ▷ (e a).hom ⊗≫
          (e a).hom ◁ (e a).counit.hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

private theorem conjTrans_naturality_comp {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (conjTransNaturality e (g ≫ h)).hom ≫ (e a).hom ◁ (Iso.refl (g ≫ h)).hom =
      (conjMapComp e g h).hom ▷ (e c).hom ≫ (α_ _ _ _).hom ≫
        ((e a).hom ≫ g ≫ (e b).inv) ◁ (conjTransNaturality e h).hom ≫ (α_ _ _ _).inv ≫
          (conjTransNaturality e g).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [conjTransNaturality_hom, conjTransNaturality_hom, conjTransNaturality_hom,
    conjMapComp_hom, Iso.refl_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ g) ◁ ((e b).counit.inv ▷ (h ≫ (e c).inv ≫ (e c).hom) ≫
          ((e b).inv ≫ (e b).hom) ◁ (h ◁ (e c).counit.hom)) ⊗≫
          ((e a).hom ≫ g) ◁ (e b).counit.hom ▷ h ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ g) ◁ (𝟙 _ ◁ (h ◁ (e c).counit.hom) ≫
          (e b).counit.inv ▷ (h ≫ 𝟙 _)) ⊗≫ ((e a).hom ≫ g) ◁ (e b).counit.hom ▷ h ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((e a).hom ≫ g ≫ h) ◁ (e c).counit.hom ⊗≫
          ((e a).hom ≫ g) ◁ ((e b).counit.inv ≫ (e b).counit.hom) ▷ h ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

end Conj

section LocalEquivalence

variable (F : B ⥤ᵖ C) [∀ a b, (F.mapFunctor a b).IsEquivalence]

private theorem map₂_preimageIso_hom {a b : B} {f g : a ⟶ b} (θ : F.map f ≅ F.map g) :
    F.map₂ ((F.mapFunctor a b).preimageIso θ).hom = θ.hom :=
  (F.mapFunctor a b).map_preimage θ.hom

private theorem map₂_preimageIso_inv {a b : B} {f g : a ⟶ b} (θ : F.map f ≅ F.map g) :
    F.map₂ ((F.mapFunctor a b).preimageIso θ).inv = θ.inv :=
  (F.mapFunctor a b).map_preimage θ.inv

private theorem map₂_preimage {a b : B} {f g : a ⟶ b} (θ : F.map f ⟶ F.map g) :
    F.map₂ ((F.mapFunctor a b).preimage θ) = θ :=
  (F.mapFunctor a b).map_preimage θ

omit [∀ a b, (F.mapFunctor a b).IsEquivalence] in
private theorem map₂_right_unitor_inv {a b : B} (f : a ⟶ b) :
    F.map₂ (ρ_ f).inv = (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv ≫
      (F.mapComp f (𝟙 b)).inv := by
  rw [F.mapComp_id_right_inv]
  simp

omit [∀ a b, (F.mapFunctor a b).IsEquivalence] in
private theorem map₂_associator_inv {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map₂ (α_ f g h).inv = (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv := by
  rw [F.mapComp_assoc_right_hom_assoc]
  simp

noncomputable abbrev liftNat {a b a' b' : B} {f : a ⟶ b} {σa : a ⟶ a'} {σb : b ⟶ b'}
    {Qf : a' ⟶ b'} {ta : F.obj a ⟶ F.obj a'} {tb : F.obj b ⟶ F.obj b'}
    (μa : F.map σa ≅ ta) (μb : F.map σb ≅ tb) (n : F.map f ≫ tb ≅ ta ≫ F.map Qf) :
    f ≫ σb ≅ σa ≫ Qf :=
  (F.mapFunctor a b').preimageIso (F.mapComp f σb ≪≫ whiskerLeftIso (F.map f) μb ≪≫ n ≪≫
    whiskerRightIso μa.symm (F.map Qf) ≪≫ (F.mapComp σa Qf).symm : F.map _ ≅ F.map _)

private theorem lift_nn {a b a' b' : B} {f g : a ⟶ b} (θ : f ⟶ g) {σa : a ⟶ a'} {σb : b ⟶ b'}
    {Qf Qg : a' ⟶ b'} (Qθ : Qf ⟶ Qg) {ta : F.obj a ⟶ F.obj a'} {tb : F.obj b ⟶ F.obj b'}
    (μa : F.map σa ≅ ta) (μb : F.map σb ≅ tb) (nf : F.map f ≫ tb ≅ ta ≫ F.map Qf)
    (ng : F.map g ≫ tb ≅ ta ≫ F.map Qg)
    (h : F.map₂ θ ▷ tb ≫ ng.hom = nf.hom ≫ ta ◁ F.map₂ Qθ) :
    θ ▷ σb ≫ (liftNat F μa μb ng).hom = (liftNat F μa μb nf).hom ≫ σa ◁ Qθ := by
  apply (F.mapFunctor _ _).map_injective
  simp only [PrelaxFunctor.mapFunctor_map, F.map₂_comp, F.map₂_whisker_left,
    F.map₂_whisker_right, map₂_preimageIso_hom, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_assoc, reassoc_of% h, whisker_exchange_assoc]

private theorem lift_id {a a' : B} (σa : a ⟶ a') {ta : F.obj a ⟶ F.obj a'}
    (μa : F.map σa ≅ ta) {Q1 Q0 : a' ⟶ a'} (Γ1 : Q1 ⟶ Q0) (Γ2 : Q0 ⟶ 𝟙 a')
    (n1 : F.map (𝟙 a) ≫ ta ≅ ta ≫ F.map Q1) (n0 : 𝟙 (F.obj a) ≫ ta ≅ ta ≫ F.map Q0)
    (h1 : (F.mapId a).hom ▷ ta ≫ n0.hom = n1.hom ≫ ta ◁ F.map₂ Γ1)
    (h2 : n0.hom ≫ ta ◁ (F.map₂ Γ2 ≫ (F.mapId a').hom) =
      𝟙 (𝟙 _) ▷ ta ≫ (λ_ ta).hom ≫ (ρ_ ta).inv) :
    (liftNat F μa μa n1).hom ≫ σa ◁ (Γ1 ≫ Γ2) =
      𝟙 (𝟙 a) ▷ σa ≫ (λ_ σa).hom ≫ (ρ_ σa).inv := by
  apply (F.mapFunctor _ _).map_injective
  simp only [PrelaxFunctor.mapFunctor_map, F.map₂_comp, F.map₂_whisker_left,
    map₂_preimageIso_hom, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    id_whiskerRight, Category.id_comp, F.map₂_left_unitor, map₂_right_unitor_inv,
    whiskerLeft_comp]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← reassoc_of% h1,
    whisker_exchange_assoc]
  calc
    _ = (F.mapComp (𝟙 a) σa).hom ≫ (F.mapId a).hom ▷ F.map σa ≫ 𝟙 (F.obj a) ◁ μa.hom ≫
          (n0.hom ≫ ta ◁ (F.map₂ Γ2 ≫ (F.mapId a').hom)) ≫ ta ◁ (F.mapId a').inv ≫
            μa.inv ▷ F.map (𝟙 a') ≫ (F.mapComp σa (𝟙 a')).inv := by
      simp
    _ = (F.mapComp (𝟙 a) σa).hom ⊗≫ (F.mapId a).hom ▷ F.map σa ⊗≫
          ((μa.hom ▷ 𝟙 _ ≫ ta ◁ (F.mapId a').inv) ≫ μa.inv ▷ F.map (𝟙 a')) ⊗≫
            (F.mapComp σa (𝟙 a')).inv := by
      rw [h2]
      bicategory
    _ = (F.mapComp (𝟙 a) σa).hom ⊗≫ (F.mapId a).hom ▷ F.map σa ⊗≫
          F.map σa ◁ (F.mapId a').inv ⊗≫ ((μa.hom ≫ μa.inv) ▷ F.map (𝟙 a')) ⊗≫
            (F.mapComp σa (𝟙 a')).inv := by
      rw [← whisker_exchange]
      bicategory
    _ = _ := by
      rw [Iso.hom_inv_id]
      bicategory

private theorem lift_comp {a b c a' b' c' : B} (f : a ⟶ b) (g : b ⟶ c) {σa : a ⟶ a'}
    {σb : b ⟶ b'} {σc : c ⟶ c'} {Qf : a' ⟶ b'} {Qg : b' ⟶ c'} {Qfg Qfg' : a' ⟶ c'}
    (Γ1 : Qfg ⟶ Qfg') (Γ2 : Qfg' ⟶ Qf ≫ Qg) {ta : F.obj a ⟶ F.obj a'}
    {tb : F.obj b ⟶ F.obj b'} {tc : F.obj c ⟶ F.obj c'} (μa : F.map σa ≅ ta)
    (μb : F.map σb ≅ tb) (μc : F.map σc ≅ tc) (nf : F.map f ≫ tb ≅ ta ≫ F.map Qf)
    (ng : F.map g ≫ tc ≅ tb ≫ F.map Qg) (nfg : F.map (f ≫ g) ≫ tc ≅ ta ≫ F.map Qfg)
    (nfg' : (F.map f ≫ F.map g) ≫ tc ≅ ta ≫ F.map Qfg')
    (h1 : (F.mapComp f g).hom ▷ tc ≫ nfg'.hom = nfg.hom ≫ ta ◁ F.map₂ Γ1)
    (h2 : nfg'.hom ≫ ta ◁ (F.map₂ Γ2 ≫ (F.mapComp Qf Qg).hom) =
      𝟙 _ ▷ tc ≫ (α_ _ _ _).hom ≫ F.map f ◁ ng.hom ≫ (α_ _ _ _).inv ≫ nf.hom ▷ F.map Qg ≫
        (α_ _ _ _).hom) :
    (liftNat F μa μc nfg).hom ≫ σa ◁ (Γ1 ≫ Γ2) =
      𝟙 (f ≫ g) ▷ σc ≫ (α_ f g σc).hom ≫ f ◁ (liftNat F μb μc ng).hom ≫ (α_ f σb Qg).inv ≫
        (liftNat F μa μb nf).hom ▷ Qg ≫ (α_ σa Qf Qg).hom := by
  apply (F.mapFunctor _ _).map_injective
  simp only [PrelaxFunctor.mapFunctor_map, F.map₂_comp, F.map₂_whisker_left,
    F.map₂_whisker_right, map₂_preimageIso_hom, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    F.map₂_associator, map₂_associator_inv, id_whiskerRight, Category.id_comp,
    comp_whiskerRight, whiskerLeft_comp, inv_hom_whiskerRight_assoc,
    whiskerLeft_inv_hom_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← reassoc_of% h1,
    whisker_exchange_assoc]
  calc
    _ = (F.mapComp (f ≫ g) σc).hom ≫ (F.mapComp f g).hom ▷ F.map σc ≫
          (F.map f ≫ F.map g) ◁ μc.hom ≫
          (nfg'.hom ≫ ta ◁ (F.map₂ Γ2 ≫ (F.mapComp Qf Qg).hom)) ≫ ta ◁ (F.mapComp Qf Qg).inv ≫
            μa.inv ▷ F.map (Qf ≫ Qg) ≫ (F.mapComp σa (Qf ≫ Qg)).inv := by
      simp
    _ = (F.mapComp (f ≫ g) σc).hom ≫ (F.mapComp f g).hom ▷ F.map σc ⊗≫
          F.map f ◁ F.map g ◁ μc.hom ⊗≫ F.map f ◁ ng.hom ⊗≫ nf.hom ▷ F.map Qg ⊗≫
          (ta ◁ (F.mapComp Qf Qg).inv ≫ μa.inv ▷ F.map (Qf ≫ Qg)) ⊗≫
            (F.mapComp σa (Qf ≫ Qg)).inv := by
      rw [h2]
      bicategory
    _ = (F.mapComp (f ≫ g) σc).hom ≫ (F.mapComp f g).hom ▷ F.map σc ⊗≫
          F.map f ◁ F.map g ◁ μc.hom ⊗≫ F.map f ◁ ng.hom ⊗≫
          F.map f ◁ ((μb.inv ≫ μb.hom) ▷ F.map Qg) ⊗≫ nf.hom ▷ F.map Qg ⊗≫
          (μa.inv ▷ (F.map Qf ≫ F.map Qg) ≫ F.map σa ◁ (F.mapComp Qf Qg).inv) ⊗≫
            (F.mapComp σa (Qf ≫ Qg)).inv := by
      rw [Iso.inv_hom_id, ← whisker_exchange]
      bicategory
    _ = _ := by
      bicategory

noncomputable def liftTrans {G : C ⥤ᵖ B} (η : Pseudofunctor.id C ⟶ G.comp F) :
    Pseudofunctor.id B ⟶ F.comp G where
  app a := (F.mapFunctor a (G.obj (F.obj a))).objPreimage (η.app (F.obj a))
  naturality f := liftNat F ((F.mapFunctor _ _).objObjPreimageIso _)
    ((F.mapFunctor _ _).objObjPreimageIso _) (η.naturality (F.map f))
  naturality_naturality θ := lift_nn F θ _ _ _ _ _ (η.naturality_naturality (F.map₂ θ))
  naturality_id a := lift_id F _ _ _ _ _ _ (η.naturality_naturality (F.mapId a).hom)
    (η.naturality_id (F.obj a))
  naturality_comp f g := lift_comp F f g _ _ _ _ _ _ _ _ _
    (η.naturality_naturality (F.mapComp f g).hom) (η.naturality_comp (F.map f) (F.map g))

noncomputable def equivalenceOfMap {a b : B} (f : a ⟶ b) {g' : F.obj b ⟶ F.obj a}
    (u : 𝟙 (F.obj a) ≅ F.map f ≫ g') (c : g' ≫ F.map f ≅ 𝟙 (F.obj b)) :
    Bicategory.Equivalence a b :=
  Equivalence.mkOfAdjointifyCounit
    ((F.mapFunctor a a).preimageIso (F.mapId a ≪≫ u ≪≫
      whiskerLeftIso (F.map f) ((F.mapFunctor b a).objObjPreimageIso g').symm ≪≫
        (F.mapComp f _).symm : F.map _ ≅ F.map _))
    ((F.mapFunctor b b).preimageIso (F.mapComp _ f ≪≫
      whiskerRightIso ((F.mapFunctor b a).objObjPreimageIso g') (F.map f) ≪≫ c ≪≫
        (F.mapId b).symm : F.map _ ≅ F.map _))

end LocalEquivalence

section PseudoInverse

variable (F : B ⥤ᵖ C) [∀ a b, (F.mapFunctor a b).IsEquivalence] (s : C → B)
  (e : ∀ c, Bicategory.Equivalence (F.obj (s c)) c)

noncomputable abbrev pseudoInverseMap {a b : C} (g : a ⟶ b) : s a ⟶ s b :=
  (F.mapFunctor (s a) (s b)).objPreimage ((e a).hom ≫ g ≫ (e b).inv)

noncomputable abbrev pseudoInverseMapIso {a b : C} (g : a ⟶ b) :
    F.map (pseudoInverseMap F s e g) ≅ (e a).hom ≫ g ≫ (e b).inv :=
  (F.mapFunctor (s a) (s b)).objObjPreimageIso _

noncomputable abbrev pseudoInverseMapComp {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    F.map (pseudoInverseMap F s e (g ≫ h)) ≅
      F.map (pseudoInverseMap F s e g) ≫ F.map (pseudoInverseMap F s e h) :=
  copyMapComp (conj e) (fun g => F.map (pseudoInverseMap F s e g)) (pseudoInverseMapIso F s e)
    g h

private theorem pseudoInverseMapComp_hom {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (pseudoInverseMapComp F s e g h).hom =
      (pseudoInverseMapIso F s e (g ≫ h)).hom ≫ (conjMapComp e g h).hom ≫
        ((e a).hom ≫ g ≫ (e b).inv) ◁ (pseudoInverseMapIso F s e h).inv ≫
          (pseudoInverseMapIso F s e g).inv ▷ F.map (pseudoInverseMap F s e h) :=
  rfl

noncomputable abbrev pseudoInverse : C ⥤ᵖ B where
  obj := s
  map g := pseudoInverseMap F s e g
  map₂ {a b g h} θ := (F.mapFunctor (s a) (s b)).preimage
    ((pseudoInverseMapIso F s e g).hom ≫ (e a).hom ◁ θ ▷ (e b).inv ≫
      (pseudoInverseMapIso F s e h).inv : F.map _ ⟶ F.map _)
  map₂_id _ := by
    simp only [Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight, Category.id_comp,
      Iso.hom_inv_id]
    exact (F.mapFunctor _ _).preimage_id
  map₂_comp _ _ := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, F.map₂_comp, map₂_preimage, Category.assoc,
      Iso.inv_hom_id_assoc, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight]
    rfl)
  mapId c := (F.mapFunctor (s c) (s c)).preimageIso
    (pseudoInverseMapIso F s e (𝟙 c) ≪≫ conjMapId e c ≪≫ (F.mapId (s c)).symm :
      F.map _ ≅ F.map _)
  mapComp {a _ c} g h := (F.mapFunctor (s a) (s c)).preimageIso
    (pseudoInverseMapComp F s e g h ≪≫ (F.mapComp _ _).symm : F.map _ ≅ F.map _)
  map₂_whisker_left g _ _ θ := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, map₂_preimageIso_hom, map₂_preimageIso_inv,
      F.map₂_comp, F.map₂_whisker_left, map₂_preimage, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]
    exact copyMap_whisker_left (conj e) _ (pseudoInverseMapIso F s e) g θ)
  map₂_whisker_right θ h := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, map₂_preimageIso_hom, map₂_preimageIso_inv,
      F.map₂_comp, F.map₂_whisker_right, map₂_preimage, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc]
    exact copyMap_whisker_right (conj e) _ (pseudoInverseMapIso F s e) θ h)
  map₂_associator g h k := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, map₂_preimageIso_hom, map₂_preimageIso_inv,
      F.map₂_comp, F.map₂_whisker_right, F.map₂_whisker_left, F.map₂_associator, map₂_preimage,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
      Iso.inv_hom_id_assoc, comp_whiskerRight, whiskerLeft_comp, 
      inv_hom_whiskerRight_assoc, whiskerLeft_inv_hom_assoc]
    exact copyMap_associator (conj e) _ (pseudoInverseMapIso F s e) g h k)
  map₂_left_unitor g := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, map₂_preimageIso_hom, 
      F.map₂_comp, F.map₂_whisker_right, F.map₂_left_unitor, map₂_preimage,
      Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, comp_whiskerRight, inv_hom_whiskerRight_assoc]
    exact copyMap_left_unitor (conj e) _ (pseudoInverseMapIso F s e) g)
  map₂_right_unitor g := (F.mapFunctor _ _).map_injective (by
    simp only [PrelaxFunctor.mapFunctor_map, map₂_preimageIso_hom, 
      F.map₂_comp, F.map₂_whisker_left, F.map₂_right_unitor, map₂_preimage,
      Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, whiskerLeft_comp, whiskerLeft_inv_hom_assoc]
    exact copyMap_right_unitor (conj e) _ (pseudoInverseMapIso F s e) g)

theorem pseudoInverse_obj (c : C) : (F.pseudoInverse s e).obj c = s c :=
  rfl

private theorem comp_pseudoInverse_map₂ {a b : C} {g h : a ⟶ b} (θ : g ⟶ h) :
    ((F.pseudoInverse s e).comp F).map₂ θ =
      (pseudoInverseMapIso F s e g).hom ≫ (e a).hom ◁ θ ▷ (e b).inv ≫
        (pseudoInverseMapIso F s e h).inv :=
  map₂_preimage F _

private theorem comp_pseudoInverse_mapId (c : C) :
    (((F.pseudoInverse s e).comp F).mapId c).hom =
      (pseudoInverseMapIso F s e (𝟙 c)).hom ≫ (conjMapId e c).hom :=
  (congrArg (· ≫ (F.mapId (s c)).hom) (map₂_preimageIso_hom F _)).trans (by simp)

private theorem comp_pseudoInverse_mapComp {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    (((F.pseudoInverse s e).comp F).mapComp g h).hom = (pseudoInverseMapComp F s e g h).hom :=
  (congrArg (· ≫ (F.mapComp _ _).hom) (map₂_preimageIso_hom F _)).trans (by simp)

private theorem counit_naturality_naturality {a b : C} {g h : a ⟶ b} (θ : g ⟶ h) :
    ((pseudoInverseMapIso F s e g).hom ≫ (e a).hom ◁ θ ▷ (e b).inv ≫
        (pseudoInverseMapIso F s e h).inv) ▷ (e b).hom ≫
      (pseudoInverseMapIso F s e h).hom ▷ (e b).hom ≫ (conjTransNaturality e h).hom =
    ((pseudoInverseMapIso F s e g).hom ▷ (e b).hom ≫ (conjTransNaturality e g).hom) ≫
      (e a).hom ◁ θ := by
  simp only [comp_whiskerRight, Category.assoc, inv_hom_whiskerRight_assoc,
    conjTrans_naturality_naturality]

private theorem counit_naturality_id (a : C) :
    ((pseudoInverseMapIso F s e (𝟙 a)).hom ▷ (e a).hom ≫ (conjTransNaturality e (𝟙 a)).hom) ≫
        (e a).hom ◁ (Iso.refl (𝟙 a)).hom =
      ((pseudoInverseMapIso F s e (𝟙 a)).hom ≫ (conjMapId e a).hom) ▷ (e a).hom ≫
        (λ_ (e a).hom).hom ≫ (ρ_ (e a).hom).inv := by
  rw [Category.assoc, conjTrans_naturality_id, comp_whiskerRight, Category.assoc]

private theorem counit_naturality_comp {a b c : C} (g : a ⟶ b) (h : b ⟶ c) :
    ((pseudoInverseMapIso F s e (g ≫ h)).hom ▷ (e c).hom ≫
        (conjTransNaturality e (g ≫ h)).hom) ≫ (e a).hom ◁ (Iso.refl (g ≫ h)).hom =
      (pseudoInverseMapComp F s e g h).hom ▷ (e c).hom ≫ (α_ _ _ _).hom ≫
        F.map (pseudoInverseMap F s e g) ◁
          ((pseudoInverseMapIso F s e h).hom ▷ (e c).hom ≫ (conjTransNaturality e h).hom) ≫
        (α_ _ _ _).inv ≫
          ((pseudoInverseMapIso F s e g).hom ▷ (e b).hom ≫ (conjTransNaturality e g).hom) ▷ h ≫
            (α_ _ _ _).hom := by
  rw [pseudoInverseMapComp_hom]
  symm
  calc
    _ = (pseudoInverseMapIso F s e (g ≫ h)).hom ▷ (e c).hom ⊗≫
          (conjMapComp e g h).hom ▷ (e c).hom ⊗≫
          ((e a).hom ≫ g ≫ (e b).inv) ◁ (pseudoInverseMapIso F s e h).inv ▷ (e c).hom ⊗≫
          ((pseudoInverseMapIso F s e g).inv ▷ (F.map (pseudoInverseMap F s e h) ≫ (e c).hom) ≫
            F.map (pseudoInverseMap F s e g) ◁ (pseudoInverseMapIso F s e h).hom ▷ (e c).hom) ⊗≫
          F.map (pseudoInverseMap F s e g) ◁ (conjTransNaturality e h).hom ⊗≫
          (pseudoInverseMapIso F s e g).hom ▷ (e b).hom ▷ h ⊗≫
          (conjTransNaturality e g).hom ▷ h ⊗≫ 𝟙 _ := by
      bicategory
    _ = (pseudoInverseMapIso F s e (g ≫ h)).hom ▷ (e c).hom ⊗≫
          (conjMapComp e g h).hom ▷ (e c).hom ⊗≫
          ((e a).hom ≫ g ≫ (e b).inv) ◁
            ((pseudoInverseMapIso F s e h).inv ≫ (pseudoInverseMapIso F s e h).hom) ▷ (e c).hom ⊗≫
          ((pseudoInverseMapIso F s e g).inv ▷ (((e b).hom ≫ h ≫ (e c).inv) ≫ (e c).hom) ≫
            F.map (pseudoInverseMap F s e g) ◁ (conjTransNaturality e h).hom) ⊗≫
          (pseudoInverseMapIso F s e g).hom ▷ (e b).hom ▷ h ⊗≫
          (conjTransNaturality e g).hom ▷ h ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = (pseudoInverseMapIso F s e (g ≫ h)).hom ▷ (e c).hom ⊗≫
          (conjMapComp e g h).hom ▷ (e c).hom ⊗≫
          ((e a).hom ≫ g ≫ (e b).inv) ◁ (conjTransNaturality e h).hom ⊗≫
          ((pseudoInverseMapIso F s e g).inv ≫ (pseudoInverseMapIso F s e g).hom) ▷
            ((e b).hom ≫ h) ⊗≫
          (conjTransNaturality e g).hom ▷ h ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id, ← whisker_exchange]
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id, Category.assoc, conjTrans_naturality_comp]
      bicategory

noncomputable abbrev pseudoInverseCounitNaturality {a b : C} (g : a ⟶ b) :
    F.map (pseudoInverseMap F s e g) ≫ (e b).hom ≅ (e a).hom ≫ g :=
  whiskerRightIso (pseudoInverseMapIso F s e g) (e b).hom ≪≫ conjTransNaturality e g

noncomputable def pseudoInverseCounitTrans : (F.pseudoInverse s e).comp F ⟶ Pseudofunctor.id C where
  app c := (e c).hom
  naturality g := pseudoInverseCounitNaturality F s e g
  naturality_naturality θ := by
    rw [comp_pseudoInverse_map₂]
    exact counit_naturality_naturality F s e θ
  naturality_id a := by
    rw [comp_pseudoInverse_mapId]
    exact counit_naturality_id F s e a
  naturality_comp g h := by
    rw [comp_pseudoInverse_mapComp]
    exact counit_naturality_comp F s e g h

noncomputable def pseudoInverseCounit :
    Bicategory.Equivalence ((F.pseudoInverse s e).comp F) (Pseudofunctor.id C) :=
  StrongTrans.equivalenceOfApp (pseudoInverseCounitTrans F s e) e fun _ => rfl

theorem pseudoInverseCounit_hom_app (c : C) :
    (F.pseudoInverseCounit s e).hom.app c = (e c).hom :=
  rfl

noncomputable def pseudoInverseUnit :
    Bicategory.Equivalence (Pseudofunctor.id B) (F.comp (F.pseudoInverse s e)) :=
  StrongTrans.equivalenceOfApp (liftTrans F (F.pseudoInverseCounit s e).inv)
    (fun a => equivalenceOfMap F _
      ((e (F.obj a)).counit.symm ≪≫ whiskerRightIso ((F.mapFunctor _ _).objObjPreimageIso _).symm _)
      (whiskerLeftIso _ ((F.mapFunctor _ _).objObjPreimageIso _) ≪≫ (e (F.obj a)).unit.symm))
    fun _ => rfl

end PseudoInverse

end Pseudofunctor

end CategoryTheory
