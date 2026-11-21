import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace Pseudofunctor

open StrongTrans

namespace StrongTrans

variable {F G : B ⥤ᵖ C} (η : F ⟶ G) (ι : ∀ a, G.obj a ⟶ F.obj a)
  (u : ∀ a, 𝟙 (F.obj a) ≅ η.app a ≫ ι a) (c : ∀ a, ι a ≫ η.app a ≅ 𝟙 (G.obj a))

def invNaturality {a b : B} (f : a ⟶ b) : G.map f ≫ ι b ≅ ι a ≫ F.map f :=
  Iso.refl _ ≪⊗≫ whiskerRightIso (c a).symm (G.map f ≫ ι b) ≪⊗≫
    whiskerLeftIso (ι a) (whiskerRightIso (η.naturality f).symm (ι b)) ≪⊗≫
    whiskerLeftIso (ι a) (whiskerLeftIso (F.map f) (u b).symm) ≪⊗≫ Iso.refl (ι a ≫ F.map f)

theorem invNaturality_hom {a b : B} (f : a ⟶ b) :
    (invNaturality η ι u c f).hom =
      𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b) ⊗≫ ι a ◁ (η.naturality f).inv ▷ ι b ⊗≫
        ι a ◁ F.map f ◁ (u b).inv ⊗≫ 𝟙 _ :=
  rfl

variable {η ι u c}

private theorem naturality_inv_naturality {a b : B} {f g : a ⟶ b} (θ : f ⟶ g) :
    η.app a ◁ G.map₂ θ ≫ (η.naturality g).inv = (η.naturality f).inv ≫ F.map₂ θ ▷ η.app b := by
  rw [Iso.comp_inv_eq, Category.assoc, η.naturality_naturality, Iso.inv_hom_id_assoc]

theorem invNaturality_naturality {a b : B} {f g : a ⟶ b} (θ : f ⟶ g) :
    G.map₂ θ ▷ ι b ≫ (invNaturality η ι u c g).hom =
      (invNaturality η ι u c f).hom ≫ ι a ◁ F.map₂ θ := by
  rw [invNaturality_hom, invNaturality_hom]
  calc
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ (G.map₂ θ ▷ ι b) ≫ (c a).inv ▷ (G.map g ≫ ι b)) ⊗≫
          ι a ◁ (η.naturality g).inv ▷ ι b ⊗≫ ι a ◁ F.map g ◁ (u b).inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b) ⊗≫
          ι a ◁ (η.app a ◁ G.map₂ θ ≫ (η.naturality g).inv) ▷ ι b ⊗≫
            ι a ◁ F.map g ◁ (u b).inv ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b) ⊗≫ ι a ◁ (η.naturality f).inv ▷ ι b ⊗≫
          ι a ◁ (F.map₂ θ ▷ (η.app b ≫ ι b) ≫ F.map g ◁ (u b).inv) ⊗≫ 𝟙 _ := by
      rw [naturality_inv_naturality]
      bicategory
    _ = _ := by
      rw [← whisker_exchange (F.map₂ θ)]
      bicategory

private theorem rightZigzag_inv_eq
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    (a : B) :
    rightZigzag (c a).inv (u a).inv = (ρ_ (η.app a)).hom ≫ (λ_ (η.app a)).inv := by
  have h : leftZigzagIso (u a) (c a) = λ_ _ ≪≫ (ρ_ _).symm :=
    Iso.ext (by rw [leftZigzagIso_hom, hu a]; rfl)
  rw [← leftZigzagIso_inv, h]
  rfl

private theorem leftZigzag_inv_eq
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    (a : B) :
    leftZigzag (c a).inv (u a).inv = (λ_ (ι a)).hom ≫ (ρ_ (ι a)).inv := by
  have h : rightZigzagIso (u a) (c a) = ρ_ _ ≪≫ (λ_ _).symm :=
    Iso.ext (by
      rw [rightZigzagIso_hom, right_triangle_of_left_triangle (u a) (c a) (hu a)]
      rfl)
  rw [← rightZigzagIso_inv, h]
  rfl

theorem invNaturality_id
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    (a : B) :
    (invNaturality η ι u c (𝟙 a)).hom ≫ ι a ◁ (F.mapId a).hom =
      (G.mapId a).hom ▷ ι a ≫ (λ_ (ι a)).hom ≫ (ρ_ (ι a)).inv := by
  rw [invNaturality_hom, naturality_id_inv]
  calc
    _ = 𝟙 _ ⊗≫ ((c a).inv ▷ (G.map (𝟙 a) ≫ ι a) ≫ (ι a ≫ η.app a) ◁ ((G.mapId a).hom ▷ ι a)) ⊗≫
          ι a ◁ ((F.mapId a).inv ▷ (η.app a ≫ ι a) ≫ F.map (𝟙 a) ◁ (u a).inv) ⊗≫
            ι a ◁ (F.mapId a).hom := by
      bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ ((G.mapId a).hom ▷ ι a) ≫ (c a).inv ▷ (𝟙 _ ≫ ι a)) ⊗≫
          ι a ◁ (𝟙 _ ◁ (u a).inv ≫ (F.mapId a).inv ▷ 𝟙 _) ⊗≫ ι a ◁ (F.mapId a).hom := by
      rw [← whisker_exchange, ← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (G.mapId a).hom ▷ ι a ⊗≫ leftZigzag (c a).inv (u a).inv ⊗≫
          ι a ◁ ((F.mapId a).inv ≫ (F.mapId a).hom) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [leftZigzag_inv_eq hu, Iso.inv_hom_id]
      bicategory

theorem invNaturality_comp
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    {a b d : B} (f : a ⟶ b) (g : b ⟶ d) :
    (invNaturality η ι u c (f ≫ g)).hom ≫ ι a ◁ (F.mapComp f g).hom =
      (G.mapComp f g).hom ▷ ι d ≫ (α_ _ _ _).hom ≫ G.map f ◁ (invNaturality η ι u c g).hom ≫
        (α_ _ _ _).inv ≫ (invNaturality η ι u c f).hom ▷ F.map g ≫ (α_ _ _ _).hom := by
  rw [invNaturality_hom, naturality_comp_inv]
  let Z : G.map f ⟶ ι a ≫ F.map f ≫ η.app b :=
    𝟙 _ ⊗≫ (c a).inv ▷ G.map f ⊗≫ ι a ◁ (η.naturality f).inv
  let W : η.app b ≫ G.map g ≫ ι d ⟶ F.map g :=
    𝟙 _ ⊗≫ (η.naturality g).inv ▷ ι d ⊗≫ F.map g ◁ (u d).inv ⊗≫ 𝟙 _
  calc
    _ = 𝟙 _ ⊗≫ ((c a).inv ▷ (G.map (f ≫ g) ≫ ι d) ≫
            (ι a ≫ η.app a) ◁ ((G.mapComp f g).hom ▷ ι d)) ⊗≫
          ι a ◁ (η.naturality f).inv ▷ G.map g ▷ ι d ⊗≫
            ι a ◁ F.map f ◁ (η.naturality g).inv ▷ ι d ⊗≫
              ι a ◁ ((F.mapComp f g).inv ▷ (η.app d ≫ ι d) ≫ F.map (f ≫ g) ◁ (u d).inv) ⊗≫
                ι a ◁ (F.mapComp f g).hom := by
      bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ ((G.mapComp f g).hom ▷ ι d) ≫ (c a).inv ▷ ((G.map f ≫ G.map g) ≫ ι d)) ⊗≫
          ι a ◁ (η.naturality f).inv ▷ G.map g ▷ ι d ⊗≫
            ι a ◁ F.map f ◁ (η.naturality g).inv ▷ ι d ⊗≫
              ι a ◁ ((F.map f ≫ F.map g) ◁ (u d).inv ≫ (F.mapComp f g).inv ▷ 𝟙 _) ⊗≫
                ι a ◁ (F.mapComp f g).hom := by
      rw [← whisker_exchange, ← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫ (c a).inv ▷ ((G.map f ≫ G.map g) ≫ ι d) ⊗≫
          ι a ◁ (η.naturality f).inv ▷ G.map g ▷ ι d ⊗≫
            ι a ◁ F.map f ◁ (η.naturality g).inv ▷ ι d ⊗≫
              ι a ◁ (F.map f ≫ F.map g) ◁ (u d).inv ⊗≫
                ι a ◁ ((F.mapComp f g).inv ≫ (F.mapComp f g).hom) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫ (c a).inv ▷ (G.map f ≫ G.map g ≫ ι d) ⊗≫
          ι a ◁ (η.naturality f).inv ▷ (G.map g ≫ ι d) ⊗≫
            ι a ◁ F.map f ◁ rightZigzag (c b).inv (u b).inv ▷ (G.map g ≫ ι d) ⊗≫
              ι a ◁ F.map f ◁ (η.naturality g).inv ▷ ι d ⊗≫
                ι a ◁ F.map f ◁ F.map g ◁ (u d).inv ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id, rightZigzag_inv_eq hu]
      bicategory
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫ Z ▷ (G.map g ≫ ι d) ⊗≫
          (ι a ≫ F.map f ≫ η.app b) ◁ (c b).inv ▷ (G.map g ≫ ι d) ⊗≫
            (ι a ≫ F.map f) ◁ ((u b).inv ▷ (η.app b ≫ G.map g ≫ ι d) ≫ 𝟙 _ ◁ W) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫ Z ▷ (G.map g ≫ ι d) ⊗≫
          (ι a ≫ F.map f ≫ η.app b) ◁ (c b).inv ▷ (G.map g ≫ ι d) ⊗≫
            (ι a ≫ F.map f) ◁ ((η.app b ≫ ι b) ◁ W ≫ (u b).inv ▷ F.map g) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange (u b).inv]
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫
          (Z ▷ (G.map g ≫ ι d) ≫ (ι a ≫ F.map f ≫ η.app b) ◁ (invNaturality η ι u c g).hom) ⊗≫
            (ι a ≫ F.map f) ◁ (u b).inv ▷ F.map g ⊗≫ 𝟙 _ := by
      rw [invNaturality_hom]
      bicategory
    _ = 𝟙 _ ⊗≫ (G.mapComp f g).hom ▷ ι d ⊗≫
          (G.map f ◁ (invNaturality η ι u c g).hom ≫ Z ▷ (ι b ≫ F.map g)) ⊗≫
            (ι a ≫ F.map f) ◁ (u b).inv ▷ F.map g ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      rw [invNaturality_hom, invNaturality_hom]
      bicategory

variable (η ι u c) in
def invTrans
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv) :
    G ⟶ F where
  app := ι
  naturality f := invNaturality η ι u c f
  naturality_naturality θ := invNaturality_naturality θ
  naturality_id a := invNaturality_id hu a
  naturality_comp f g := invNaturality_comp hu f g

private theorem unit_naturality
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    {a b : B} (f : a ⟶ b) :
    F.map f ◁ (u b).hom ≫ (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ ι b ≫ (α_ _ _ _).hom ≫
        η.app a ◁ (invNaturality η ι u c f).hom ≫ (α_ _ _ _).inv =
      ((ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv) ≫ (u a).hom ▷ F.map f := by
  rw [invNaturality_hom]
  calc
    _ = 𝟙 _ ⊗≫ F.map f ◁ (u b).hom ⊗≫ (η.naturality f).hom ▷ ι b ⊗≫
          (η.app a ◁ (c a).inv ⊗≫ ((u a).inv ≫ (u a).hom) ▷ η.app a) ▷ (G.map f ≫ ι b) ⊗≫
            η.app a ◁ ι a ◁ (η.naturality f).inv ▷ ι b ⊗≫
              η.app a ◁ ι a ◁ F.map f ◁ (u b).inv ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = 𝟙 _ ⊗≫ F.map f ◁ (u b).hom ⊗≫ (η.naturality f).hom ▷ ι b ⊗≫
          (rightZigzag (c a).inv (u a).inv ⊗≫ (u a).hom ▷ η.app a) ▷ (G.map f ≫ ι b) ⊗≫
            η.app a ◁ ι a ◁ (η.naturality f).inv ▷ ι b ⊗≫
              η.app a ◁ ι a ◁ F.map f ◁ (u b).inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ (F.map f ◁ (u b).hom ≫ (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ ι b) ≫
            (u a).hom ▷ ((η.app a ≫ G.map f) ≫ ι b)) ⊗≫
          (η.app a ≫ ι a) ◁ (η.naturality f).inv ▷ ι b ⊗≫
            (η.app a ≫ ι a) ◁ F.map f ◁ (u b).inv ⊗≫ 𝟙 _ := by
      rw [rightZigzag_inv_eq hu]
      bicategory
    _ = 𝟙 _ ⊗≫ ((u a).hom ▷ (F.map f ≫ 𝟙 _) ≫
            (η.app a ≫ ι a) ◁ (F.map f ◁ (u b).hom ≫ (α_ _ _ _).inv ≫
              (η.naturality f).hom ▷ ι b)) ⊗≫
          (η.app a ≫ ι a) ◁ (η.naturality f).inv ▷ ι b ⊗≫
            (η.app a ≫ ι a) ◁ F.map f ◁ (u b).inv ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (u a).hom ▷ F.map f ⊗≫ (η.app a ≫ ι a) ◁ (F.map f ◁ (u b).hom ⊗≫
          ((η.naturality f).hom ≫ (η.naturality f).inv) ▷ ι b ⊗≫ F.map f ◁ (u b).inv) ⊗≫
            𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (u a).hom ▷ F.map f ⊗≫
          (η.app a ≫ ι a) ◁ F.map f ◁ ((u b).hom ≫ (u b).inv) ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id]
      bicategory
    _ = _ := by
      rw [Iso.hom_inv_id]
      bicategory

private theorem counit_naturality
    (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)
    {a b : B} (f : a ⟶ b) :
    G.map f ◁ (c b).hom ≫ (ρ_ (G.map f)).hom ≫ (λ_ (G.map f)).inv =
      ((α_ _ _ _).inv ≫ (invNaturality η ι u c f).hom ▷ η.app b ≫ (α_ _ _ _).hom ≫
        ι a ◁ (η.naturality f).hom ≫ (α_ _ _ _).inv) ≫ (c a).hom ▷ G.map f := by
  rw [invNaturality_hom]
  symm
  calc
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b) ▷ η.app b ⊗≫
          ι a ◁ (η.naturality f).inv ▷ ι b ▷ η.app b ⊗≫
            ι a ◁ F.map f ◁ ((u b).inv ▷ η.app b ⊗≫ leftZigzag (u b).hom (c b).hom) ⊗≫
              ι a ◁ (η.naturality f).hom ⊗≫ (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [hu]
      bicategory
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b ≫ η.app b) ⊗≫
          ι a ◁ (η.naturality f).inv ▷ ι b ▷ η.app b ⊗≫
            ι a ◁ F.map f ◁ ((u b).inv ≫ (u b).hom) ▷ η.app b ⊗≫
              ι a ◁ F.map f ◁ η.app b ◁ (c b).hom ⊗≫
                ι a ◁ (η.naturality f).hom ⊗≫ (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b ≫ η.app b) ⊗≫
          ι a ◁ ((η.naturality f).inv ▷ (ι b ≫ η.app b) ≫
            (F.map f ≫ η.app b) ◁ (c b).hom) ⊗≫
            ι a ◁ (η.naturality f).hom ⊗≫ (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = 𝟙 _ ⊗≫ (c a).inv ▷ (G.map f ≫ ι b ≫ η.app b) ⊗≫
          ι a ◁ ((η.app a ≫ G.map f) ◁ (c b).hom ≫ (η.naturality f).inv ▷ 𝟙 _) ⊗≫
            ι a ◁ (η.naturality f).hom ⊗≫ (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((c a).inv ▷ (G.map f ≫ ι b ≫ η.app b) ≫
            (ι a ≫ η.app a) ◁ (G.map f ◁ (c b).hom)) ⊗≫
          ι a ◁ ((η.naturality f).inv ≫ (η.naturality f).hom) ⊗≫
            (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ (G.map f ◁ (c b).hom) ≫ (c a).inv ▷ (G.map f ≫ 𝟙 _)) ⊗≫
          ι a ◁ ((η.naturality f).inv ≫ (η.naturality f).hom) ⊗≫
            (c a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ G.map f ◁ (c b).hom ⊗≫ ((c a).inv ≫ (c a).hom) ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

variable (η ι u c)
  (hu : ∀ a, leftZigzag (u a).hom (c a).hom = (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv)

def invTransUnitIso : 𝟙 F ≅ η ≫ invTrans η ι u c hu :=
  isoMk u fun f => by
    rw [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact unit_naturality hu f

def invTransCounitIso : invTrans η ι u c hu ≫ η ≅ 𝟙 G :=
  isoMk c fun f => by
    rw [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact counit_naturality hu f

end StrongTrans

private theorem leftZigzag_eqToIso {a b : C} (e : Bicategory.Equivalence a b) {f : a ⟶ b}
    (h : e.hom = f) :
    leftZigzag (e.unit ≪≫ whiskerRightIso (eqToIso h) e.inv).hom
        (whiskerLeftIso e.inv (eqToIso h).symm ≪≫ e.counit).hom = (λ_ f).hom ≫ (ρ_ f).inv := by
  subst h
  simpa using e.left_triangle_hom

def StrongTrans.equivalenceOfApp {F G : B ⥤ᵖ C} (η : F ⟶ G)
    (e : ∀ a, Bicategory.Equivalence (F.obj a) (G.obj a)) (he : ∀ a, (e a).hom = η.app a) :
    Bicategory.Equivalence F G :=
  Equivalence.mkOfAdjointifyCounit
    (invTransUnitIso η (fun a => (e a).inv)
      (fun a => (e a).unit ≪≫ whiskerRightIso (eqToIso (he a)) _)
      (fun a => whiskerLeftIso _ (eqToIso (he a)).symm ≪≫ (e a).counit)
      (fun a => leftZigzag_eqToIso (e a) (he a)))
    (invTransCounitIso η (fun a => (e a).inv)
      (fun a => (e a).unit ≪≫ whiskerRightIso (eqToIso (he a)) _)
      (fun a => whiskerLeftIso _ (eqToIso (he a)).symm ≪≫ (e a).counit)
      (fun a => leftZigzag_eqToIso (e a) (he a)))

theorem StrongTrans.equivalenceOfApp_hom {F G : B ⥤ᵖ C} (η : F ⟶ G)
    (e : ∀ a, Bicategory.Equivalence (F.obj a) (G.obj a)) (he : ∀ a, (e a).hom = η.app a) :
    (StrongTrans.equivalenceOfApp η e he).hom = η :=
  rfl

end Pseudofunctor

end CategoryTheory
