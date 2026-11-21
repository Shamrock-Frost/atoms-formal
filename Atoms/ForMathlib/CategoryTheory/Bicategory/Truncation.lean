import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.IsomorphismClasses

namespace CategoryTheory.Bicategory

universe w v u w₂ v₂ u₂

structure Truncation (B : Type u) [Bicategory.{w, v} B] : Type u where
  as : B

namespace Truncation

variable {B : Type u} [Bicategory.{w, v} B]

instance : Category.{v} (Truncation B) where
  Hom a b := Quotient (isIsomorphicSetoid (a.as ⟶ b.as))
  id a := Quotient.mk _ (𝟙 a.as)
  comp := Quotient.map₂ (· ≫ ·) fun _ _ ⟨e⟩ _ _ ⟨e'⟩ =>
    ⟨whiskerRightIso e _ ≪≫ whiskerLeftIso _ e'⟩
  id_comp := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound ⟨λ_ f⟩
  comp_id := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound ⟨ρ_ f⟩
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound ⟨α_ f g h⟩

def homMk {a b : B} (f : a ⟶ b) : mk a ⟶ mk b :=
  Quotient.mk (isIsomorphicSetoid (a ⟶ b)) f

theorem homMk_eq_homMk_iff {a b : B} (f g : a ⟶ b) : homMk f = homMk g ↔ Nonempty (f ≅ g) :=
  Quotient.eq (r := isIsomorphicSetoid (a ⟶ b))

@[reassoc, simp]
theorem homMk_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  rfl

@[simp]
theorem homMk_id (a : B) : homMk (𝟙 a) = 𝟙 (mk a) :=
  rfl

theorem homMk_surjective {a b : B} (φ : mk a ⟶ mk b) : ∃ f : a ⟶ b, homMk f = φ :=
  Quotient.exists_rep (s := isIsomorphicSetoid (a ⟶ b)) φ

def isoMk {a b : B} (e : a ≌ b) : mk a ≅ mk b where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := (homMk_eq_homMk_iff _ _).2 ⟨e.unit.symm⟩
  inv_hom_id := (homMk_eq_homMk_iff _ _).2 ⟨e.counit⟩

variable {C : Type u₂} [Bicategory.{w₂, v₂} C]

def map (F : B ⥤ᵖ C) : Truncation B ⥤ Truncation C where
  obj a := mk (F.obj a.as)
  map {a b} := Quotient.map (sa := isIsomorphicSetoid (a.as ⟶ b.as))
    (sb := isIsomorphicSetoid (F.obj a.as ⟶ F.obj b.as)) F.map
    fun _ _ ⟨e⟩ => ⟨F.map₂Iso e⟩
  map_id a := Quotient.sound ⟨F.mapId a.as⟩
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact Quotient.sound ⟨F.mapComp f g⟩

@[simp]
theorem map_map_homMk (F : B ⥤ᵖ C) {a b : B} (f : a ⟶ b) :
    (map F).map (homMk f) = homMk (F.map f) :=
  rfl

end Truncation

end CategoryTheory.Bicategory
