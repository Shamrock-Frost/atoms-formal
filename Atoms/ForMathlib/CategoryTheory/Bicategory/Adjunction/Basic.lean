import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

def adjointifyUnit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : 𝟙 a ≅ f ≫ g :=
  η ≪≫ whiskerRightIso ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) g

theorem adjointifyUnit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso (adjointifyUnit η ε) ε = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  simp only [adjointifyUnit, leftZigzagIso_hom, Iso.trans_hom, whiskerRightIso_hom,
    Iso.symm_hom, rightZigzagIso_hom, leftZigzag, rightZigzag]
  calc
    _ = 𝟙 _ ⊗≫ η.hom ▷ f ⊗≫
          (((ρ_ f).inv ≫ (f ◁ ε.inv ⊗≫ η.inv ▷ f) ≫ (λ_ f).hom) ▷ (g ≫ f) ≫ f ◁ ε.hom) := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.hom ▷ f ⊗≫
          (f ◁ ε.hom ≫ ((ρ_ f).inv ≫ (f ◁ ε.inv ⊗≫ η.inv ▷ f) ≫ (λ_ f).hom) ▷ 𝟙 b) := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ η.hom ▷ f ⊗≫ f ◁ (ε.hom ≫ ε.inv) ⊗≫ η.inv ▷ f ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (η.hom ≫ η.inv) ▷ f ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id ε]; bicategory
    _ = _ := by
      rw [Iso.hom_inv_id η]; bicategory

def Equivalence.mkOfAdjointifyUnit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := adjointifyUnit η ε
  counit := ε
  left_triangle := adjointifyUnit_left_triangle η ε

namespace Equivalence

@[simps]
def toAdjunction (e : a ≌ b) : e.hom ⊣ e.inv where
  unit := e.unit.hom
  counit := e.counit.hom
  left_triangle := e.left_triangle_hom
  right_triangle := e.right_triangle_hom

variable (e : a ≌ b) (e' : b ≌ c)

def compUnitIso : 𝟙 a ≅ (e.hom ≫ e'.hom) ≫ e'.inv ≫ e.inv :=
  e.unit ≪⊗≫ whiskerRightIso (whiskerLeftIso e.hom e'.unit) e.inv ≪⊗≫ Iso.refl _

def compCounitIso : (e'.inv ≫ e.inv) ≫ e.hom ≫ e'.hom ≅ 𝟙 c :=
  Iso.refl _ ≪⊗≫ whiskerRightIso (whiskerLeftIso e'.inv e.counit) e'.hom ≪⊗≫ e'.counit

theorem compUnitIso_hom :
    (compUnitIso e e').hom = Adjunction.compUnit e.toAdjunction e'.toAdjunction := by
  simp only [compUnitIso, bicategoricalIsoComp, Adjunction.compUnit, Iso.trans_hom,
    whiskerRightIso_hom, whiskerLeftIso_hom, Iso.refl_hom, bicategoricalComp, toAdjunction_unit]
  bicategory

theorem compCounitIso_hom :
    (compCounitIso e e').hom = Adjunction.compCounit e.toAdjunction e'.toAdjunction := by
  simp only [compCounitIso, bicategoricalIsoComp, Adjunction.compCounit, Iso.trans_hom,
    whiskerRightIso_hom, whiskerLeftIso_hom, Iso.refl_hom, bicategoricalComp, toAdjunction_counit]
  bicategory

def comp : a ≌ c where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  unit := compUnitIso e e'
  counit := compCounitIso e e'
  left_triangle := Iso.ext <| by
    rw [leftZigzagIso_hom, compUnitIso_hom, compCounitIso_hom]
    exact Adjunction.comp_left_triangle_aux _ _

theorem comp_toAdjunction : (e.comp e').toAdjunction = e.toAdjunction.comp e'.toAdjunction :=
  Adjunction.ext (compUnitIso_hom e e') (compCounitIso_hom e e')

end Equivalence

namespace Adjunction

variable {η : 𝟙 a ⟶ f ≫ g} {ε : g ≫ f ⟶ 𝟙 b}

theorem leftZigzag_eq_iff :
    leftZigzag η ε = (λ_ f).hom ≫ (ρ_ f).inv ↔
      (λ_ f).inv ≫ η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε ≫ (ρ_ f).hom = 𝟙 f := by
  have h : (λ_ f).inv ≫ η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε ≫ (ρ_ f).hom =
      (λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom := by
    simp only [bicategoricalComp]; bicategory
  rw [h, Iso.inv_comp_eq, Category.comp_id, Iso.eq_comp_inv]

theorem rightZigzag_eq_iff :
    rightZigzag η ε = (ρ_ g).hom ≫ (λ_ g).inv ↔
      (ρ_ g).inv ≫ g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g ≫ (λ_ g).hom = 𝟙 g := by
  have h : (ρ_ g).inv ≫ g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g ≫ (λ_ g).hom =
      (ρ_ g).inv ≫ rightZigzag η ε ≫ (λ_ g).hom := by
    simp only [bicategoricalComp]; bicategory
  rw [h, Iso.inv_comp_eq, Category.comp_id, Iso.eq_comp_inv]

def ofUnitorTriangles (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
    (h₁ : (λ_ f).inv ≫ η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε ≫ (ρ_ f).hom = 𝟙 f)
    (h₂ : (ρ_ g).inv ≫ g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g ≫ (λ_ g).hom = 𝟙 g) : f ⊣ g where
  unit := η
  counit := ε
  left_triangle := leftZigzag_eq_iff.2 h₁
  right_triangle := rightZigzag_eq_iff.2 h₂

end Adjunction

end Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace Pseudofunctor

def mapEquivalence (F : Pseudofunctor B C) {a b : B} (e : Bicategory.Equivalence a b) :
    Bicategory.Equivalence (F.obj a) (F.obj b) where
  hom := F.map e.hom
  inv := F.map e.inv
  unit := (F.mapId a).symm ≪≫ F.map₂Iso e.unit ≪≫ F.mapComp e.hom e.inv
  counit := (F.mapComp e.inv e.hom).symm ≪≫ F.map₂Iso e.counit ≪≫ F.mapId b
  left_triangle := Iso.ext (F.mapAdjunction e.toAdjunction).left_triangle

end Pseudofunctor

def StrictPseudofunctor.mapEquivalence (F : StrictPseudofunctor B C) {a b : B}
    (e : Bicategory.Equivalence a b) : Bicategory.Equivalence (F.obj a) (F.obj b) :=
  F.toPseudofunctor.mapEquivalence e

end CategoryTheory
