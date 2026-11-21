import Atoms.Molecule.Construction.GrayProductMap
import Mathlib.CategoryTheory.Monoidal.Category

universe u

open CategoryTheory MonoidalCategory Order

namespace Atoms.Molecule.OGP

variable {P Q R P' Q' : OGP.{u}}

def grayProductMap (f : P ⟶ P') (g : Q ⟶ Q') : grayProduct P Q ⟶ grayProduct P' Q' :=
  ConcreteCategory.ofHom ⟨fun p => (f p.1, g p.2), isMorphism_prodMap (isMorphism f) (isMorphism g)⟩

@[simp] theorem grayProductMap_apply (f : P ⟶ P') (g : Q ⟶ Q') (p : grayProduct P Q) :
    grayProductMap f g p = (f p.1, g p.2) :=
  rfl

instance instIsInclusionGrayProductMap (f : P ⟶ P') (g : Q ⟶ Q') [IsInclusion f]
    [IsInclusion g] : IsInclusion (grayProductMap f g) :=
  ⟨fun _ _ h => Prod.ext (IsInclusion.injective (f := f) (congrArg Prod.fst h))
    (IsInclusion.injective (f := g) (congrArg Prod.snd h))⟩

def grayProductAssoc (P Q R : OGP.{u}) :
    grayProduct (grayProduct P Q) R ≅ grayProduct P (grayProduct Q R) :=
  OGP.isoMk (OrderIso.prodAssoc P Q R) fun {p q} h => by
    rcases p with ⟨⟨x, y⟩, z⟩
    rcases q with ⟨⟨x', y'⟩, z'⟩
    rcases Prod.covBy_iff.1 h with ⟨hxy, hz⟩ | ⟨hz, hxy⟩
    · change z' = z at hz
      subst z'
      rcases Prod.covBy_iff.1 hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · change y' = y at hy
        subst y'
        have ht : ((x', (y, z)) : grayProduct P (grayProduct Q R)) ⋖ (x, (y, z)) :=
          Prod.covBy_iff.2 (.inl ⟨hx, rfl⟩)
        change (grayProduct P (grayProduct Q R)).orient ht = _
        rw [grayProduct_orient_of_covBy_fst (P := grayProduct P Q) hxy z,
          grayProduct_orient_of_covBy_fst (P := P) (Q := Q) hx y,
          grayProduct_orient_of_covBy_fst (P := P) (Q := grayProduct Q R) hx (y, z)]
      · change x' = x at hx
        subst x'
        have hyz : ((y', z) : grayProduct Q R) ⋖ (y, z) :=
          Prod.covBy_iff.2 (.inl ⟨hy, rfl⟩)
        have ht : ((x, (y', z)) : grayProduct P (grayProduct Q R)) ⋖ (x, (y, z)) :=
          Prod.covBy_iff.2 (.inr ⟨hyz, rfl⟩)
        change (grayProduct P (grayProduct Q R)).orient ht = _
        rw [grayProduct_orient_of_covBy_fst (P := grayProduct P Q) hxy z,
          grayProduct_orient_of_covBy_snd (P := P) (Q := Q) x hy,
          grayProduct_orient_of_covBy_snd (P := P) (Q := grayProduct Q R) x hyz,
          grayProduct_orient_of_covBy_fst (P := Q) (Q := R) hy z]
    · change (x', y') = (x, y) at hxy
      obtain ⟨hx, hy⟩ := Prod.mk.inj hxy
      subst x'
      subst y'
      have hyz : ((y, z') : grayProduct Q R) ⋖ (y, z) :=
        Prod.covBy_iff.2 (.inr ⟨hz, rfl⟩)
      have ht : ((x, (y, z')) : grayProduct P (grayProduct Q R)) ⋖ (x, (y, z)) :=
        Prod.covBy_iff.2 (.inr ⟨hyz, rfl⟩)
      change (grayProduct P (grayProduct Q R)).orient ht = _
      rw [grayProduct_orient_of_covBy_snd (P := grayProduct P Q) (Q := R) (x, y) hz,
        grayProduct_orient_of_covBy_snd (P := P) (Q := grayProduct Q R) x hyz,
        grayProduct_orient_of_covBy_snd (P := Q) (Q := R) y hz,
        Prod.grade_eq_add, Nat.bodd_add, Bool.xor_assoc]

@[simp] theorem grayProductAssoc_hom_apply (p : grayProduct (grayProduct P Q) R) :
    (grayProductAssoc P Q R).hom p = (p.1.1, (p.1.2, p.2)) :=
  rfl

@[simp] theorem grayProductAssoc_inv_apply (p : grayProduct P (grayProduct Q R)) :
    (grayProductAssoc P Q R).inv p = ((p.1, p.2.1), p.2.2) :=
  rfl

private theorem grade_point (x : point.{u}) : grade ℕ x = 0 :=
  (isMin_point x).grade (𝕆 := ℕ) |>.eq_bot

def grayProductLeftUnitor (P : OGP.{u}) : grayProduct point.{u} P ≅ P :=
  OGP.isoMk
    { toFun := Prod.snd
      invFun := fun x => (⊤, x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := ⟨fun h => ⟨le_of_eq rfl, h⟩, fun h => h.2⟩ }
    fun {p q} h => by
    rcases p with ⟨u, y⟩
    rcases q with ⟨u', y'⟩
    obtain rfl : u = u' := rfl
    have hy : y' ⋖ y := (Prod.mk_covBy_mk_iff_right (a := u)).1 h
    rw [grayProduct_orient_of_covBy_snd u hy, grade_point, Nat.bodd_zero, Bool.false_xor]

@[simp] theorem grayProductLeftUnitor_hom_apply (p : grayProduct point.{u} P) :
    (grayProductLeftUnitor P).hom p = p.2 :=
  rfl

@[simp] theorem grayProductLeftUnitor_inv_apply (x : P) :
    (grayProductLeftUnitor P).inv x = (⊤, x) :=
  rfl

def grayProductRightUnitor (P : OGP.{u}) : grayProduct P point.{u} ≅ P :=
  OGP.isoMk
    { toFun := Prod.fst
      invFun := fun x => (x, ⊤)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := ⟨fun h => ⟨h, le_of_eq rfl⟩, fun h => h.1⟩ }
    fun {p q} h => by
    rcases p with ⟨x, u⟩
    rcases q with ⟨x', u'⟩
    obtain rfl : u = u' := rfl
    have hx : x' ⋖ x := (Prod.mk_covBy_mk_iff_left (b := u)).1 h
    rw [grayProduct_orient_of_covBy_fst hx u]

@[simp] theorem grayProductRightUnitor_hom_apply (p : grayProduct P point.{u}) :
    (grayProductRightUnitor P).hom p = p.1 :=
  rfl

@[simp] theorem grayProductRightUnitor_inv_apply (x : P) :
    (grayProductRightUnitor P).inv x = (x, ⊤) :=
  rfl

instance instMonoidalCategory : MonoidalCategory OGP.{u} :=
  letI : MonoidalCategoryStruct OGP.{u} :=
    { tensorObj := grayProduct
      whiskerLeft := fun P _ _ g => grayProductMap (𝟙 P) g
      whiskerRight := fun f Q => grayProductMap f (𝟙 Q)
      tensorHom := grayProductMap
      tensorUnit := point
      associator := grayProductAssoc
      leftUnitor := grayProductLeftUnitor
      rightUnitor := grayProductRightUnitor }
  .ofTensorHom
    (id_tensorHom_id := fun _ _ => rfl)
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => rfl)
    (associator_naturality := fun _ _ _ => rfl)
    (leftUnitor_naturality := fun _ => rfl)
    (rightUnitor_naturality := fun _ => rfl)
    (pentagon := fun _ _ _ _ => rfl)
    (triangle := fun _ _ => rfl)

end Atoms.Molecule.OGP
