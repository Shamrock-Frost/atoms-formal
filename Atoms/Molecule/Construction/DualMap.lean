import Atoms.Molecule.Construction.Dual
import Atoms.Molecule.RegularComplex.Basic

universe u v

open CategoryTheory Order

namespace Atoms.Molecule.OGP

variable (J : ℕ → Bool)

section Predicates

variable {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}

theorem IsMorphism.dual (hf : IsMorphism f) : IsMorphism (P := dual P J) (Q := dual Q J) f :=
  ⟨fun x α => by
    rw [faces_dual, faces_dual, hf.grade_eq]
    exact hf.bijOn_faces x _⟩

theorem isMorphism_dual_iff : IsMorphism (P := dual P J) (Q := dual Q J) f ↔ IsMorphism f :=
  ⟨fun hf => ⟨fun x α => by
    simpa only [faces_dual, hf.grade_eq, Bool.xor_xor_cancel_left] using
      hf.bijOn_faces x (xor (J (grade ℕ x)) α)⟩, IsMorphism.dual J⟩

theorem isMorphism_dual_iff_of_forall (h : ∀ x : P, J (grade ℕ x) = false) :
    IsMorphism (Q := dual Q J) f ↔ IsMorphism f := by
  have hfaces (hd : ∀ x, grade ℕ (f x) = grade ℕ x) (x : P) (α : Bool) :
      (dual Q J).faces α (f x) = Q.faces α (f x) := by
    rw [faces_dual, hd, h, Bool.false_xor]
  exact ⟨fun hf => ⟨fun x α => hfaces hf.grade_eq x α ▸ hf.bijOn_faces x α⟩,
    fun hf => ⟨fun x α => (hfaces hf.grade_eq x α).symm ▸ hf.bijOn_faces x α⟩⟩

theorem IsMap.dual (hf : IsMap f) : IsMap (P := dual P J) (Q := dual Q J) f where
  isClosedMap := hf.isClosedMap
  finalOn x n α := by
    rw [boundary_dual, boundary_dual]
    exact hf.finalOn x n _

theorem isMap_dual_iff : IsMap (P := dual P J) (Q := dual Q J) f ↔ IsMap f :=
  ⟨fun hf => ⟨hf.isClosedMap, fun x n α => by
    simpa only [boundary_dual, Bool.xor_xor_cancel_left] using hf.finalOn x n (xor (J (n + 1)) α)⟩,
    IsMap.dual J⟩

theorem isMap_dual_left_iff : IsMap (P := dual P J) (Q := Q) f ↔ IsMap (P := P) (Q := dual Q J) f :=
  ⟨fun hf => ⟨hf.isClosedMap, fun x n α => by
    simpa only [boundary_dual, Bool.xor_xor_cancel_left] using
      hf.finalOn x n (xor (J (n + 1)) α)⟩,
    fun hf => ⟨hf.isClosedMap, fun x n α => by
      simpa only [boundary_dual, Bool.xor_xor_cancel_left] using
        hf.finalOn x n (xor (J (n + 1)) α)⟩⟩

theorem IsRDC.dual {P : OGP.{u}} (hP : P.IsRDC) : (dual P J).IsRDC := fun x =>
  (isMoleculeIn_dual J).2 (hP x)

end Predicates

section Arrows

variable {P Q : OGP.{u}}

def dualHom (f : P ⟶ Q) : dual P J ⟶ dual Q J :=
  ConcreteCategory.ofHom ⟨f, (isMorphism f).dual J⟩

@[simp] theorem dualHom_apply (f : P ⟶ Q) (x : P) : dualHom J f x = f x :=
  rfl

instance isInclusion_dualHom (f : P ⟶ Q) [IsInclusion f] : IsInclusion (dualHom J f) :=
  ⟨IsInclusion.injective (f := f)⟩

end Arrows

@[simps obj]
def dualFunctor : OGP.{u} ⥤ OGP.{u} where
  obj P := dual P J
  map := dualHom J

variable {J}

section Arrows

variable {P Q : OGP.{u}}

@[simp] theorem dualFunctor_map_apply (f : P ⟶ Q) (x : P) : (dualFunctor J).map f x = f x :=
  rfl

instance isInclusion_dualFunctor_map (f : P ⟶ Q) [IsInclusion f] :
    IsInclusion ((dualFunctor J).map f) :=
  inferInstanceAs (IsInclusion (dualHom J f))

variable (J) in
def dualDualIso (P : OGP.{u}) : dual (dual P J) J ≅ P :=
  isoMk (OrderIso.refl P) fun {x _} h => by
    rw [orient_dual, orient_dual]
    exact (Bool.xor_xor_cancel_left _ _).symm

@[simp] theorem dualDualIso_hom_apply (x : P) : (dualDualIso J P).hom x = x :=
  rfl

@[simp] theorem dualDualIso_inv_apply (x : P) : (dualDualIso J P).inv x = x :=
  rfl

variable (J) in
def dualIsoOfForall (P : OGP.{u}) (h : ∀ x : P, J (grade ℕ x) = false) : dual P J ≅ P :=
  isoMk (OrderIso.refl P) fun {x _} _ => by
    rw [orient_dual, h x, Bool.false_xor]
    rfl

def homOfDual (f : P ⟶ dual Q J) (h : ∀ x : P, J (grade ℕ x) = false) : P ⟶ Q :=
  ConcreteCategory.ofHom ⟨f, (isMorphism_dual_iff_of_forall J h).1 (isMorphism f)⟩

instance (f : P ⟶ dual Q J) [IsInclusion f] (h : ∀ x : P, J (grade ℕ x) = false) :
    IsInclusion (homOfDual f h) :=
  ⟨IsInclusion.injective (f := f)⟩

end Arrows

variable (J) in
@[simps obj_toOGP]
def RDCpxDown.dualFunctor : RDCpxDown.{u} ⥤ RDCpxDown.{u} where
  obj P := ⟨dual P.toOGP J, P.isRDC.dual J⟩
  map f := ConcreteCategory.ofHom ⟨ConcreteCategory.hom f, (ConcreteCategory.hom f).isMap.dual J⟩

@[simp] theorem RDCpxDown.dualFunctor_map_apply {P Q : RDCpxDown.{u}} (f : P ⟶ Q) (x : P) :
    ConcreteCategory.hom ((dualFunctor J).map f) x = ConcreteCategory.hom f x :=
  rfl

variable (J) in
abbrev RDCpx.dualFunctor : RDCpx.{u} ⥤ RDCpx.{u} :=
  (RDCpxDown.dualFunctor J).mapWideSubcategory fun _ _ _ hf => hf

variable (J) in
abbrev RDCpxEq.dualFunctor : RDCpxEq.{u} ⥤ RDCpxEq.{u} :=
  (RDCpxDown.dualFunctor J).mapWideSubcategory fun _ _ _ hf => hf

variable (J) in
theorem RDCpxEq.toRDCpx_comp_dualFunctor :
    toRDCpx.{u} ⋙ RDCpx.dualFunctor J = RDCpxEq.dualFunctor J ⋙ toRDCpx :=
  rfl

@[simp] theorem RDCpx.dualFunctor_map_ofInclusion {P Q : RDCpx.{u}}
    (f : P.obj.toOGP ⟶ Q.obj.toOGP) [IsInclusion f] :
    (dualFunctor J).map (ofInclusion f) =
      @ofInclusion ((dualFunctor J).obj P) ((dualFunctor J).obj Q) ((OGP.dualFunctor J).map f)
        (isInclusion_dualFunctor_map f) :=
  rfl

variable (J) in
def RDCpx.dualHomEquiv (P Q : RDCpx.{u}) :
    (P ⟶ (dualFunctor J).obj Q) ≃ ((dualFunctor J).obj P ⟶ Q) where
  toFun g := ⟨ConcreteCategory.ofHom ⟨ConcreteCategory.hom g.hom,
    (isMap_dual_left_iff J).2 (ConcreteCategory.hom g.hom).isMap⟩, by exact g.property⟩
  invFun g := ⟨ConcreteCategory.ofHom ⟨ConcreteCategory.hom g.hom,
    (isMap_dual_left_iff J).1 (ConcreteCategory.hom g.hom).isMap⟩, by exact g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem RDCpx.dualHomEquiv_apply_apply {P Q : RDCpx.{u}}
    (g : P ⟶ (dualFunctor J).obj Q) (x : P.obj) :
    ConcreteCategory.hom (dualHomEquiv J P Q g).hom x = ConcreteCategory.hom g.hom x :=
  rfl

end Atoms.Molecule.OGP
