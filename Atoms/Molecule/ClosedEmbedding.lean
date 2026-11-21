import Atoms.Molecule.RegularComplex.CartesianAtom
import Mathlib.Data.Fintype.Inv

universe u

open CategoryTheory

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

def codRestrict (f : P ⟶ Q) (C : LowerSet Q) (h : ∀ x, f x ∈ C) : P ⟶ Q.restrict C :=
  ConcreteCategory.ofHom ⟨fun x => ⟨f x, h x⟩,
    IsMorphism.of_comp_of_injective (g := incl C) (isMorphism (incl C)) IsInclusion.injective
      (isMorphism f)⟩

@[simp] theorem codRestrict_apply (f : P ⟶ Q) (C : LowerSet Q) (h : ∀ x, f x ∈ C) (x : P) :
    codRestrict f C h x = ⟨f x, h x⟩ :=
  rfl

@[reassoc (attr := simp)]
theorem codRestrict_incl (f : P ⟶ Q) (C : LowerSet Q) (h : ∀ x, f x ∈ C) :
    codRestrict f C h ≫ incl C = f := by
  ext x
  rfl

instance (f : P ⟶ Q) [IsInclusion f] (C : LowerSet Q) (h : ∀ x, f x ∈ C) :
    IsInclusion (codRestrict f C h) :=
  ⟨fun _ _ hxy => IsInclusion.injective (f := f) (congrArg Subtype.val hxy)⟩

theorem map_codRestrict (f : P ⟶ Q) (C : LowerSet Q) (h : ∀ x, f x ∈ C) (U : LowerSet P) :
    map (codRestrict f C h) U = comap (incl C) (map f U) := by
  rw [← comap_map (incl C) (map (codRestrict f C h) U), ← map_comp, codRestrict_incl]

section Inclusion

variable (f : P ⟶ Q) [IsInclusion f]

theorem isIso_codRestrict {C : LowerSet Q} (hC : map f ⊤ = C) :
    IsIso (codRestrict f C fun x => hC ▸ ⟨x, LowerSet.mem_top, rfl⟩) := by
  refine (isIso_iff_bijective _).2 ⟨fun _ _ hxy => IsInclusion.injective (f := f)
    (congrArg Subtype.val hxy), fun y => ?_⟩
  obtain ⟨x, -, hx⟩ : y.1 ∈ map f ⊤ := hC ▸ y.2
  exact ⟨x, Subtype.ext hx⟩

theorem exists_iso_restrict {C : LowerSet Q} (hC : map f ⊤ = C) :
    ∃ e : P ≅ Q.restrict C, e.hom ≫ incl C = f :=
  haveI := isIso_codRestrict f hC
  ⟨asIso (codRestrict f C fun x => hC ▸ ⟨x, LowerSet.mem_top, rfl⟩), codRestrict_incl _ _ _⟩

theorem exists_iso_restrict_map (S : LowerSet P) :
    ∃ e : P.restrict S ≅ Q.restrict (map f S), e.hom ≫ incl _ = incl S ≫ f :=
  exists_iso_restrict (incl S ≫ f) (by rw [map_comp, map_incl_top])

omit [IsInclusion f] in
private theorem mem_range_of_mem {C : LowerSet Q} (hC : map f ⊤ = C) (y : Q.restrict C) :
    y.1 ∈ Set.range f :=
  let ⟨x, _, hx⟩ : y.1 ∈ map f ⊤ := hC ▸ y.2
  ⟨x, hx⟩

def isoRestrictOfFintype [Fintype P] [DecidableEq Q] {C : LowerSet Q} (hC : map f ⊤ = C) :
    P ≅ Q.restrict C where
  hom := codRestrict f C fun x => hC ▸ ⟨x, LowerSet.mem_top, rfl⟩
  inv := ConcreteCategory.ofHom
    ⟨fun y => (IsInclusion.injective (f := f)).invOfMemRange ⟨y.1, mem_range_of_mem f hC y⟩,
      IsMorphism.of_comp_of_injective
        (g := codRestrict f C fun x => hC ▸ ⟨x, LowerSet.mem_top, rfl⟩)
        (isMorphism _) IsInclusion.injective (by
          convert IsMorphism.id (Q.restrict C) using 1
          funext y
          exact Subtype.ext
            ((IsInclusion.injective (f := f)).left_inv_of_invOfMemRange ⟨y.1, _⟩))⟩
  hom_inv_id := by
    ext x
    exact (IsInclusion.injective (f := f)).right_inv_of_invOfMemRange x
  inv_hom_id := by
    ext y
    exact (IsInclusion.injective (f := f)).left_inv_of_invOfMemRange ⟨y.1, _⟩

@[simp] theorem isoRestrictOfFintype_hom_apply [Fintype P] [DecidableEq Q] {C : LowerSet Q}
    (hC : map f ⊤ = C) (x : P) : ((isoRestrictOfFintype f hC).hom x : Q) = f x :=
  rfl

def restrictCongr {S T : LowerSet Q} (h : S = T) : Q.restrict S ≅ Q.restrict T :=
  isoMk (OrderIso.setCongr (S : Set Q) T (congrArg SetLike.coe h)) fun _ => rfl

@[simp] theorem restrictCongr_hom_apply {S T : LowerSet Q} (h : S = T) (x : Q.restrict S) :
    ((restrictCongr h).hom x : Q) = x :=
  rfl

theorem comap_boundary {S : LowerSet Q} (hS : S ≤ map f ⊤) (n : ℕ) (α : Bool) :
    comap f (Q.boundary S n α) = P.boundary (comap f S) n α := by
  rw [← comap_map f (P.boundary (comap f S) n α), map_boundary, map_comap_of_le f hS]

theorem isPastingFactorOf_map_iff {X U : LowerSet P} :
    Q.IsPastingFactorOf (map f X) (map f U) ↔ P.IsPastingFactorOf X U := by
  refine ⟨fun ⟨k, α, Y, hp, hX, hY⟩ => ?_, fun ⟨k, α, Y, hp, hX, hY⟩ =>
    ⟨k, α, map f Y, by simpa only [Bool.apply_cond (map f)] using
      (isPastingIn_map_iff f k _ _ _).2 hp, (isMoleculeIn_map_iff f X).2 hX,
      (isMoleculeIn_map_iff f Y).2 hY⟩⟩
  obtain ⟨Y', -, rfl⟩ := exists_map_eq_of_le f (((isPastingIn_cond_iff α).1 hp).1 ▸ le_sup_left)
  exact ⟨k, α, Y', (isPastingIn_map_iff f k _ _ _).1 (by simpa only [Bool.apply_cond (map f)]),
    (isMoleculeIn_map_iff f X).1 hX, (isMoleculeIn_map_iff f Y').1 hY⟩

theorem isSubmoleculeOf_map_iff {X U : LowerSet P} :
    Q.IsSubmoleculeOf (map f X) (map f U) ↔ P.IsSubmoleculeOf X U := by
  refine and_congr (isMoleculeIn_map_iff f U) ⟨fun h => ?_, fun h => ?_⟩
  · have key : ∀ A, Relation.ReflTransGen Q.IsPastingFactorOf A (map f U) →
        ∃ B, map f B = A ∧ Relation.ReflTransGen P.IsPastingFactorOf B U := by
      intro A hA
      induction hA using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨U, rfl, .refl⟩
      | head hAA' _ ih =>
        obtain ⟨B', rfl, hB'⟩ := ih
        obtain ⟨B, -, rfl⟩ := exists_map_eq_of_le f hAA'.le
        exact ⟨B, rfl, .head ((isPastingFactorOf_map_iff f).1 hAA') hB'⟩
    obtain ⟨B, hB, hBU⟩ := key _ h
    rw [map_inj f] at hB
    exact hB ▸ hBU
  · induction h with
    | refl => exact .refl
    | tail _ hYU ih => exact ih.tail ((isPastingFactorOf_map_iff f).2 hYU)

theorem IsSubmoleculeOf.comap {X U : LowerSet Q} (h : Q.IsSubmoleculeOf X U)
    (hU : U ≤ map f ⊤) : P.IsSubmoleculeOf (comap f X) (comap f U) := by
  rw [← isSubmoleculeOf_map_iff f, map_comap_of_le f (h.le.trans hU), map_comap_of_le f hU]
  exact h

theorem isAtomIn_map_iff {U : LowerSet P} : Q.IsAtomIn (map f U) ↔ P.IsAtomIn U := by
  refine and_congr (isMoleculeIn_map_iff f U)
    ⟨fun ⟨t, ht⟩ => ?_, fun ⟨t, ht⟩ => ⟨f t, by rw [ht, map_Iic]⟩⟩
  obtain ⟨s, -, rfl⟩ : t ∈ map f U := ht ▸ LowerSet.mem_Iic_iff.2 le_rfl
  exact ⟨s, map_injective f (by rw [ht, map_Iic])⟩

omit [IsInclusion f] in
theorem isAtom_iff_of_iso (e : P ≅ Q) : P.IsAtom ↔ Q.IsAtom := by
  rw [IsAtom, IsAtom, ← isAtomIn_map_iff e.hom, map_top_of_isIso]

end Inclusion

namespace RDCpx

variable {U R : RDCpx.{u}}

theorem exists_iso_restrict (i : U.obj.toOGP ⟶ R.obj.toOGP) [IsInclusion i] :
    ∃ e : U ≅ restrict R (map i ⊤), e.hom ≫ restrictIncl R (map i ⊤) = ofInclusion i := by
  obtain ⟨e, he⟩ := OGP.exists_iso_restrict i rfl
  exact ⟨isoOfIso e, by ext x; exact ConcreteCategory.congr_hom he x⟩

end RDCpx

end Atoms.Molecule.OGP
