import Atoms.ForMathlib.Order.UpperLower.Fibration
import Atoms.Molecule.Category

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} (f : P ⟶ Q) {U V : LowerSet P}

theorem map_sup (U V : LowerSet P) : map f (U ⊔ V) = map f U ⊔ map f V :=
  SetLike.coe_injective (Set.image_union _ _ _)

theorem map_iSup {ι : Sort*} (U : ι → LowerSet P) : map f (⨆ i, U i) = ⨆ i, map f (U i) :=
  SetLike.coe_injective (by simp only [coe_map, LowerSet.coe_iSup, image_iUnion])

@[simp] theorem map_bot : map f ⊥ = ⊥ :=
  SetLike.coe_injective (Set.image_empty _)

variable [IsInclusion f]

@[simp 1100] theorem apply_mem_map_iff {x : P} : f x ∈ map f U ↔ x ∈ U :=
  (IsInclusion.injective (f := f)).mem_set_image

theorem map_injective : Function.Injective (map f) := fun _ _ h =>
  SetLike.coe_injective (Set.image_injective.2 IsInclusion.injective (congrArg SetLike.coe h))

@[simp] theorem map_inj : map f U = map f V ↔ U = V :=
  (map_injective f).eq_iff

theorem map_inf (U V : LowerSet P) : map f (U ⊓ V) = map f U ⊓ map f V :=
  SetLike.coe_injective (Set.image_inter IsInclusion.injective)

@[simp] theorem map_eq_bot_iff : map f U = ⊥ ↔ U = ⊥ := by
  rw [← map_bot f, map_inj]

@[simp] theorem comap_map (U : LowerSet P) : comap f (map f U) = U :=
  SetLike.coe_injective (IsInclusion.injective.preimage_image _)

theorem exists_map_eq_of_le {W : LowerSet Q} (h : W ≤ map f U) : ∃ V ≤ U, map f V = W :=
  ⟨comap f W, fun _ hx => (apply_mem_map_iff f).1 (h hx),
    map_comap_of_le f (h.trans (map_mono f le_top))⟩

@[simp] theorem krullDim_map (U : LowerSet P) : krullDim (map f U) = krullDim U :=
  (krullDim_eq_of_orderIso
    { toEquiv := Equiv.Set.image f U IsInclusion.injective,
      map_rel_iff' := IsInclusion.le_iff f }).symm

theorem image_facesIn (U : Set P) (n : ℕ) (α : Bool) :
    f '' P.facesIn U n α = Q.facesIn (f '' U) n α := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxU, hxn, hd⟩, rfl⟩
    refine ⟨mem_image_of_mem f hxU, by rw [(isMorphism f).grade_eq, hxn], disjoint_left.2 ?_⟩
    rintro c hc ⟨z, hz, rfl⟩
    exact disjoint_left.1 hd ((IsInclusion.mem_faces_iff f).1 hc) hz
  · rintro ⟨⟨x, hxU, rfl⟩, hxn, hd⟩
    refine ⟨x, ⟨hxU, by rw [← (isMorphism f).grade_eq, hxn], disjoint_left.2 fun z hz hzU => ?_⟩,
      rfl⟩
    exact disjoint_left.1 hd ((IsInclusion.mem_faces_iff f).2 hz) (mem_image_of_mem f hzU)

theorem maximal_apply_mem_map_iff {x : P} : Maximal (· ∈ map f U) (f x) ↔ Maximal (· ∈ U) x :=
  ⟨fun h => ⟨(apply_mem_map_iff f).1 h.prop, fun y hy hxy =>
    (IsInclusion.le_iff f).1 (h.2 ((apply_mem_map_iff f).2 hy) ((isMorphism f).monotone hxy))⟩,
  fun h => ⟨(apply_mem_map_iff f).2 h.prop, by
    rintro _ ⟨y, hy, rfl⟩ hxy
    exact (isMorphism f).monotone (h.2 hy ((IsInclusion.le_iff f).1 hxy))⟩⟩

theorem image_setOf_maximal_grade (U : LowerSet P) (p : ℕ → Prop) :
    f '' {x | Maximal (· ∈ U) x ∧ p (grade ℕ x)} =
      {y | Maximal (· ∈ map f U) y ∧ p (grade ℕ y)} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨(maximal_apply_mem_map_iff f).2 hx, by rwa [(isMorphism f).grade_eq]⟩
  · rintro ⟨hy, hp⟩
    obtain ⟨x, -, rfl⟩ := hy.prop
    exact ⟨x, ⟨(maximal_apply_mem_map_iff f).1 hy, by rwa [← (isMorphism f).grade_eq]⟩, rfl⟩

theorem map_boundary (U : LowerSet P) (n : ℕ) (α : Bool) :
    map f (P.boundary U n α) = Q.boundary (map f U) n α :=
  SetLike.coe_injective (by
    rw [coe_map, boundary, boundary,
      (isMorphism f).fibration.image_lowerClosure (isMorphism f).monotone, image_union,
      image_facesIn, image_setOf_maximal_grade f U (· < n)]
    rfl)

theorem map_boundaryFull (U : LowerSet P) (n : ℕ) :
    map f (P.boundaryFull U n) = Q.boundaryFull (map f U) n := by
  rw [boundaryFull, boundaryFull, map_sup, map_boundary, map_boundary]

theorem map_bdry (U : LowerSet P) (α : Bool) : map f (P.bdry U α) = Q.bdry (map f U) α := by
  rw [bdry, bdry, krullDim_map]
  simp only [map_iSup, map_boundary]

theorem map_bdryFull (U : LowerSet P) : map f (P.bdryFull U) = Q.bdryFull (map f U) := by
  rw [bdryFull, bdryFull, map_sup, map_bdry, map_bdry]

end Atoms.Molecule.OGP
