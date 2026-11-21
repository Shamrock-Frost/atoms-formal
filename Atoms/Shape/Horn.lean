import Atoms.Shape.GrayCylinder
import Atoms.Molecule.Rewritable.Block
import Atoms.Molecule.Vertex

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

theorem Atom.krullDim_top_of_pos (U : Atom) (hU : 0 < U.dimension) :
    krullDim (⊤ : LowerSet U.ogp) = (U.dimension - 1 : ℕ) + 1 :=
  U.toMoleculeShape.krullDim_top_eq (Nat.sub_add_cancel hU).symm

theorem Atom.krullDim_top_pos (U : Atom) (hU : 0 < U.dimension) :
    0 < krullDim (⊤ : LowerSet U.ogp) := by
  rw [LowerSet.krullDim_top, U.krullDim_eq_dimension]
  exact_mod_cast hU

theorem Atom.bdry_top_eq_boundary (U : Atom) (hU : 0 < U.dimension) (α : Bool) :
    U.ogp.bdry ⊤ α = U.ogp.boundary ⊤ (U.dimension - 1) α :=
  bdry_eq_boundary (U.krullDim_top_of_pos hU) α

theorem Atom.lt_top_of_mem_bdry (U : Atom) {y : U.ogp} {α : Bool}
    (hy : y ∈ U.ogp.bdry ⊤ α) : y < U.top :=
  lt_of_le_of_ne (U.le_top y) ((U.mem_bdryFull_top_iff y).1 (bdry_le_bdryFull ⊤ α hy))

theorem Atom.interior_Iic (U : Atom) (x : U.ogp) :
    U.ogp.interior (LowerSet.Iic x) = {x} :=
  (U.isRDC x).interior_Iic

structure HornData where
  atom : Atom
  positive : 0 < atom.dimension
  side : Bool
  removed : LowerSet atom.ogp
  rewritable : atom.ogp.IsRewritableSubmolecule removed (atom.ogp.bdry ⊤ side)

theorem HornData.isRewritableSubmolecule_boundary (h : HornData) :
    h.atom.ogp.IsRewritableSubmolecule h.removed
      (h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side) := by
  rw [← h.atom.bdry_top_eq_boundary h.positive]
  exact h.rewritable

theorem HornData.eq_of_removed_eq (h : HornData) (V : LowerSet h.atom.ogp)
    (hV : h.atom.ogp.IsRewritableSubmolecule V (h.atom.ogp.bdry ⊤ h.side))
    (e : h.removed = V) : (⟨h.atom, h.positive, h.side, V, hV⟩ : HornData) = h := by
  cases h
  cases e
  rfl

def hornSubset (h : HornData) : LowerSet h.atom.ogp :=
  h.rewritable.hornSet h.atom.isMolecule h.atom.isAtom.isRound

theorem mem_hornSubset_iff (h : HornData) (x : h.atom.ogp) :
    x ∈ hornSubset h ↔ x ≠ h.atom.top ∧ x ∉ h.atom.ogp.interior h.removed := by
  rw [hornSubset, IsRewritableSubmolecule.hornSet, IsSubmoleculeOf.mem_hornSet,
    h.atom.mem_bdryFull_top_iff]

private theorem HornData.bdry_inf_bdry_not_eq_properBoundary (h : HornData) :
    h.atom.ogp.bdry ⊤ h.side ⊓ h.atom.ogp.bdry ⊤ (!h.side) =
      h.atom.ogp.properBoundary (h.atom.ogp.bdry ⊤ h.side) := by
  have hn := h.atom.krullDim_top_of_pos h.positive
  rw [bdry_eq_boundary hn, bdry_eq_boundary hn]
  exact h.atom.isAtom.isRound.inf_boundary_eq_properBoundary h.atom.isMolecule
    (by rw [hn]; exact_mod_cast (h.atom.dimension - 1).lt_succ_self) h.side

theorem HornData.notMem_interior_removed_of_mem_bdry_not (h : HornData)
    {x : h.atom.ogp} (hx : x ∈ h.atom.ogp.bdry ⊤ (!h.side)) :
    x ∉ h.atom.ogp.interior h.removed := by
  intro hxV
  have hr := h.rewritable
  have hxB := hr.isSubmoleculeOf.interior_subset_interior hr.krullDim_eq hxV
  exact hxB.2 (h.bdry_inf_bdry_not_eq_properBoundary ▸ ⟨hxB.1, hx⟩)

theorem HornData.bdry_not_subset_hornSubset (h : HornData) :
    h.atom.ogp.bdry ⊤ (!h.side) ≤ hornSubset h :=
  h.rewritable.isSubmoleculeOf.bdry_not_le_hornSet h.atom.isMolecule h.atom.isAtom.isRound
    h.rewritable.krullDim_eq (h.atom.krullDim_top_of_pos h.positive)

theorem hornSubset_eq_complement_union (h : HornData) :
    hornSubset h = h.rewritable.complement ⊔ h.atom.ogp.bdry ⊤ (!h.side) := by
  refine SetLike.ext fun x => ?_
  rw [hornSubset, IsRewritableSubmolecule.hornSet, IsSubmoleculeOf.mem_hornSet,
    LowerSet.mem_sup_iff, IsSubmoleculeOf.mem_complement,
    bdryFull_eq_bdry_sup_bdry_not _ h.side, LowerSet.mem_sup_iff]
  have hd : x ∈ h.atom.ogp.bdry ⊤ (!h.side) → x ∉ h.atom.ogp.interior h.removed :=
    h.notMem_interior_removed_of_mem_bdry_not
  tauto

theorem HornData.sdiff_interior_inter_bdry_not_eq_bdryFull (h : HornData) :
    h.rewritable.complement ⊓ h.atom.ogp.bdry ⊤ (!h.side) =
      h.atom.ogp.bdryFull (h.atom.ogp.bdry ⊤ h.side) := by
  rw [← (h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive)
      h.side).properBoundary_eq_bdryFull, ← h.bdry_inf_bdry_not_eq_properBoundary]
  refine SetLike.ext fun x => ?_
  rw [LowerSet.mem_inf_iff, IsSubmoleculeOf.mem_complement, LowerSet.mem_inf_iff]
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
    fun hx => ⟨⟨hx.1, h.notMem_interior_removed_of_mem_bdry_not hx.2⟩, hx.2⟩⟩

def HornData.IsAtomic (h : HornData) : Prop :=
  ∃ x : h.atom.ogp, h.removed = LowerSet.Iic x

structure AtomicHornData extends HornData where
  isAtomic : toHornData.IsAtomic

@[ext] theorem AtomicHornData.ext {h₁ h₂ : AtomicHornData} (h : h₁.toHornData = h₂.toHornData) :
    h₁ = h₂ := by
  cases h₁; cases h₂; cases h; rfl

theorem mem_faceSet_top_of_isRewritableSubmolecule (h : HornData) {x : h.atom.ogp}
    (hx : h.removed = LowerSet.Iic x) : x ∈ h.atom.ogp.faces h.side h.atom.top := by
  have hxb : x ∈ h.atom.ogp.bdry (LowerSet.Iic h.atom.top) h.side := by
    rw [h.atom.Iic_top]
    exact h.rewritable.isSubmoleculeOf.le (hx.symm ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have hdx : grade ℕ x = h.atom.dimension - 1 := by
    have hd := h.isRewritableSubmolecule_boundary.krullDim_eq
    rw [hx, LowerSet.krullDim_Iic, h.atom.isMolecule.krullDim_boundary
      (by rw [LowerSet.krullDim_top, h.atom.krullDim_eq_dimension];
          exact_mod_cast Nat.sub_le _ 1)] at hd
    exact_mod_cast hd
  refine mem_faces_of_mem_bdry_Iic hxb ?_
  rw [hdx, ← h.atom.dimension_eq, Nat.sub_add_cancel h.positive]

theorem mem_hornSet_closure_singleton_iff (h : HornData) {x z : h.atom.ogp}
    (hx : h.removed = LowerSet.Iic x) :
    z ∈ hornSubset h ↔ z ≠ h.atom.top ∧ z ≠ x := by
  rw [mem_hornSubset_iff, hx, h.atom.interior_Iic, Set.mem_singleton_iff]

def atomicHornDataOfCovBy (U : Atom) (x : U.ogp) (hx : x ⋖ U.top) : AtomicHornData where
  atom := U
  positive := U.dimension_eq ▸ Nat.zero_lt_of_lt (hx.grade ℕ).lt
  side := U.ogp.orient hx
  removed := LowerSet.Iic x
  rewritable := by
    have hpos : 0 < U.dimension := U.dimension_eq ▸ Nat.zero_lt_of_lt (hx.grade ℕ).lt
    have hbm : IsMoleculeIn U.ogp (U.ogp.bdry ⊤ (U.ogp.orient hx)) :=
      U.isMolecule.bdry (U.krullDim_top_pos hpos) _
    have hbr : U.ogp.IsRound (U.ogp.bdry ⊤ (U.ogp.orient hx)) := by
      rw [U.bdry_top_eq_boundary hpos]
      exact U.isAtom.isRound.boundary _ _
    have hmax : Maximal (· ∈ U.ogp.bdry ⊤ (U.ogp.orient hx)) x :=
      ⟨U.Iic_top ▸ mem_bdry_Iic_of_covBy hx, fun _ hy hxy =>
        (eq_of_le_of_not_lt hxy fun hlt => hx.2 hlt (U.lt_top_of_mem_bdry hy)).symm.le⟩
    exact isRewritableSubmolecule_Iic_of_maximal hbm hbr hmax
  isAtomic := ⟨x, rfl⟩

theorem exists_atomicHornData (U : Atom) (hU : 0 < U.dimension) :
    ∃ h : AtomicHornData, h.atom = U := by
  obtain ⟨y, hy⟩ := (U.isMolecule.bdry (U.krullDim_top_pos hU) false).nonempty
  obtain ⟨x, -, hx⟩ := exists_le_covBy_of_lt (U.lt_top_of_mem_bdry hy)
  exact ⟨atomicHornDataOfCovBy U x hx, rfl⟩

def principalHornData (U : Atom) (x : U.ogp) (hx : 0 < grade ℕ x) (α : Bool) :
    HornData where
  atom := Atom.ofClosure U x
  positive := dimension_ofClosure_pos U x hx
  side := !α
  removed := (Atom.ofClosure U x).ogp.bdry ⊤ (!α)
  rewritable := isRewritableSubmolecule_bdry_self (Atom.ofClosure U x).isMolecule
    (Atom.ofClosure U x).isAtom.isRound
    ((Atom.ofClosure U x).krullDim_top_of_pos (dimension_ofClosure_pos U x hx)) (!α)

theorem hornSubset_principalHornData (U : Atom) (x : U.ogp) (hx : 0 < grade ℕ x)
    (α : Bool) :
    hornSubset (principalHornData U x hx α) =
      (Atom.ofClosure U x).ogp.bdry ⊤ α :=
  IsSubmoleculeOf.hornSet_bdry (Atom.ofClosure U x).isMolecule
    (Atom.ofClosure U x).isAtom.isRound
    ((Atom.ofClosure U x).krullDim_top_of_pos (dimension_ofClosure_pos U x hx))
    (principalHornData U x hx α).rewritable.isSubmoleculeOf
    (principalHornData U x hx α).rewritable.krullDim_eq

theorem image_hornSubset_principalHornData (U : Atom) (x : U.ogp)
    (hx : 0 < grade ℕ x) (α : Bool) :
    Atom.closureIncl U x ''
        SetLike.coe (A := LowerSet (Atom.ofClosure U x).ogp)
          (hornSubset (principalHornData U x hx α)) =
      U.ogp.boundary (.Iic x) (grade ℕ x - 1) α := by
  rw [hornSubset_principalHornData,
    (Atom.ofClosure U x).bdry_top_eq_boundary (dimension_ofClosure_pos U x hx),
    Atom.dimension_ofClosure, image_boundary_closureIncl]

private theorem hornSet_grayCylinder_obj (U : Atom) {α : Bool}
    {W : LowerSet (grayProduct (globe.{0} 1) U.ogp)}
    (hW : (grayProduct (globe.{0} 1) U.ogp).IsRewritableSubmolecule W
      ((grayProduct (globe.{0} 1) U.ogp).bdry ⊤ α)) :
    (isRewritableSubmolecule_grayCylinder_obj U hW).hornSet
        (grayCylinder.obj U).isMolecule (grayCylinder.obj U).isAtom.isRound =
      map (cylAtomIso U).hom
        (hW.hornSet (isMolecule_grayProduct (isAtom_globe 1).isMoleculeIn U.isMolecule)
          (isAtom_grayProduct (isAtom_globe 1) U.isAtom).isRound) :=
  SetLike.coe_injective (by
    rw [IsSubmoleculeOf.coe_hornSet, coe_map, IsSubmoleculeOf.coe_hornSet,
      image_sdiff IsInclusion.injective, image_interior, ← coe_map, map_bdryFull,
      map_top_of_isIso]
    rfl)

private theorem isRewritableSubmolecule_cylinder (h : HornData) :
    (grayProduct (globe.{0} 1) h.atom.ogp).IsRewritableSubmolecule
      ((⊤ : LowerSet (globe.{0} 1)) ×ˢ h.removed)
      ((grayProduct (globe.{0} 1) h.atom.ogp).bdry ⊤ (!h.side)) := by
  have hW := isRewritableSubmolecule_prod_right (isAtom_globe 1)
    (krullDim_globe 1) h.atom.isAtom h.rewritable
  rwa [Nat.bodd_one, Bool.true_xor] at hW

def endpointHornData (ε : Bool) (U : Atom) : HornData where
  atom := grayCylinder.obj U
  positive := by rw [dimension_grayCylinder_obj]; exact Nat.succ_pos _
  side := !ε
  removed := map (cylAtomIso U).hom
    (LowerSet.Iic (SuspCarrier.pole (!ε) : globe.{0} 1) ×ˢ (⊤ : LowerSet U.ogp))
  rewritable := isRewritableSubmolecule_grayCylinder_obj U
    (isRewritableSubmolecule_prod_left (isAtom_globe 1) U.isAtom
      (isRewritableSubmolecule_globe_one (!ε)))

def cylinderHornData (h : HornData) : HornData where
  atom := grayCylinder.obj h.atom
  positive := by rw [dimension_grayCylinder_obj]; exact Nat.succ_pos _
  side := !h.side
  removed := map (cylAtomIso h.atom).hom ((⊤ : LowerSet (globe.{0} 1)) ×ˢ h.removed)
  rewritable := isRewritableSubmolecule_grayCylinder_obj h.atom (isRewritableSubmolecule_cylinder h)

theorem hornSubset_endpointHornData (ε : Bool) (U : Atom) :
    hornSubset (endpointHornData ε U) =
      cylinderSubset U (U.ogp.bdryFull ⊤) ⊔ endpointSubset ε U := by
  refine (hornSet_grayCylinder_obj U
    (isRewritableSubmolecule_prod_left (isAtom_globe 1) U.isAtom
      (isRewritableSubmolecule_globe_one (!ε)))).trans ?_
  rw [hornSet_prod_left (isAtom_globe 1) U.isAtom (isRewritableSubmolecule_globe_one (!ε)),
    hornSet_globe_one, Bool.not_not, sup_comm, OGP.map_sup, ← endpointSubset_eq_map]
  rfl

theorem hornSubset_cylinderHornData (h : HornData) :
    hornSubset (cylinderHornData h) =
      cylinderSubset h.atom (hornSubset h) ⊔
        (endpointSubset false h.atom ⊔ endpointSubset true h.atom) := by
  have heq : (isRewritableSubmolecule_cylinder h).hornSet
      (isMolecule_grayProduct (isAtom_globe 1).isMoleculeIn h.atom.isMolecule)
      (isAtom_grayProduct (isAtom_globe 1) h.atom.isAtom).isRound =
    (isRewritableSubmolecule_prod_right (isAtom_globe 1) (krullDim_globe 1)
      h.atom.isAtom h.rewritable).hornSet
      (isMolecule_grayProduct (isAtom_globe 1).isMoleculeIn h.atom.isMolecule)
      (isAtom_grayProduct (isAtom_globe 1) h.atom.isAtom).isRound :=
    SetLike.coe_injective (by rw [IsSubmoleculeOf.coe_hornSet, IsSubmoleculeOf.coe_hornSet])
  refine (hornSet_grayCylinder_obj h.atom (isRewritableSubmolecule_cylinder h)).trans ?_
  rw [heq, hornSet_prod_right (isAtom_globe 1) (krullDim_globe 1) h.atom.isAtom h.rewritable,
    bdryFull_globe_one, LowerSet.sup_prod, sup_comm, OGP.map_sup, OGP.map_sup,
    ← endpointSubset_eq_map false, ← endpointSubset_eq_map true]
  rfl

theorem Iic_cylAtomIso (U : Atom) (a : globe.{0} 1) (b : U.ogp) :
    LowerSet.Iic ((cylAtomIso U).hom (a, b)) =
      map (cylAtomIso U).hom (LowerSet.Iic a ×ˢ LowerSet.Iic b) := by
  rw [← map_Iic, Iic_grayProduct]

theorem endpointHornData_isAtomic (ε : Bool) (U : Atom) :
    (endpointHornData ε U).IsAtomic := by
  refine ⟨(cylAtomIso U).hom (SuspCarrier.pole (!ε), U.top), ?_⟩
  change map (cylAtomIso U).hom
    (LowerSet.Iic (SuspCarrier.pole (!ε) : globe.{0} 1) ×ˢ (⊤ : LowerSet U.ogp)) =
    LowerSet.Iic ((cylAtomIso U).hom (SuspCarrier.pole (!ε), U.top))
  rw [Iic_cylAtomIso, U.Iic_top]

theorem cylinderHornData_isAtomic (h : AtomicHornData) :
    (cylinderHornData h.toHornData).IsAtomic := by
  rcases h with ⟨h, x, hx⟩
  refine ⟨(cylAtomIso h.atom).hom (⊤, x), ?_⟩
  change map (cylAtomIso h.atom).hom ((⊤ : LowerSet (globe.{0} 1)) ×ˢ h.removed) =
    LowerSet.Iic ((cylAtomIso h.atom).hom (⊤, x))
  rw [Iic_cylAtomIso, LowerSet.Iic_top, hx]

end Atoms.Shape
