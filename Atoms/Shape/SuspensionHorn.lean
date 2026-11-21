import Atoms.Shape.Horn
import Atoms.Shape.Suspension

open CategoryTheory Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

private theorem isRewritableSubmolecule_atomSuspension_obj (h : HornData) :
    (atomSuspension.obj h.atom).ogp.IsRewritableSubmolecule
      (map (FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom h.removed.susp)
      ((atomSuspension.obj h.atom).ogp.bdry ⊤ h.side) := by
  have hb := bdry_susp (P := h.atom.ogp) (V := ⊤) (α := h.side)
    h.rewritable.isSubmoleculeOf.isMoleculeIn_right.nonempty
  have h1 := (isRewritableSubmolecule_map_iff (FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom
    _ _).2 h.rewritable.susp
  rwa [← hb, susp_top, map_bdry, map_top_of_isIso] at h1

def HornData.suspension (h : HornData) : HornData where
  atom := atomSuspension.obj h.atom
  positive := by rw [dimension_atomSuspension]; exact Nat.succ_pos _
  side := h.side
  removed := map (FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom h.removed.susp
  rewritable := isRewritableSubmolecule_atomSuspension_obj h

@[simp] theorem HornData.suspension_atom (h : HornData) :
    h.suspension.atom = atomSuspension.obj h.atom :=
  rfl

theorem hornSubset_suspension (h : HornData) (z : OGP.suspension h.atom.ogp) :
    (FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom z ∈ hornSubset h.suspension ↔
      z ∈ (hornSubset h).susp := by
  let e : OGP.suspension h.atom.ogp ≅ (atomSuspension.obj h.atom).ogp :=
    FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)
  have hV := h.rewritable.isSubmoleculeOf.isMoleculeIn
  have hb : (OGP.suspension h.atom.ogp).bdryFull ⊤ = (h.atom.ogp.bdryFull ⊤).susp := by
    rw [← bdryFull_susp h.atom.isMolecule, susp_top]
  have hi : e.hom z ∈ (atomSuspension.obj h.atom).ogp.interior (map e.hom h.removed.susp) ↔
      z ∈ (OGP.suspension h.atom.ogp).interior h.removed.susp := by
    rw [← image_interior]
    exact (IsInclusion.injective (f := e.hom)).mem_set_image
  have ht : e.hom z ≠ (atomSuspension.obj h.atom).top ↔
      z ∈ (h.atom.ogp.bdryFull ⊤).susp := by
    rw [← (atomSuspension.obj h.atom).mem_bdryFull_top_iff, ← hb, ← map_top_of_isIso e.hom,
      ← map_bdryFull, mem_map]
    exact ⟨fun ⟨x, hx, hxz⟩ => IsInclusion.injective (f := e.hom) hxz ▸ hx,
      fun hz => ⟨z, hz, rfl⟩⟩
  refine ((mem_hornSubset_iff h.suspension (e.hom z)).trans (and_congr ht (not_congr hi))).trans ?_
  cases z with
  | pole β =>
    exact iff_of_true ⟨pole_mem_susp _ β, pole_notMem_interior_susp hV β⟩ (pole_mem_susp _ β)
  | susp x =>
    rw [susp_mem_susp, susp_mem_susp, susp_mem_interior_susp hV, mem_hornSubset_iff,
      h.atom.mem_bdryFull_top_iff]

theorem boundary_Iic_atomSuspension_zero (U : Atom) (z : U.ogp) (α : Bool) :
    (atomSuspension.obj U).ogp.boundary
        (LowerSet.Iic ((FiniteOGP.ofOGPIso (OGP.suspension U.ogp)).hom (SuspCarrier.susp z))) 0 α =
      (atomSuspension.obj U).ogp.boundary ⊤ 0 α := by
  let e : OGP.suspension U.ogp ≅ (atomSuspension.obj U).ogp := FiniteOGP.ofOGPIso _
  have h1 : (atomSuspension.obj U).ogp.boundary (LowerSet.Iic (e.hom (SuspCarrier.susp z))) 0 α =
      map e.hom ((OGP.suspension U.ogp).boundary (LowerSet.Iic z).susp 0 α) := by
    rw [map_boundary, susp_Iic, map_Iic]
  have h2 : (atomSuspension.obj U).ogp.boundary ⊤ 0 α =
      map e.hom ((OGP.suspension U.ogp).boundary (⊤ : LowerSet U.ogp).susp 0 α) := by
    rw [map_boundary, susp_top, map_top_of_isIso]
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [boundary_susp_zero ⟨z, LowerSet.mem_Iic_iff.2 le_rfl⟩,
    boundary_susp_zero (V := (⊤ : LowerSet U.ogp)) ⟨z, LowerSet.mem_top⟩]

theorem HornData.IsAtomic.suspension {h : HornData} {x : h.atom.ogp}
    (hx : h.removed = LowerSet.Iic x) :
    h.suspension.removed =
      LowerSet.Iic ((FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom (SuspCarrier.susp x)) := by
  have h1 : h.suspension.removed =
      map (FiniteOGP.ofOGPIso (OGP.suspension h.atom.ogp)).hom h.removed.susp :=
    rfl
  rw [h1, hx, susp_Iic, map_Iic]

def AtomicHornData.suspension (h : AtomicHornData) : AtomicHornData where
  toHornData := h.toHornData.suspension
  isAtomic := by
    obtain ⟨x, hx⟩ := h.isAtomic
    exact ⟨_, HornData.IsAtomic.suspension hx⟩

end Atoms.Shape
