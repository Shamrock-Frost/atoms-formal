import Atoms.Molecule.Gluing.Substitution
import Atoms.Molecule.Gluing.BoundaryIso

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

section SubstAlong

variable {U S W : OGP.{u}} (e : S ⟶ U) [IsInclusion e]

theorem map_incl_bdryFull_comp :
    map (incl (S.bdryFull ⊤) ≫ e) ⊤ = U.bdryFull (map e ⊤) := by
  rw [map_comp, map_incl_top, map_bdryFull]

variable (hV : U.IsRewritableSubmolecule (map e ⊤) ⊤)

@[implicit_reducible] def substCorner : S.restrict (S.bdryFull ⊤) ⟶ U.restrict hV.complement :=
  codRestrict (incl (S.bdryFull ⊤) ≫ e) hV.complement fun x =>
    (hV.isSubmoleculeOf.mem_complement hV.krullDim_eq).2 ⟨LowerSet.mem_top, fun hi =>
      hi.2 (bdryFull_le_properBoundary _ (map_incl_bdryFull_comp e ▸ ⟨x, LowerSet.mem_top, rfl⟩))⟩

instance : IsInclusion (substCorner e hV) :=
  inferInstanceAs (IsInclusion (codRestrict _ _ _))

@[reassoc (attr := simp)]
theorem substCorner_incl : substCorner e hV ≫ incl hV.complement = incl (S.bdryFull ⊤) ≫ e :=
  codRestrict_incl _ _ _

theorem map_substCorner :
    map (substCorner e hV) ⊤ = comap (incl hV.complement) (U.bdryFull (map e ⊤)) := by
  rw [← comap_map (incl hV.complement) (map (substCorner e hV) ⊤), ← map_comp, substCorner_incl,
    map_incl_bdryFull_comp]

variable [Fintype (S.restrict (S.bdryFull ⊤))] [DecidableEq U]

def bdryIsoAlong (φS : S.restrict (S.bdryFull ⊤) ≅ W.restrict (W.bdryFull ⊤)) :
    U.restrict (U.bdryFull (map e ⊤)) ≅ W.restrict (W.bdryFull ⊤) :=
  (isoRestrictOfFintype (incl (S.bdryFull ⊤) ≫ e) (map_incl_bdryFull_comp e)).symm ≪≫ φS

theorem bdryIsoAlong_apply (φS : S.restrict (S.bdryFull ⊤) ≅ W.restrict (W.bdryFull ⊤))
    (x : S.restrict (S.bdryFull ⊤)) (h : e x.1 ∈ U.bdryFull (map e ⊤)) :
    (bdryIsoAlong e φS).hom ⟨e x.1, h⟩ = φS.hom x :=
  congrArg φS.hom
    ((isoRestrictOfFintype (incl (S.bdryFull ⊤) ≫ e) (map_incl_bdryFull_comp e)).hom_inv_id_apply x)

theorem isSigned_bdryIsoAlong {φS : S.restrict (S.bdryFull ⊤) ≅ W.restrict (W.bdryFull ⊤)}
    (hφ : φS.IsSigned) : (bdryIsoAlong e φS).IsSigned := by
  intro α y
  let x := (isoRestrictOfFintype (incl (S.bdryFull ⊤) ≫ e) (map_incl_bdryFull_comp e)).inv y
  have hy : e x.1 = y.1 := congrArg Subtype.val
    ((isoRestrictOfFintype (incl (S.bdryFull ⊤) ≫ e) (map_incl_bdryFull_comp e)).inv_hom_id_apply y)
  change y.1 ∈ U.bdry (map e ⊤) α ↔ (φS.hom x).1 ∈ W.bdry ⊤ α
  rw [← hy, ← map_bdry, apply_mem_map_iff]
  exact hφ α x

theorem substInl_substCorner (φS : S.restrict (S.bdryFull ⊤) ≅ W.restrict (W.bdryFull ⊤))
    (x : S.restrict (S.bdryFull ⊤)) :
    substInl hV (bdryIsoAlong e φS) (substCorner e hV x) =
      substInr hV (bdryIsoAlong e φS) (φS.hom x).1 := by
  have h : e x.1 ∈ U.bdryFull (map e ⊤) :=
    map_incl_bdryFull_comp e ▸ ⟨x, LowerSet.mem_top, rfl⟩
  exact Subtype.ext (glue.inl_eq_inr_iff.2 ⟨h, congrArg Subtype.val (bdryIsoAlong_apply e φS x h)⟩)

theorem map_substCorner_comp_substInl
    (φS : S.restrict (S.bdryFull ⊤) ≅ W.restrict (W.bdryFull ⊤)) :
    map (substCorner e hV ≫ substInl hV (bdryIsoAlong e φS)) ⊤ =
      map (substInl hV (bdryIsoAlong e φS)) ⊤ ⊓ map (substInr hV (bdryIsoAlong e φS)) ⊤ := by
  let φ := bdryIsoAlong e φS
  refine map_injective (incl (substSupport hV φ)) ?_
  rw [map_inf, ← map_comp, ← map_comp, ← map_comp, Category.assoc, substInl_incl, substInr_incl,
    substCorner_incl_assoc, ← Category.assoc, map_comp, map_incl_bdryFull_comp, map_comp,
    map_incl_top]
  have hm := glue.map_inl_inf_map_inr φ
  rw [map_comp, map_incl_top] at hm
  exact le_antisymm (le_inf (map_mono _ fun _ hx =>
    (hV.isSubmoleculeOf.mem_complement hV.krullDim_eq).2 ⟨LowerSet.mem_top,
      fun hi => hi.2 (bdryFull_le_properBoundary _ hx)⟩) (hm.symm.trans_le inf_le_right))
    ((inf_le_inf_right _ (map_mono _ le_top)).trans hm.le)

end SubstAlong

end Atoms.Molecule.OGP
