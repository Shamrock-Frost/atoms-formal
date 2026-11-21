import Atoms.Molecule.Construction.DualMap
import Atoms.Diagrammatic.Pasting.Paste

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X Y : DiagSet.{u}}

@[implicit_reducible, simps]
def cylDiagram (m : PastingDiagram X) (K : LowerSet m.shape.ogp) [DecidablePred (· ∈ K)] :
    PastingDiagram X :=
  ⟨cylShape m.shape K, realize.map (cylProj m.shape K) ≫ m.map⟩

theorem cylDiagram_congr (m : PastingDiagram X) {K K' : LowerSet m.shape.ogp} (h : K = K')
    [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')] :
    cylDiagram m K = cylDiagram m K' := by
  subst h
  congr

section Round

variable (c : PastingDiagram X) (K : LowerSet c.shape.ogp) [DecidablePred (· ∈ K)]
  (hc : c.IsRound) (hKU : K ≤ c.shape.ogp.bdryFull ⊤)

include hKU in
theorem dim_cylDiagram : (cylDiagram c K).dim = c.dim + 1 := by
  obtain ⟨x, hx, hxd⟩ := exists_notMem_bdryFull_grade_eq c.shape.isMolecule
    c.shape.krullDim_eq_dimension
  exact dimension_cylShape _ _ ⟨x, fun h => hx (hKU h), hxd⟩

include hc hKU in
theorem isRound_cylDiagram : (cylDiagram c K).IsRound :=
  isRound_cylShape _ _ hc hKU

include hKU in
theorem isDegenerate_cylDiagram : (cylDiagram c K).IsDegenerate := by
  refine ⟨⟨c.shape.rdc, cylProj _ _, c.map, surjective_cylProj _ _, ?_, rfl⟩⟩
  rw [show krullDim c.shape.rdc.obj.toOGP = c.dim from c.shape.krullDim_eq_dimension,
    dim_cylDiagram c K hKU]
  exact_mod_cast Nat.lt_succ_self c.dim

end Round

@[implicit_reducible] def unit (u : PastingDiagram X) : PastingDiagram X :=
  cylDiagram u (u.shape.ogp.bdryFull ⊤)

theorem unit_eq_cylDiagram (m : PastingDiagram X) :
    m.unit = cylDiagram m (m.shape.ogp.bdryFull ⊤) := rfl

theorem dim_unit (u : PastingDiagram X) : u.unit.dim = u.dim + 1 :=
  dim_cylDiagram u (u.shape.ogp.bdryFull ⊤) le_rfl

theorem isDegenerate_unit (u : PastingDiagram X) : u.unit.IsDegenerate :=
  isDegenerate_cylDiagram u _ le_rfl

theorem isRound_unit {u : PastingDiagram X} (hu : u.IsRound) : u.unit.IsRound :=
  isRound_cylDiagram u _ hu le_rfl

abbrev IsRound.unit {u : PastingDiagram X} (hu : u.IsRound) : RoundPastingDiagram X :=
  ⟨u.unit, isRound_unit hu⟩

theorem boundary_unit {u : PastingDiagram X} {k : ℕ} (hk : u.dim = k)
    (α : Bool) : (u.unit.boundary k α).Equiv u := by
  subst hk
  refine equiv_of_emb_of_image_eq (a := u.unit.boundary u.dim α) (b := u)
    (C := u.unit.shape.rdc) u.unit.map ((unitShape u.shape).boundaryIncl u.dim α)
    (cylEndpoint u.shape (u.shape.ogp.bdryFull ⊤) α) rfl ?_ ?_
  · change realize.map (RDCpx.ofInclusion (P := u.shape.rdc) (Q := (unitShape u.shape).rdc)
      (cylEndpoint u.shape (u.shape.ogp.bdryFull ⊤) α)) ≫
        realize.map (cylProj u.shape (u.shape.ogp.bdryFull ⊤)) ≫ u.map = u.map
    rw [← Category.assoc, ← realize.map_comp, ofInclusion_cylEndpoint_comp_cylProj,
      realize.map_id, Category.id_comp]
  · exact ((unitShape u.shape).map_boundaryIncl_top u.dim α).trans
      (map_cylEndpoint_bdryFull_top u.shape α).symm

theorem unit_mapTo (u : PastingDiagram X) (f : X ⟶ Y) : (u.mapTo f).unit = u.unit.mapTo f :=
  congrArg (PastingDiagram.mk (unitShape u.shape)) (Category.assoc _ _ _).symm

theorem equiv_unit_mapTo (u : PastingDiagram X) (φ : X ⟶ Y) :
    (u.unit.mapTo φ).Equiv (u.mapTo φ).unit := by
  rw [unit_mapTo]

theorem Equiv.unit {u v : PastingDiagram X} (h : u.Equiv v) : u.unit.Equiv v.unit := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨unitShapeIsoOfIso ψ, ?_⟩
  change realize.map (RDCpx.isoOfIso (P := (unitShape u.shape).rdc) (Q := (unitShape v.shape).rdc)
      (unitShapeIsoOfIso ψ)).hom ≫ realize.map (cylProj v.shape (v.shape.ogp.bdryFull ⊤)) ≫
        v.map =
    realize.map (cylProj u.shape (u.shape.ogp.bdryFull ⊤)) ≫ u.map
  rw [← hψ, ← Category.assoc, ← realize.map_comp, isoOfIso_unitShapeIsoOfIso_comp_cylProj,
    realize.map_comp, Category.assoc]

end Atoms.Diagrammatic.PastingDiagram
