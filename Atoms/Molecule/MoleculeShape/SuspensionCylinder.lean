import Atoms.Molecule.MoleculeShape.PartialCylinder
import Atoms.Molecule.MoleculeShape.Suspension

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

namespace PartialCylinder

open SuspCarrier PartialCylinderCarrier

variable {U : OGP.{u}} {K : LowerSet U}

def suspToCylinder :
    SuspCarrier (PartialCylinderCarrier U K) → PartialCylinderCarrier (suspension U) K.susp
  | pole α => Sum.inl ⟨pole α, pole_mem_susp K α⟩
  | susp (Sum.inl x) => Sum.inl ⟨susp x.1, susp_mem_susp.2 x.2⟩
  | susp (Sum.inr q) => Sum.inr (q.1, ⟨susp q.2.1, fun h => q.2.2 (susp_mem_susp.1 h)⟩)

def cylinderToSusp :
    PartialCylinderCarrier (suspension U) K.susp → SuspCarrier (PartialCylinderCarrier U K)
  | Sum.inl ⟨pole α, _⟩ => pole α
  | Sum.inl ⟨susp x, h⟩ => susp (Sum.inl ⟨x, susp_mem_susp.1 h⟩)
  | Sum.inr (_, ⟨pole α, h⟩) => (h (pole_mem_susp K α)).elim
  | Sum.inr (i, ⟨susp x, h⟩) => susp (Sum.inr (i, ⟨x, fun hx => h (susp_mem_susp.2 hx)⟩))

variable (U K) in
def suspOrderIso : suspension (partialCylinder U K) ≃o partialCylinder (suspension U) K.susp where
  toFun := suspToCylinder
  invFun := cylinderToSusp
  left_inv := by rintro (α | x | q) <;> rfl
  right_inv := by
    rintro (⟨α | x, hx⟩ | ⟨i, ⟨α | x, hx⟩⟩)
    · rfl
    · rfl
    · exact (hx (pole_mem_susp K α)).elim
    · rfl
  map_rel_iff' {a b} := by
    rcases a with α | x | q <;> rcases b with β | y | r <;> exact Iff.rfl

variable (U K) in
def suspensionIso : suspension (partialCylinder U K) ≅ partialCylinder (suspension U) K.susp :=
  isoMk (suspOrderIso U K) fun {x y} h => by
    rcases x with α | a
    · exact (not_covBy_pole h).elim
    rcases y with β | b
    · rcases a with x | ⟨⟨_ | γ⟩, x⟩
      · rfl
      · have hm : IsMin (mkI K none x.1 x.2) := pole_covBy_susp.1 h
        obtain ⟨h' | h', -⟩ := @hm (mkI K (some false) x.1 x.2) ⟨Or.inr rfl, le_refl x.1⟩ <;>
          cases h'
      · rfl
    · rcases a with x | ⟨⟨_ | γ⟩, x⟩ <;> rcases b with y | ⟨⟨_ | δ⟩, y⟩ <;> rfl

theorem proj_suspensionIso_hom (a : suspension (partialCylinder U K)) :
    partialCylinderProj (suspension U) K.susp ((suspensionIso U K).hom a) =
      suspMap (partialCylinderProj U K) a := by
  rcases a with α | x | q <;> rfl

end PartialCylinder

end Atoms.Molecule.OGP

namespace Atoms.Molecule

open OGP

private theorem suspensionIso_mem_bdryFull_iff (P : MoleculeShape) (x : OGP.suspension P.ogp) :
    P.suspensionIso.hom x ∈ P.suspension.ogp.bdryFull ⊤ ↔ x ∈ (P.ogp.bdryFull ⊤).susp := by
  rw [← map_top_of_isIso P.suspensionIso.hom, ← map_bdryFull, apply_mem_map_iff, ← susp_top,
    bdryFull_susp P.isMolecule]

def suspensionUnitShapeIso (P : MoleculeShape) :
    (unitShape P).suspension.ogp ≅ (unitShape P.suspension).ogp :=
  (unitShape P).suspensionIso.symm ≪≫ OGP.suspension.mapIso (cylShapeIso P _).symm ≪≫
    PartialCylinder.suspensionIso P.ogp _ ≪≫
    PartialCylinder.isoOfIso _ _ P.suspensionIso (suspensionIso_mem_bdryFull_iff P) ≪≫
    cylShapeIso P.suspension _

theorem isoOfIso_suspensionUnitShapeIso_comp_cylProj (P : MoleculeShape) :
    (RDCpx.isoOfIso (P := (unitShape P).suspension.rdc) (Q := (unitShape P.suspension).rdc)
        (suspensionUnitShapeIso P)).hom ≫ cylProj P.suspension (P.suspension.ogp.bdryFull ⊤) =
      (unitShape P).suspensionRDCIso.inv ≫
        RDCpx.suspensionFunctor.map (cylProj P (P.ogp.bdryFull ⊤)) ≫ P.suspensionRDCIso.hom := by
  ext x
  refine (congrArg (partialCylinderProj P.suspension.ogp (P.suspension.ogp.bdryFull ⊤))
    (Iso.hom_inv_id_apply (cylShapeIso P.suspension _) _)).trans ?_
  refine (PartialCylinder.proj_carrierMapOfMap _ _ _ (suspensionIso_mem_bdryFull_iff P) _).trans ?_
  refine congrArg P.suspensionIso.hom
    ((PartialCylinder.proj_suspensionIso_hom _).trans ?_)
  change suspMap _ (suspMap _ ((unitShape P).suspensionIso.inv x)) =
    suspMap _ ((unitShape P).suspensionIso.inv x)
  generalize (unitShape P).suspensionIso.inv x = y
  rcases y with α | y <;> rfl

end Atoms.Molecule
