import Atoms.Molecule.MoleculeShape.Basic
import Atoms.Molecule.Construction.DualMap

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

namespace MoleculeShape

variable (P : MoleculeShape) (J : ℕ → Bool)

def dual : MoleculeShape :=
  ofOGP (OGP.dual P.ogp J) ((isMoleculeIn_dual J).2 P.isMolecule)

def dualIso : OGP.dual P.ogp J ≅ (P.dual J).ogp :=
  FiniteOGP.ofOGPIso _

def dualDualIso : ((P.dual J).dual J).ogp ≅ P.ogp :=
  ((P.dual J).dualIso J).symm ≪≫ (OGP.dualFunctor J).mapIso (P.dualIso J).symm ≪≫
    OGP.dualDualIso J P.ogp

@[simp] theorem dualDualIso_hom_apply (x : ((P.dual J).dual J).ogp) :
    (P.dualDualIso J).hom x = (P.dualIso J).inv (((P.dual J).dualIso J).inv x) :=
  rfl

theorem dimension_dual : (P.dual J).dimension = P.dimension := by
  have h := (dimension_ofOGP (OGP.dual P.ogp J) ((isMoleculeIn_dual J).2 P.isMolecule)).trans
    P.krullDim_eq_dimension
  exact_mod_cast h

theorem isRound_dual {P : MoleculeShape} (hP : P.IsRound) (J : ℕ → Bool) : (P.dual J).IsRound :=
  isRound_ofOGP _ _ ((OGP.isRound_dual J).2 hP)

variable {P J} {Q : RDCpx.{0}}

def dualLift (p : P.rdc ⟶ Q) (hQ : ∀ x : Q.obj.toOGP, J (grade ℕ x) = false) :
    (P.dual J).rdc ⟶ Q :=
  (RDCpx.isoOfIso (P := (P.dual J).rdc) (Q := (RDCpx.dualFunctor J).obj P.rdc)
      (P.dualIso J).symm).hom ≫
    (RDCpx.dualFunctor J).map p ≫
    (RDCpx.isoOfIso (P := (RDCpx.dualFunctor J).obj Q) (Q := Q)
      (dualIsoOfForall J Q.obj.toOGP hQ)).hom

@[simp] theorem dualLift_apply (p : P.rdc ⟶ Q) (hQ : ∀ x : Q.obj.toOGP, J (grade ℕ x) = false)
    (x : (P.dual J).rdc.obj) :
    ConcreteCategory.hom (dualLift p hQ).hom x = ConcreteCategory.hom p.hom ((P.dualIso J).inv x) :=
  rfl

theorem surjective_dualLift (p : P.rdc ⟶ Q) (hQ : ∀ x : Q.obj.toOGP, J (grade ℕ x) = false)
    (hp : Function.Surjective (ConcreteCategory.hom p.hom)) :
    Function.Surjective (ConcreteCategory.hom (dualLift p hQ).hom) := fun y => by
  obtain ⟨x, rfl⟩ := hp y
  exact ⟨(P.dualIso J).hom x,
    (dualLift_apply p hQ _).trans (congrArg _ (Iso.hom_inv_id_apply (P.dualIso J) x))⟩

variable (P) {k : ℕ}

theorem apply_grade_boundary_dual_eq_false (hJ : ∀ m ≤ k, J m = false) (α : Bool)
    (y : ((P.dual J).boundary k α).ogp) : J (grade ℕ y) = false := by
  have hb := (P.dual J).isMolecule.boundary k α
  have hy : (P.dual J).subIncl hb y ∈ map ((P.dual J).subIncl hb) ⊤ :=
    mem_map.2 ⟨y, LowerSet.mem_top, rfl⟩
  rw [map_subIncl_top] at hy
  exact hJ _ (((isMorphism ((P.dual J).subIncl hb)).grade_eq y).symm.le.trans
    (grade_le_of_mem_boundary hy))

def boundaryDualIncl (hJ : ∀ m ≤ k, J m = false) (α : Bool) :
    ((P.dual J).boundary k α).ogp ⟶ P.ogp :=
  homOfDual ((P.dual J).subIncl _ ≫ (P.dualIso J).inv)
    (P.apply_grade_boundary_dual_eq_false hJ α)

@[simp] theorem boundaryDualIncl_apply (hJ : ∀ m ≤ k, J m = false) (α : Bool)
    (y : ((P.dual J).boundary k α).ogp) :
    P.boundaryDualIncl hJ α y = (P.dualIso J).inv ((P.dual J).subIncl _ y) :=
  rfl

instance (hJ : ∀ m ≤ k, J m = false) (α : Bool) : IsInclusion (P.boundaryDualIncl hJ α) :=
  ⟨IsInclusion.injective
    (f := (P.dual J).subIncl ((P.dual J).isMolecule.boundary k α) ≫ (P.dualIso J).inv)⟩

theorem map_boundaryDualIncl_top (hJ : ∀ m ≤ k, J m = false) (α : Bool) :
    map (P.boundaryDualIncl hJ α) ⊤ = P.ogp.boundary ⊤ k (xor (J (k + 1)) α) := by
  have hb := (P.dual J).isMolecule.boundary k α
  have h : map ((P.dual J).subIncl hb ≫ (P.dualIso J).inv) ⊤ =
      (OGP.dual P.ogp J).boundary ⊤ k α := by
    rw [map_comp, map_subIncl_top, map_boundary, map_top_of_isIso]
  rw [← boundary_dual, ← h]
  refine SetLike.coe_injective ?_
  rw [coe_map, coe_map]
  exact Set.image_congr fun y _ => P.boundaryDualIncl_apply hJ α y

end MoleculeShape

end Atoms.Molecule
