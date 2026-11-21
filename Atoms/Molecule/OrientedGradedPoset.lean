import Atoms.ForMathlib.Order.Grade
import Atoms.ForMathlib.Tactic.TransferInstances
import Atoms.ForMathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Data.FinEnum
import Mathlib.Order.Grade
import Mathlib.Order.KrullDimension
import Mathlib.Order.UpperLower.Closure

universe u v w

open Order Set

namespace Atoms.Molecule

structure OGP : Type (u + 1) where
  carrier : Type u
  [partialOrderCarrier : PartialOrder carrier]
  [gradeMinOrderCarrier : GradeMinOrder ℕ carrier]
  orient : ∀ {x y : carrier}, y ⋖ x → Bool

attribute [instance] OGP.partialOrderCarrier OGP.gradeMinOrderCarrier
attribute [coe] OGP.carrier

instance : CoeSort OGP.{u} (Type u) := ⟨OGP.carrier⟩

namespace OGP

variable (P : OGP.{u}) (Q : OGP.{v})

instance wellFoundedLT : WellFoundedLT P := GradeOrder.wellFoundedLT ℕ

scoped instance topologicalSpace : TopologicalSpace P := Topology.upperSet P

scoped instance isUpperSet : Topology.IsUpperSet P := ⟨rfl⟩

def faces (α : Bool) (x : P) : Set P := {y | ∃ h : y ⋖ x, P.orient h = α}

def cofaces (α : Bool) (x : P) : Set P := {y | ∃ h : x ⋖ y, P.orient h = α}

def facesIn (U : Set P) (n : ℕ) (α : Bool) : Set P :=
  {x ∈ U | grade ℕ x = n ∧ Disjoint (P.cofaces (!α) x) U}

def boundary (U : LowerSet P) (n : ℕ) (α : Bool) : LowerSet P :=
  lowerClosure (P.facesIn U n α ∪ {x | Maximal (· ∈ U) x ∧ grade ℕ x < n})

def boundaryFull (U : LowerSet P) (n : ℕ) : LowerSet P :=
  P.boundary U n false ⊔ P.boundary U n true

def bdry (U : LowerSet P) (α : Bool) : LowerSet P :=
  ⨆ (n : ℕ) (_ : krullDim U = n + 1), P.boundary U n α

def bdryFull (U : LowerSet P) : LowerSet P := P.bdry U false ⊔ P.bdry U true

variable {P}

@[simp] theorem mem_faces {α : Bool} {x y : P} :
    y ∈ P.faces α x ↔ ∃ h : y ⋖ x, P.orient h = α :=
  Iff.rfl

@[simp] theorem mem_cofaces {α : Bool} {x y : P} :
    y ∈ P.cofaces α x ↔ ∃ h : x ⋖ y, P.orient h = α :=
  Iff.rfl

theorem orient_congr {x x' y y' : P} (hx : x = x') (hy : y = y') (h : y ⋖ x) (h' : y' ⋖ x') :
    P.orient h = P.orient h' := by
  subst hx hy
  rfl

theorem bdry_le_bdryFull (U : LowerSet P) (α : Bool) : P.bdry U α ≤ P.bdryFull U := by
  cases α
  exacts [le_sup_left, le_sup_right]

theorem disjoint_faces (x : P) (α : Bool) : Disjoint (P.faces α x) (P.faces (!α) x) := by
  refine Set.disjoint_left.2 fun _ ⟨_, h⟩ ⟨_, h'⟩ => ?_
  have h'' := h.symm.trans h'
  cases α <;> exact Bool.noConfusion h''

theorem mem_facesIn_Iic_iff_mem_faces {n : ℕ} {x z : P}
    (hx : grade ℕ x = n + 1) (α : Bool) :
    z ∈ P.facesIn (Set.Iic x) n α ↔ z ∈ P.faces α x := by
  constructor
  · intro hz
    have hcov : z ⋖ x := GradeOrder.covBy_of_le_of_grade_eq_add_one hz.1
      (by rw [hx, hz.2.1])
    refine ⟨hcov, ?_⟩
    by_contra hne
    exact Set.disjoint_left.1 hz.2.2 ⟨hcov, Bool.eq_not_iff.2 hne⟩ le_rfl
  · intro hz
    have hzn : grade ℕ z = n := by
      have := Nat.covBy_iff_add_one_eq.1 (hz.1.grade ℕ)
      omega
    refine ⟨hz.1.le, hzn, Set.disjoint_left.2 fun c hc hcx => ?_⟩
    have hce : c = x := GradeOrder.eq_of_le_of_grade_le hcx (by
      have := Nat.covBy_iff_add_one_eq.1 (hc.1.grade ℕ)
      omega)
    subst c
    exact Set.disjoint_left.1 (P.disjoint_faces x α) hz hc

theorem facesIn_subset (U : Set P) (n : ℕ) (α : Bool) : P.facesIn U n α ⊆ U :=
  fun _ hx => hx.1

theorem boundary_le (U : LowerSet P) (n : ℕ) (α : Bool) : P.boundary U n α ≤ U :=
  lowerClosure_le.2 (union_subset (facesIn_subset _ n α) fun _ hx => hx.1.prop)

theorem bdry_eq_boundary {U : LowerSet P} {n : ℕ} (h : krullDim U = n + 1)
    (α : Bool) : P.bdry U α = P.boundary U n α := by
  refine le_antisymm (iSup₂_le fun m hm => ?_) (le_iSup₂_of_le n h le_rfl)
  have h' : m + 1 = n + 1 := by exact_mod_cast hm.symm.trans h
  obtain rfl : m = n := by omega
  exact le_rfl

theorem bdryFull_eq_bdry_sup_bdry_not (U : LowerSet P) (α : Bool) :
    P.bdryFull U = P.bdry U α ⊔ P.bdry U (!α) := by
  cases α
  · rfl
  · exact sup_comm _ _

@[implicit_reducible] def restrict (U : LowerSet P) : OGP.{u} where
  carrier := U
  orient h := P.orient ((LowerSet.coe_covBy_coe U).2 h)

instance (U : LowerSet P) : CoeOut (P.restrict U) P := ⟨Subtype.val⟩

@[ext] theorem restrict_ext {U : LowerSet P} {x y : P.restrict U} (h : (x : P) = y) : x = y :=
  Subtype.ext h

variable (U : LowerSet P) in
transfer_instances P.restrict U with DecidableEq DecidableLE Fintype FinEnum

@[simp] theorem restrict_orient (U : LowerSet P) {x y : P.restrict U} (h : y ⋖ x) :
    (P.restrict U).orient h = P.orient ((LowerSet.coe_covBy_coe U).2 h) :=
  rfl

end OGP

end Atoms.Molecule
