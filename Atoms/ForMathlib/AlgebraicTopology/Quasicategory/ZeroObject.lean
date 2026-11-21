import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject

open CategoryTheory Simplicial

universe u

namespace SSet

variable {X : SSet.{u}}

def IsInitialObject (ω : X _⦋0⦌) : Prop :=
  IsFinal (X := X.op) (opObjEquiv.symm ω)

def IsZeroObject (ω : X _⦋0⦌) : Prop :=
  IsFinal ω ∧ IsInitialObject ω

def IsPointed (X : SSet.{u}) : Prop :=
  ∃ ω : X _⦋0⦌, IsZeroObject ω

theorem isInitialObject_op_iff (ω : X _⦋0⦌) :
    IsInitialObject (X := X.op) (opObjEquiv.symm ω) ↔ IsFinal ω :=
  (isFinal_iso_hom_app_iff (opFunctorCompOpFunctorIso.app X) _).symm

theorem isZeroObject_op_iff (ω : X _⦋0⦌) :
    IsZeroObject (X := X.op) (opObjEquiv.symm ω) ↔ IsZeroObject ω :=
  (and_comm.trans (and_congr_left' (isInitialObject_op_iff ω)))

theorem isPointed_op_iff : X.op.IsPointed ↔ X.IsPointed :=
  ⟨fun ⟨ω, h⟩ ↦ ⟨opObjEquiv ω, (isZeroObject_op_iff _).1 h⟩,
    fun ⟨ω, h⟩ ↦ ⟨opObjEquiv.symm ω, (isZeroObject_op_iff ω).2 h⟩⟩

def zeroSubcomplex (X : SSet.{u}) : X.Subcomplex where
  obj n := {σ | ∀ i : Fin (n.unop.len + 1),
    IsZeroObject (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ)}
  map {n m} θ σ hσ i := by
    have h := hσ (θ.unop.toOrderHom i)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

theorem mem_zeroSubcomplex_iff {n : ℕ} (σ : X _⦋n⦌) :
    σ ∈ (zeroSubcomplex X).obj (Opposite.op ⦋n⦌) ↔
      ∀ i : Fin (n + 1), IsZeroObject (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ) :=
  Iff.rfl

theorem mem_zeroSubcomplex_obj_zero_iff (ω : X _⦋0⦌) :
    ω ∈ (zeroSubcomplex X).obj _ ↔ IsZeroObject ω := by
  have h (i : Fin 1) : X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ i).op ω = ω := by
    rw [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ i), op_id,
      Functor.map_id_apply]
  rw [mem_zeroSubcomplex_iff]
  exact ⟨fun hω ↦ h 0 ▸ hω 0, fun hω i ↦ (h i).symm ▸ hω⟩

end SSet
