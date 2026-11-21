import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FunctionSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InvertibleTransformation
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ZeroObject

open CategoryTheory Simplicial MonoidalCategory

universe u

namespace SSet

variable {X : SSet.{u}}

theorem exists_extension_of_mono_of_lastVertex {A B : SSet.{u}} (j : A ⟶ B) [Mono j]
    (a : A ⟶ X) (P : X _⦋0⦌ → Prop)
    (hP : ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), P (b.app _ (boundary.lastVertex n)) →
      ∃ c : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ c = b)
    (hB : ∀ (m : ℕ) (σ : B _⦋m⦌), σ ∈ B.nonDegenerate m → σ ∉ Set.range (j.app _) →
      ∃ x : A _⦋0⦌, j.app _ x = B.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ (Fin.last m)).op σ ∧
        P (a.app _ x)) :
    ∃ c : B ⟶ X, j ≫ c = a :=
  exists_extension_of_mono_of_vertex j a P Fin.last boundary.lastVertex (fun _ ↦ rfl) hP hB

def initialSubcomplex (X : SSet.{u}) : X.Subcomplex where
  obj n := {σ | ∀ i : Fin (n.unop.len + 1),
    IsInitialObject (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ)}
  map {n m} θ σ hσ i := by
    have h := hσ (θ.unop.toOrderHom i)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

theorem mem_initialSubcomplex_iff {n : ℕ} (σ : X _⦋n⦌) :
    σ ∈ (initialSubcomplex X).obj (Opposite.op ⦋n⦌) ↔
      ∀ i : Fin (n + 1), IsInitialObject (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ) :=
  Iff.rfl

theorem mem_initialSubcomplex_obj_zero_iff (ω : X _⦋0⦌) :
    ω ∈ (initialSubcomplex X).obj (Opposite.op ⦋0⦌) ↔ IsInitialObject ω := by
  rw [mem_initialSubcomplex_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · have h0 := h 0
    rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id,
      Functor.map_id_apply] at h0
  · rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ i), op_id,
      Functor.map_id_apply]

noncomputable def initialAtSubcomplex {L : SSet.{u}} (v : L _⦋0⦌) (X : SSet.{u}) :
    ((ihom L).obj X).Subcomplex :=
  (initialSubcomplex X).preimage (evalVertex v X)

noncomputable def finalAtSubcomplex {L : SSet.{u}} (v : L _⦋0⦌) (X : SSet.{u}) :
    ((ihom L).obj X).Subcomplex :=
  (finalSubcomplex X).preimage (evalVertex v X)

end SSet
