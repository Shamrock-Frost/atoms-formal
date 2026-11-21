import Atoms.Diagrammatic.Vertex
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

open CategoryTheory

universe u

namespace Atoms.Diagrammatic.DiagSet

variable {X Y Z : DiagSet.{u}}

def π₀Rel (X : DiagSet.{u}) (x y : X.Vertex) : Prop := Nonempty (X.Edge x y)

def π₀ (X : DiagSet.{u}) : Type u := Quot X.π₀Rel

def π₀.mk (x : X.Vertex) : X.π₀ := Quot.mk _ x

theorem π₀.mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

theorem π₀.sound {x y : X.Vertex} (e : X.Edge x y) : π₀.mk x = π₀.mk y :=
  Quot.sound ⟨e⟩

theorem π₀.mk_eq_mk_iff (x y : X.Vertex) :
    π₀.mk x = π₀.mk y ↔ Relation.EqvGen X.π₀Rel x y := Quot.eq

def mapπ₀ (f : X ⟶ Y) : X.π₀ → Y.π₀ :=
  Quot.lift (fun x => π₀.mk (x.map f)) (fun _ _ ⟨e⟩ => π₀.sound (e.map f))

@[simp] theorem mapπ₀_mk (f : X ⟶ Y) (x : X.Vertex) :
    mapπ₀ f (π₀.mk x) = π₀.mk (x.map f) := rfl

@[simp] theorem mapπ₀_id_apply (c : X.π₀) : mapπ₀ (𝟙 X) c = c := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective c
  rfl

@[simp] theorem mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (c : X.π₀) :
    mapπ₀ (f ≫ g) c = mapπ₀ g (mapπ₀ f c) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective c
  rfl

def π₀EquivSSet (X : DiagSet.{u}) : X.π₀ ≃ SSet.π₀ (DiagSet.toSSet.obj X) where
  toFun := Quot.lift (fun x => SSet.π₀.mk (X.vertexEquivSSet x))
    (fun _ _ ⟨e⟩ => SSet.π₀.sound (X.edgeEquivSSet e))
  invFun := SSet.π₀.lift (fun x => π₀.mk (X.vertexEquivSSet.symm x))
    (fun _ _ e => π₀.sound (X.edgeEquivSSet.symm e))
  left_inv c := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective c
    exact congrArg π₀.mk (X.vertexEquivSSet.symm_apply_apply x)
  right_inv c := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
    exact congrArg SSet.π₀.mk (X.vertexEquivSSet.apply_symm_apply x)

@[simp] theorem π₀EquivSSet_mk (x : X.Vertex) :
    X.π₀EquivSSet (π₀.mk x) = SSet.π₀.mk (X.vertexEquivSSet x) := rfl

theorem π₀EquivSSet_mapπ₀ (f : X ⟶ Y) (c : X.π₀) :
    Y.π₀EquivSSet (mapπ₀ f c) =
      SSet.mapπ₀ (DiagSet.toSSet.map f) (X.π₀EquivSSet c) := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective c
  rw [mapπ₀_mk, π₀EquivSSet_mk, π₀EquivSSet_mk, SSet.mapπ₀_mk, vertexEquivSSet_map]

end Atoms.Diagrammatic.DiagSet
