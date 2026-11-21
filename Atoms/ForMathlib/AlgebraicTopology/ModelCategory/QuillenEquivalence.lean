import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory HomotopicalAlgebra

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
  [ModelCategory C] [ModelCategory D] {adj : F ⊣ G}

theorem IsQuillenEquivalence.weakEquivalence_of_map (h : adj.IsQuillenEquivalence) {X Y : D}
    [IsFibrant X] [IsFibrant Y] [IsCofibrant (G.obj X)] (f : X ⟶ Y) [WeakEquivalence (G.map f)] :
    WeakEquivalence f := by
  have e : adj.homEquiv (G.obj X) X (adj.counit.app X) = 𝟙 _ := by
    rw [adj.homEquiv_unit, adj.right_triangle_components]
  have hε : WeakEquivalence (adj.counit.app X) :=
    (h.weakEquivalence_iff (A := G.obj X) (X := X) (adj.counit.app X)).2 (e ▸ inferInstance)
  have e' : adj.homEquiv (G.obj X) Y (adj.counit.app X ≫ f) = G.map f :=
    (adj.homEquiv_naturality_right _ _).trans
      ((congrArg (· ≫ G.map f) e).trans (Category.id_comp _))
  have : WeakEquivalence (adj.counit.app X ≫ f) :=
    (h.weakEquivalence_iff (A := G.obj X) (X := Y) (adj.counit.app X ≫ f)).2
      (e' ▸ ‹WeakEquivalence (G.map f)›)
  exact weakEquivalence_of_precomp (adj.counit.app X) f

theorem IsQuillenEquivalence.weakEquivalence_map_iff (h : adj.IsQuillenEquivalence) {X Y : D}
    [IsFibrant X] [IsFibrant Y] [IsCofibrant (G.obj X)] (f : X ⟶ Y) :
    WeakEquivalence (G.map f) ↔ WeakEquivalence f :=
  ⟨fun _ ↦ h.weakEquivalence_of_map f, fun _ ↦ h.toIsQuillen.weakEquivalence_map_of_isFibrant f⟩

end CategoryTheory.Adjunction
