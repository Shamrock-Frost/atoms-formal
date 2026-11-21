import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

def fullSubcomplex (X : SSet.{u}) (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj n := {σ | ∀ i : Fin (n.unop.len + 1), P (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ)}
  map {n m} θ σ hσ i := by
    have h := hσ (θ.unop.toOrderHom i)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

theorem mem_fullSubcomplex_iff {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {n : ℕ}
    (σ : X _⦋n⦌) : σ ∈ (X.fullSubcomplex P).obj _ ↔
      ∀ i : Fin (n + 1), P (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ) := Iff.rfl

@[simp]
theorem mem_fullSubcomplex_obj_zero_iff {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (x : X _⦋0⦌) : x ∈ (X.fullSubcomplex P).obj (op ⦋0⦌) ↔ P x := by
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · have h0 := h 0
    rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id,
      Functor.map_id_apply] at h0
  · rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ i), op_id,
      Functor.map_id_apply]

def fullSubcomplexMap {X Y : SSet.{u}} (f : X ⟶ Y) (P : X _⦋0⦌ → Prop)
    (Q : Y _⦋0⦌ → Prop) (hf : ∀ x, P x → Q (f.app _ x)) :
    (X.fullSubcomplex P : SSet.{u}) ⟶ (Y.fullSubcomplex Q : SSet.{u}) where
  app n := TypeCat.ofHom fun x ↦ ⟨f.app n x.val, fun i ↦ by
    rw [← f.naturality_apply]
    exact hf _ (x.property i)⟩
  naturality n m θ := by
    ext x
    apply Subtype.ext
    exact f.naturality_apply θ x.val

theorem fullSubcomplexMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (P : X _⦋0⦌ → Prop)
    (Q : Y _⦋0⦌ → Prop) (hf : ∀ x, P x → Q (f.app _ x)) :
    fullSubcomplexMap f P Q hf ≫ (Y.fullSubcomplex Q).ι = (X.fullSubcomplex P).ι ≫ f := rfl

instance innerFibration_fullSubcomplex_ι (Z : SSet.{u}) (P : Z _⦋0⦌ → Prop) :
    InnerFibration (Z.fullSubcomplex P).ι :=
  ⟨fun _ _ _ h ↦ by
    obtain @⟨n, i, h0, hn⟩ := h
    exact ⟨fun {a b} sq ↦ by
      have hr : Subcomplex.range b ≤ Z.fullSubcomplex P := by
        rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff,
          mem_fullSubcomplex_iff]
        intro k
        have hk : stdSimplex.obj₀Equiv.symm k ∈ (horn (n + 2) i).obj (op ⦋0⦌) := by
          rw [horn_obj_eq_univ i 0 (by omega)]
          trivial
        have h := (a.app _ ⟨_, hk⟩).property
        rw [mem_fullSubcomplex_obj_zero_iff] at h
        have hev := congrArg (fun f => f.app (op ⦋0⦌) ⟨_, hk⟩) sq.w
        change (a.app _ ⟨_, hk⟩).val = b.app _ (stdSimplex.obj₀Equiv.symm k) at hev
        rw [hev] at h
        have hv : Z.map (SimplexCategory.const ⦋0⦌ ⦋n + 2⦌ k).op
            (yonedaEquiv b) = b.app _ (stdSimplex.obj₀Equiv.symm k) :=
          (b.naturality_apply _ _).symm.trans rfl
        rw [hv]
        exact h
      exact ⟨⟨⟨Subcomplex.lift b hr, by
        rw [← cancel_mono (Z.fullSubcomplex P).ι, Category.assoc,
          Subcomplex.lift_ι, sq.w], Subcomplex.lift_ι _ _⟩⟩⟩⟩⟩

instance quasicategory_fullSubcomplex (X : SSet.{u}) [X.Quasicategory]
    (P : X _⦋0⦌ → Prop) : (X.fullSubcomplex P : SSet.{u}).Quasicategory :=
  quasicategory_of_innerFibration (X.fullSubcomplex P).ι

end SSet
