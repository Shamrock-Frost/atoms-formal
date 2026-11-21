import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

namespace CategoryTheory.Bicategory

open Limits

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

structure IsTwoTerminal (z : B) : Prop where
  nonempty_hom (a : B) : Nonempty (a ⟶ z)
  subsingleton_hom (a : B) : Subsingleton (a ⟶ z)
  nonempty_hom₂ {a : B} (f g : a ⟶ z) : Nonempty (f ⟶ g)
  subsingleton_hom₂ {a : B} (f g : a ⟶ z) : Subsingleton (f ⟶ g)

namespace IsTwoTerminal

variable {z : B}

theorem isIso (hz : IsTwoTerminal z) {a : B} {f g : a ⟶ z} (θ : f ⟶ g) : IsIso θ :=
  ⟨(hz.nonempty_hom₂ g f).some, (hz.subsingleton_hom₂ f f).elim _ _,
    (hz.subsingleton_hom₂ g g).elim _ _⟩

theorem nonempty_adjunction_of_isIso (hz : IsTwoTerminal z) {a : B} (u : a ⟶ z) (t : z ⟶ a)
    (η : 𝟙 a ⟶ u ≫ t) (hη : IsIso (t ◁ η)) : Nonempty (u ⊣ t) := by
  let ε : t ≫ u ⟶ 𝟙 z := (hz.nonempty_hom₂ _ _).some
  have hl : leftZigzag η ε = (λ_ u).hom ≫ (ρ_ u).inv := (hz.subsingleton_hom₂ _ _).elim _ _
  have : IsIso ε := hz.isIso ε
  have : IsIso (rightZigzag η ε) := by
    dsimp only [rightZigzag, bicategoricalComp]
    infer_instance
  refine ⟨⟨η, ε, hl, ?_⟩⟩
  rw [← cancel_epi (rightZigzag η ε ≫ (λ_ t).hom ≫ (ρ_ t).inv)]
  calc
    _ = rightZigzag η ε ⊗≫ rightZigzag η ε := by bicategory
    _ = rightZigzag η ε := rightZigzag_idempotent_of_left_triangle _ _ hl
    _ = _ := by simp

theorem nonempty_adjunction_iff (hz : IsTwoTerminal z) {a : B} (u : a ⟶ z) (t : z ⟶ a) :
    Nonempty (u ⊣ t) ↔ ∀ {x : B} (k : x ⟶ z), Nonempty (IsTerminal (k ≫ t)) := by
  refine ⟨fun ⟨adj⟩ x k ↦ ⟨IsTerminal.ofUniqueHom
    (fun _ ↦ adj.homEquiv₂ (hz.nonempty_hom₂ _ _).some)
    (fun _ _ ↦ adj.homEquiv₂.symm.injective ((hz.subsingleton_hom₂ _ _).elim _ _))⟩, fun h ↦ ?_⟩
  exact hz.nonempty_adjunction_of_isIso u t ((h u).some.from _) (isIso_of_isTerminal
    ((h (𝟙 z)).some.ofIso (λ_ t ≪≫ (ρ_ t).symm)) ((h (t ≫ u)).some.ofIso (α_ t u t)) _)

theorem nonempty_adjunction_comp (hz : IsTwoTerminal z) {a b : B} {f : b ⟶ a} {g : a ⟶ b}
    (adj : f ⊣ g) (ua : a ⟶ z) (ub : b ⟶ z) {t : z ⟶ a} (ht : Nonempty (ua ⊣ t)) :
    Nonempty (ub ⊣ t ≫ g) := by
  obtain rfl : f ≫ ua = ub := (hz.subsingleton_hom b).elim _ _
  exact ⟨adj.comp ht.some⟩

end IsTwoTerminal

end CategoryTheory.Bicategory
