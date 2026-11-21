import Atoms.Diagrammatic.Marked.Entire

open CategoryTheory Limits Opposite HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem MarkedDiagSet.Coinductive.weakEquivalence_of_isIso_forget_of_mem_marked (n : ℕ∞)
    {A B : MarkedDiagSet.{u}} (i : A ⟶ B) [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (V : Atom) (z : diagram B.underlying V), z ∈ B.marked V →
      (∃ w ∈ A.marked V, (MarkedPresheaf.forget.map i).app (op V) w = z) ∨
        IsEquivalence B.underlying z ∨ n < V.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map i) := by
  refine weakEquivalence_of_isIso_forget n i fun X hX => ⟨fun {u _} _ => ?_⟩
  have hA := (hasMarkedRLP_markingGeneratorsAbove_iff n _).1 ((hasMarkedRLP_sup _ _ _).1
    ((hasMarkedRLP_sup _ _ _).1 (hasMarkedRLP_coinductiveGenerators_natural n hX)).1).2
  let l : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj (MarkedDiagSet.natural.obj X) :=
    inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map u
  have hl : MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u :=
    IsIso.hom_inv_id_assoc _ _
  refine ⟨⟨⟨MarkedPresheaf.homMk l fun V z hz => ?_, MarkedPresheaf.hom_ext ?_,
    terminal.hom_ext _ _⟩⟩⟩
  · rcases h V z hz with ⟨w, hw, rfl⟩ | he | hlt
    · have e : l.app _ ((MarkedPresheaf.forget.map i).app _ w) =
          (MarkedPresheaf.forget.map u).app _ w :=
        ConcreteCategory.congr_hom (congr_app hl _) w
      exact e ▸ MarkedPresheaf.map_mem_marked u hw
    · exact (MarkedDiagSet.mem_marked_natural_iff X V _).2 (he.map l)
    · exact hA V _ hlt
  · exact (Functor.map_comp _ _ _).trans hl

private theorem exists_mem_marked_or_lt_of_corner (n : ℕ∞) {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (sq : (Functor.curry.obj (markedTensorBifunctor.{u} false)).PushoutObjObj f₁ f₂)
    {A B : MarkedDiagSet.{u}} (a : A ⟶ Y₁) (b : B ⟶ Y₂) [IsIso (MarkedPresheaf.forget.map a)]
    [IsIso (MarkedPresheaf.forget.map b)] (c : markedTensor false A B ⟶ sq.pt)
    (hc : c ≫ sq.ι = markedTensorMap false a b)
    (ha : ∀ (U : Atom) (y : diagram Y₁.underlying U), y ∈ Y₁.marked U →
      (∃ x ∈ A.marked U, (MarkedPresheaf.forget.map a).app (op U) x = y) ∨ n < U.dimension)
    (hb : ∀ (V : Atom) (y : diagram Y₂.underlying V), y ∈ Y₂.marked V →
      (∃ x ∈ B.marked V, (MarkedPresheaf.forget.map b).app (op V) x = y) ∨ n < V.dimension)
    {T : Atom} (z : diagram (grayTensor Y₁.underlying Y₂.underlying) T)
    (hz : z ∈ (markedTensor false Y₁ Y₂).marked T) :
    (∃ w ∈ sq.pt.marked T, (MarkedPresheaf.forget.map sq.ι).app (op T) w = z) ∨
      IsEquivalence (grayTensor Y₁.underlying Y₂.underlying) z ∨ n < T.dimension := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, y₁, y₂, e, hm, rfl⟩
  · exact Or.inr (Or.inl (degenerate_isEquivalence _ _ hd))
  have hT : T.dimension = U.dimension + V.dimension :=
    (Atom.dimension_eq_of_iso e).trans (Atom.dimension_grayTensor U V)
  rcases hm with hy₁ | hy₂ | ⟨h, -⟩
  · rcases ha U y₁ hy₁ with ⟨x₁, hx₁, rfl⟩ | hlt
    · obtain ⟨x₂, rfl⟩ := exists_forget_map_app_eq b y₂
      exact Or.inl (exists_mem_marked_ι_eq_of_corner false sq a b c hc e x₁ x₂ (Or.inl hx₁))
    · exact Or.inr (Or.inr (lt_of_lt_of_le hlt (Nat.cast_le.2 (hT ▸ Nat.le_add_right _ _))))
  · rcases hb V y₂ hy₂ with ⟨x₂, hx₂, rfl⟩ | hlt
    · obtain ⟨x₁, rfl⟩ := exists_forget_map_app_eq a y₁
      exact Or.inl (exists_mem_marked_ι_eq_of_corner false sq a b c hc e x₁ x₂
        (Or.inr (Or.inl hx₂)))
    · exact Or.inr (Or.inr (lt_of_lt_of_le hlt (Nat.cast_le.2 (hT ▸ Nat.le_add_left _ _))))
  · exact absurd h Bool.false_ne_true

private theorem exists_mem_marked_or_lt_markedAtom (n : ℕ∞) (U : Atom) (hU : 0 < U.dimension)
    (hn : n < U.dimension) (V : Atom)
    (y : diagram (MarkedDiagSet.markedAtom.{u} U hU).underlying V)
    (hy : y ∈ (MarkedDiagSet.markedAtom U hU).marked V) :
    (∃ x ∈ ((MarkedPresheaf.flat atomMarking).obj (ball.{u} U)).marked V,
      (MarkedPresheaf.forget.map (MarkedDiagSet.markingInclusion U hU)).app (op V) x = y) ∨
      n < V.dimension := by
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hy with hd | hi
  · exact Or.inl ⟨y, (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).2 hd, rfl⟩
  · exact Or.inr ((congrArg (fun d : ℕ => n < d) (Atom.dimension_eq_of_iso (asIso y.down))).mpr hn)

theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_markingGeneratorsAbove_left
    (n : ℕ∞) {A B X Y : MarkedDiagSet.{u}} (g : A ⟶ B) (hg : markingGeneratorsAbove n g)
    (i : X ⟶ Y) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) g i).ι) := by
  obtain ⟨⟨U, hn⟩⟩ := hg
  have hU : 0 < U.dimension := Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) hn)
  have := isIso_forget_map_pushoutProduct_left (MarkedDiagSet.markingInclusion.{u} U hU) i
  exact weakEquivalence_of_isIso_forget_of_mem_marked n _ fun _ z hz =>
    exists_mem_marked_or_lt_of_corner n _ _ (𝟙 _) _ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) (MarkedDiagSet.markingInclusion U hU)
        i).inr_ι
      (exists_mem_marked_or_lt_markedAtom.{u} n U hU hn) (fun _ y hy => Or.inl ⟨y, hy, rfl⟩) z hz

theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_markingGeneratorsAbove_right
    (n : ℕ∞) {A B X Y : MarkedDiagSet.{u}} (i : X ⟶ Y) (g : A ⟶ B)
    (hg : markingGeneratorsAbove n g) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) i g).ι) := by
  obtain ⟨⟨U, hn⟩⟩ := hg
  have hU : 0 < U.dimension := Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) hn)
  have := isIso_forget_map_pushoutProduct_right i (MarkedDiagSet.markingInclusion.{u} U hU)
  exact weakEquivalence_of_isIso_forget_of_mem_marked n _ fun _ z hz =>
    exists_mem_marked_or_lt_of_corner n _ (𝟙 _) _ _ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) i
        (MarkedDiagSet.markingInclusion U hU)).inl_ι
      (fun _ y hy => Or.inl ⟨y, hy, rfl⟩) (exists_mem_marked_or_lt_markedAtom.{u} n U hU hn) z hz

end Atoms.Diagrammatic
