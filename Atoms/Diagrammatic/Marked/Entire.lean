import Atoms.Diagrammatic.Marked.Fibrancy
import Atoms.Diagrammatic.Marked.GrayTensor
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.PseudoGenerating
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem hasLiftingProperty_of_isIso_forget {A B X Y : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)] (p : X ⟶ Y)
    (hX : HasLiftingProperty i (terminal.from X)) : HasLiftingProperty i p := by
  refine ⟨fun {u v} sq => ?_⟩
  obtain ⟨⟨⟨l, hl, -⟩⟩⟩ := hX.sq_hasLift
    (⟨terminal.hom_ext _ _⟩ : CommSq u i (terminal.from X) (terminal.from B))
  refine ⟨⟨⟨l, hl, MarkedPresheaf.hom_ext ?_⟩⟩⟩
  rw [← cancel_epi (MarkedPresheaf.forget.map i), ← Functor.map_comp, ← Functor.map_comp,
    ← Category.assoc, hl, sq.w]

theorem hasLiftingProperty_of_isIso_forget_of_mem_marked {A B X Y : MarkedDiagSet.{u}}
    (i : A ⟶ B) [IsIso (MarkedPresheaf.forget.map i)] (p : X ⟶ Y)
    (h : ∀ ⦃u : A ⟶ X⦄ ⦃v : B ⟶ Y⦄, CommSq u i p v →
      ∀ l : B.underlying ⟶ X.underlying,
        MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u →
        l ≫ MarkedPresheaf.forget.map p = MarkedPresheaf.forget.map v →
        ∀ (T : Atom) (z : diagram B.underlying T),
          z ∈ B.marked T → l.app (op T) z ∈ X.marked T) : HasLiftingProperty i p := by
  refine ⟨fun {u v} sq => ?_⟩
  let l := inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map u
  have hl : MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u :=
    IsIso.hom_inv_id_assoc _ _
  have hp : l ≫ MarkedPresheaf.forget.map p = MarkedPresheaf.forget.map v := by
    rw [← cancel_epi (MarkedPresheaf.forget.map i), ← Category.assoc, hl,
      ← Functor.map_comp, ← Functor.map_comp, sq.w]
  exact ⟨⟨⟨MarkedPresheaf.homMk l (h sq l hl hp),
    MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans hl),
    MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans hp)⟩⟩⟩

instance isIso_forget_map_markingInclusion (U : Atom) (hU : 0 < U.dimension) :
    IsIso (MarkedPresheaf.forget.map (MarkedDiagSet.markingInclusion.{u} U hU)) :=
  inferInstanceAs (IsIso (𝟙 _))

instance isIso_forget_map_markingToMarkedBall (U : Atom) (hU : 0 < U.dimension) :
    IsIso (MarkedPresheaf.forget.map (markingToMarkedBall.{u} U hU)) :=
  inferInstanceAs (IsIso (𝟙 _))

instance isIso_forget_map_flatToMarkedWalkingEquivalence (U : Atom) (hU : 0 < U.dimension) :
    IsIso (MarkedPresheaf.forget.map (MarkedDiagSet.flatToMarkedWalkingEquivalence.{u} U hU)) :=
  inferInstanceAs (IsIso (𝟙 _))

theorem isIso_of_isIso_forget {A B : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (V : Atom) (y : diagram B.underlying V), y ∈ B.marked V →
      ∃ x ∈ A.marked V, (MarkedPresheaf.forget.map i).app (op V) x = y) : IsIso i := by
  let j : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj A :=
    inv (MarkedPresheaf.forget.map i)
  refine ⟨⟨MarkedPresheaf.homMk j fun V y hy => ?_,
    MarkedPresheaf.hom_ext ?_, MarkedPresheaf.hom_ext ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := h V y hy
    have e : j.app (op V) ((MarkedPresheaf.forget.map i).app (op V) x) = x :=
      congrArg (fun f => f.app (op V) x) (IsIso.hom_inv_id (MarkedPresheaf.forget.map i))
    exact (congrArg (· ∈ A.marked V) e).mpr hx
  · exact (Functor.map_comp _ _ _).trans ((IsIso.hom_inv_id (MarkedPresheaf.forget.map i)).trans
      (CategoryTheory.Functor.map_id _ _).symm)
  · exact (Functor.map_comp _ _ _).trans ((IsIso.inv_hom_id (MarkedPresheaf.forget.map i)).trans
      (CategoryTheory.Functor.map_id _ _).symm)

theorem exists_forget_map_app_eq {A B : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)] {V : Atom} (y : diagram B.underlying V) :
    ∃ x, (MarkedPresheaf.forget.map i).app (op V) x = y :=
  ⟨_, congrArg (fun f => f.app (op V) y) (IsIso.inv_hom_id (MarkedPresheaf.forget.map i))⟩

private theorem exists_mem_marked_of_isDegenerate {A B : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)] {V : Atom} {y : diagram B.underlying V}
    (hy : IsDegenerate B.underlying y) :
    ∃ x ∈ A.marked V, (MarkedPresheaf.forget.map i).app (op V) x = y := by
  obtain ⟨x, rfl⟩ := exists_forget_map_app_eq i y
  refine ⟨x, A.mem_marked_of_isDegenerate ?_, rfl⟩
  have e : (inv (MarkedPresheaf.forget.map i)).app (op V)
      ((MarkedPresheaf.forget.map i).app (op V) x) = x :=
    congrArg (fun f => f.app (op V) x) (IsIso.hom_inv_id (MarkedPresheaf.forget.map i))
  exact e ▸ isDegenerate_app (inv (MarkedPresheaf.forget.map i)) hy

theorem MarkedDiagSet.Coinductive.fibration_map_iff (n : ℕ∞) {X Y : MarkedDiagSet.{u}}
    (p : X ⟶ Y) (hY : IsFibrant ((MarkedDiagSet.toCoinductive n).obj Y)) :
    Fibration ((MarkedDiagSet.toCoinductive n).map p) ↔ (coinductiveGenerators.{u} n).rlp p := by
  have hS := coinductiveGenerators_le_monomorphisms.{u} n
  rw [HomotopicalAlgebra.fibration_iff]
  refine ⟨fun hp _ _ j hj => hp _ ⟨hS j hj,
    markedExactCylinder.anodyne_le_weakEquivalences _ hS _ (markedExactCylinder.le_anodyne _ _ hj)⟩,
    fun hp => ?_⟩
  have hYJ := (isFibrant_coinductive_iff n _).1 hY
  have hXJ : HasMarkedRLP (coinductiveGenerators n) X := by
    unfold HasMarkedRLP
    rw [← terminal.comp_from p]
    exact MorphismProperty.comp_mem _ _ _ hp hYJ
  have hH := ((hasMarkedRLP_sup _ _ _).1 ((hasMarkedRLP_sup _ _ _).1 hXJ).1).1
  obtain ⟨-, hM⟩ := (hasMarkedRLP_coinductiveGenerators_iff n X).1 hXJ
  have hI := hasMarkedRLP_of_natural hM (hasMarkedRLP_invertorGenerators_natural X.underlying)
  have hpH : markedHorns.rlp p := antitone_rlp
    (le_sup_left.trans le_sup_left : markedHorns ≤ coinductiveGenerators.{u} n) _ hp
  have hgen : fibrancyGenerators (coinductiveGenerators n) ≤
      (MorphismProperty.ofHoms fun _ : Unit => p).llp := fun _ _ g hg _ _ q hq => by
    cases hq
    rcases hornLike_or_lifting_of_fibrancyGenerators
        (markedHorns_or_isIso_of_coinductiveGenerators n) hXJ hH hI g hg with h | ⟨hi, hl⟩
    · exact h.hasLiftingProperty hpH
    · exact hasLiftingProperty_of_isIso_forget g p hl
  exact markedExactCylinder.rlp_trivialCofibrations_of_rlp_anodyne _ hS p
    (fun _ _ f hf => saturation_le.{u} _ _ hgen f
      (anodyne_le_saturation_fibrancyGenerators _ f hf) _ (MorphismProperty.ofHoms.mk ()))
    ((isFibrant_coinductive_iff_isFibrant n _).1 hY)

theorem MarkedDiagSet.Coinductive.isPseudoGenerating (n : ℕ∞) :
    IsPseudoGenerating (C := MarkedDiagSet.Coinductive.{u} n) (coinductiveGenerators n) where
  le_trivialCofibrations _ _ j hj := ⟨coinductiveGenerators_le_monomorphisms n j hj,
    markedExactCylinder.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms n)
      j (markedExactCylinder.le_anodyne _ j hj)⟩
  fibration_iff := fun _ _ p hY => fibration_map_iff n p hY

instance MarkedDiagSet.Coinductive.hasFactorization_coinductiveGenerators (n : ℕ∞) :
    MorphismProperty.HasFactorization
      (MorphismProperty.rlp (C := MarkedDiagSet.Coinductive.{u} n) (coinductiveGenerators n)).llp
      (MorphismProperty.rlp (C := MarkedDiagSet.Coinductive.{u} n) (coinductiveGenerators n)) :=
  inferInstanceAs (MorphismProperty.HasFactorization (C := MarkedDiagSet.{u})
    (coinductiveGenerators n).rlp.llp (coinductiveGenerators n).rlp)

theorem MarkedDiagSet.Coinductive.weakEquivalence_of_isIso_forget (n : ℕ∞)
    {A B : MarkedDiagSet.{u}} (i : A ⟶ B) [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ X : DiagSet.{u}, IsInftyCategory n X →
      HasLiftingProperty i (terminal.from (MarkedDiagSet.natural.obj X))) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map i) := by
  refine weakEquivalence_of_hasLiftingProperty _ fun X Y p hX _ _ => ?_
  obtain ⟨hXc, hXn⟩ := (isFibrant_coinductive_iff_natural n X).1 hX
  have := hasMarkedRLP_of_natural (J := MorphismProperty.ofHoms fun _ : Unit => i) hXn
    fun _ _ _ hj => by
      cases hj
      exact h _ hXc
  exact hasLiftingProperty_of_isIso_forget i p (this _ (MorphismProperty.ofHoms.mk ()))

theorem MarkedDiagSet.Coinductive.weakEquivalence_of_isIso_forget_of_lt_dimension (n : ℕ∞)
    {A B : MarkedDiagSet.{u}} (i : A ⟶ B) [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (V : Atom) (z : diagram B.underlying V), z ∈ B.marked V →
      IsDegenerate B.underlying z ∨ n < V.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map i) := by
  refine weakEquivalence_of_isIso_forget n i fun X hX => ⟨fun {u _} _ => ?_⟩
  have hA := (hasMarkedRLP_markingGeneratorsAbove_iff n _).1 ((hasMarkedRLP_sup _ _ _).1
    ((hasMarkedRLP_sup _ _ _).1 (hasMarkedRLP_coinductiveGenerators_natural n hX)).1).2
  let l : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj (MarkedDiagSet.natural.obj X) :=
    inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map u
  refine ⟨⟨⟨MarkedPresheaf.homMk l fun V z hz => ?_, MarkedPresheaf.hom_ext ?_,
    terminal.hom_ext _ _⟩⟩⟩
  · rcases h V z hz with hd | hlt
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _ (isDegenerate_app _ hd)
    · exact hA V _ hlt
  · exact (Functor.map_comp _ _ _).trans (IsIso.hom_inv_id_assoc _ _)

section PushoutProduct

instance isIso_forget_map_markedTensorMap {X Y X' Y' : MarkedDiagSet.{u}} (f : X ⟶ X')
    (g : Y ⟶ Y') [IsIso (MarkedPresheaf.forget.map f)] [IsIso (MarkedPresheaf.forget.map g)] :
    IsIso (MarkedPresheaf.forget.map (markedTensorMap false f g)) := by
  rw [forget_map_markedTensorMap]
  have : IsIso (X := ((X.underlying, Y.underlying) : DiagSet.{u} × DiagSet.{u}))
      (Y := (X'.underlying, Y'.underlying))
      (MarkedPresheaf.forget.map f, MarkedPresheaf.forget.map g) :=
    (isIso_prod_iff (C := DiagSet.{u}) (D := DiagSet.{u})).2 ⟨‹IsIso (MarkedPresheaf.forget.map f)›,
      ‹IsIso (MarkedPresheaf.forget.map g)›⟩
  exact Functor.map_isIso grayTensorBifunctor _

theorem isIso_forget_map_pushoutProduct_left {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) [IsIso (MarkedPresheaf.forget.map f₁)] :
    IsIso (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι) :=
  (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isIso_map_ι_of_left _
    (isIso_forget_map_markedTensorMap f₁ (𝟙 X₂)) (isIso_forget_map_markedTensorMap f₁ (𝟙 Y₂))

theorem isIso_forget_map_pushoutProduct_right {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) [IsIso (MarkedPresheaf.forget.map f₂)] :
    IsIso (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι) :=
  (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isIso_map_ι_of_right _
    (isIso_forget_map_markedTensorMap (𝟙 X₁) f₂) (isIso_forget_map_markedTensorMap (𝟙 Y₁) f₂)

theorem isIso_pushoutProduct_of_isIso_forget {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) [IsIso (MarkedPresheaf.forget.map f₁)] [IsIso (MarkedPresheaf.forget.map f₂)] :
    IsIso (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι := by
  have := isIso_forget_map_pushoutProduct_left f₁ f₂
  refine isIso_of_isIso_forget _ fun T z hz => ?_
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, y₁, y₂, e, hm, rfl⟩
  · exact exists_mem_marked_of_isDegenerate _ hd
  obtain ⟨x₂, rfl⟩ := exists_forget_map_app_eq f₂ y₂
  rcases hm with hy₁ | hy₂ | ⟨h, -⟩
  · exact exists_mem_marked_ι_eq_of_corner false _ (𝟙 Y₁) f₂ _ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inl_ι e y₁ x₂ (Or.inl hy₁)
  · obtain ⟨x₁, rfl⟩ := exists_forget_map_app_eq f₁ y₁
    exact exists_mem_marked_ι_eq_of_corner false _ f₁ (𝟙 Y₂) _ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inr_ι e x₁ _
      (Or.inr (Or.inl hy₂))
  · exact absurd h Bool.false_ne_true

private theorem exists_corner_of_mem_marked {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) {T : Atom} {w : diagram (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt.underlying T}
    (hw : w ∈ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt.marked T) :
    (∃ x ∈ (markedTensor false Y₁ X₂).marked T,
      (MarkedPresheaf.forget.map (markedTensorMap false (𝟙 Y₁) f₂)).app (op T) x =
        (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι).app (op T) w) ∨
    ∃ x ∈ (markedTensor false X₁ Y₂).marked T,
      (MarkedPresheaf.forget.map (markedTensorMap false f₁ (𝟙 Y₂))).app (op T) x =
        (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι).app (op T) w := by
  let sq := Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂
  have hl (x) : (MarkedPresheaf.forget.map (markedTensorMap false (𝟙 Y₁) f₂)).app (op T) x =
      (MarkedPresheaf.forget.map sq.ι).app (op T)
        ((MarkedPresheaf.forget.map sq.inl).app (op T) x) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Functor.map_comp MarkedPresheaf.forget _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq.inl_ι)) (op T)) x).symm
  have hr (x) : (MarkedPresheaf.forget.map (markedTensorMap false f₁ (𝟙 Y₂))).app (op T) x =
      (MarkedPresheaf.forget.map sq.ι).app (op T)
        ((MarkedPresheaf.forget.map sq.inr).app (op T) x) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Functor.map_comp MarkedPresheaf.forget _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq.inr_ι)) (op T)) x).symm
  obtain ⟨j, x, hx, rfl⟩ := MarkedPresheaf.exists_mem_marked_of_isColimit sq.isPushout.isColimit hw
  rcases j with _ | _ | _
  · refine Or.inl ⟨_, MarkedPresheaf.map_mem_marked
      (((Functor.curry.obj (markedTensorBifunctor.{u} false)).map f₁).app X₂) hx,
      (hl _).trans (congrArg _ ?_)⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Functor.map_comp MarkedPresheaf.forget _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map
          (PushoutCocone.condition_zero sq.isPushout.cocone).symm)) (op T)) x
  · exact Or.inl ⟨x, hx, hl x⟩
  · exact Or.inr ⟨x, hx, hr x⟩

theorem exists_mem_marked_pushoutProduct_ι_eq_iff {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [IsIso (MarkedPresheaf.forget.map f₁)] {T : Atom}
    (z : diagram (grayTensor Y₁.underlying Y₂.underlying) T) :
    (∃ w ∈ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt.marked T,
      (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι).app (op T) w = z) ↔
      IsDegenerate (grayTensor Y₁.underlying Y₂.underlying) z ∨
        ∃ (U V : Atom) (y₁ : diagram Y₁.underlying U) (y₂ : diagram Y₂.underlying V)
          (e : T ≅ Atom.grayTensor U V),
          z = (grayTensor Y₁.underlying Y₂.underlying).map e.hom.op (grayTensorCell y₁ y₂) ∧
          ((y₁ ∈ Y₁.marked U ∧ ∃ x₂, (MarkedPresheaf.forget.map f₂).app (op V) x₂ = y₂) ∨
            (∃ x₁ ∈ X₁.marked U, (MarkedPresheaf.forget.map f₁).app (op U) x₁ = y₁) ∨
            y₂ ∈ Y₂.marked V) := by
  have := isIso_forget_map_pushoutProduct_left f₁ f₂
  refine ⟨fun ⟨w, hw, hwz⟩ => ?_, fun h => ?_⟩
  · subst hwz
    rcases exists_corner_of_mem_marked f₁ f₂ hw with ⟨x, hx, hxw⟩ | ⟨x, hx, hxw⟩
    · rw [← hxw]
      rcases (mem_marked_markedTensor _ _ _ _ _).1 hx with hd | ⟨U, V, y₁, x₂, e, hm, rfl⟩
      · exact Or.inl (isDegenerate_app _ hd)
      refine Or.inr ⟨U, V, y₁, _, e,
        (forget_map_markedTensorMap_app false (𝟙 Y₁) f₂ e.hom y₁ x₂).trans
          (by rw [CategoryTheory.Functor.map_id]; rfl), ?_⟩
      rcases hm with hy | hx | ⟨h, -⟩
      · exact Or.inl ⟨hy, x₂, rfl⟩
      · exact Or.inr (Or.inr (MarkedPresheaf.map_mem_marked f₂ hx))
      · exact absurd h Bool.false_ne_true
    · rw [← hxw]
      rcases (mem_marked_markedTensor _ _ _ _ _).1 hx with hd | ⟨U, V, x₁, y₂, e, hm, rfl⟩
      · exact Or.inl (isDegenerate_app _ hd)
      refine Or.inr ⟨U, V, _, y₂, e,
        (forget_map_markedTensorMap_app false f₁ (𝟙 Y₂) e.hom x₁ y₂).trans
          (by rw [CategoryTheory.Functor.map_id]; rfl), ?_⟩
      rcases hm with hx | hy | ⟨h, -⟩
      · exact Or.inr (Or.inl ⟨x₁, hx, rfl⟩)
      · exact Or.inr (Or.inr hy)
      · exact absurd h Bool.false_ne_true
  · rcases h with hd | ⟨U, V, y₁, y₂, e, rfl, h⟩
    · exact exists_mem_marked_of_isDegenerate _ hd
    rcases h with ⟨hy₁, x₂, rfl⟩ | ⟨x₁, hx₁, rfl⟩ | hy₂
    · exact exists_mem_marked_ι_eq_of_corner false _ (𝟙 Y₁) f₂ _ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inl_ι e y₁ x₂ (Or.inl hy₁)
    · exact exists_mem_marked_ι_eq_of_corner false _ f₁ (𝟙 Y₂) _ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inr_ι e x₁ y₂ (Or.inl hx₁)
    · obtain ⟨x₁, rfl⟩ := exists_forget_map_app_eq f₁ y₁
      exact exists_mem_marked_ι_eq_of_corner false _ f₁ (𝟙 Y₂) _ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inr_ι e x₁ y₂
        (Or.inr (Or.inl hy₂))

end PushoutProduct

private theorem isDegenerate_or_lt_of_mem_marked_markedTensor (n : ℕ∞) {Y₁ Y₂ : MarkedDiagSet.{u}}
    (h₁ : ∀ (V : Atom) (y : diagram Y₁.underlying V), y ∈ Y₁.marked V →
      IsDegenerate Y₁.underlying y ∨ n < V.dimension)
    (h₂ : ∀ (V : Atom) (y : diagram Y₂.underlying V), y ∈ Y₂.marked V →
      IsDegenerate Y₂.underlying y ∨ n < V.dimension)
    {T : Atom} (z : diagram (grayTensor Y₁.underlying Y₂.underlying) T)
    (hz : z ∈ (markedTensor false Y₁ Y₂).marked T) :
    IsDegenerate (grayTensor Y₁.underlying Y₂.underlying) z ∨ n < T.dimension := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, y₁, y₂, e, hm, rfl⟩
  · exact Or.inl hd
  have hT : T.dimension = U.dimension + V.dimension :=
    (Atom.dimension_eq_of_iso e).trans (Atom.dimension_grayTensor U V)
  rcases hm with hy | hy | ⟨h, -⟩
  · refine (h₁ U y₁ hy).imp (fun hd => ?_) fun hlt => lt_of_lt_of_le hlt ?_
    · exact (isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell (Or.inl hd))
    · exact Nat.cast_le.2 (hT ▸ Nat.le_add_right _ _)
  · refine (h₂ V y₂ hy).imp (fun hd => ?_) fun hlt => lt_of_lt_of_le hlt ?_
    · exact (isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell (Or.inr hd))
    · exact Nat.cast_le.2 (hT ▸ Nat.le_add_left _ _)
  · exact absurd h Bool.false_ne_true

private theorem isDegenerate_or_lt_of_mem_marked_markedAtom (n : ℕ∞) (U : Atom)
    (hU : 0 < U.dimension) (hn : n < U.dimension) (V : Atom)
    (y : diagram (MarkedDiagSet.markedAtom.{u} U hU).underlying V)
    (hy : y ∈ (MarkedDiagSet.markedAtom U hU).marked V) :
    IsDegenerate (MarkedDiagSet.markedAtom U hU).underlying y ∨ n < V.dimension := by
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hy with hd | hi
  · exact Or.inl hd
  · exact Or.inr ((congrArg (fun d : ℕ => n < d) (Atom.dimension_eq_of_iso (asIso y.down))).mpr hn)

private theorem isDegenerate_of_mem_marked_markedBall_empty (U : Atom) (V : Atom)
    (y : diagram (markedBall.{u} U ∅ (pos_grade_of_mem_empty U)).underlying V)
    (hy : y ∈ (markedBall U ∅ (pos_grade_of_mem_empty U)).marked V) :
    IsDegenerate (markedBall U ∅ (pos_grade_of_mem_empty U)).underlying y :=
  ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hy).resolve_right fun h => h

theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_markingInclusion_sphere
    (n : ℕ∞) (U V : Atom) (hU : 0 < U.dimension) (hn : n < U.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (MarkedDiagSet.markingInclusion U hU) (sphereToMarkedBall V)).ι) := by
  have := isIso_forget_map_pushoutProduct_left (MarkedDiagSet.markingInclusion.{u} U hU)
    (sphereToMarkedBall V)
  exact weakEquivalence_of_isIso_forget_of_lt_dimension n _ fun _ z hz =>
    isDegenerate_or_lt_of_mem_marked_markedTensor n
      (isDegenerate_or_lt_of_mem_marked_markedAtom n U hU hn)
      (fun W y hy => Or.inl (isDegenerate_of_mem_marked_markedBall_empty V W y hy)) z hz

theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_sphere_markingInclusion
    (n : ℕ∞) (U V : Atom) (hU : 0 < U.dimension) (hn : n < U.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (sphereToMarkedBall V) (MarkedDiagSet.markingInclusion U hU)).ι) := by
  have := isIso_forget_map_pushoutProduct_right (sphereToMarkedBall V)
    (MarkedDiagSet.markingInclusion.{u} U hU)
  exact weakEquivalence_of_isIso_forget_of_lt_dimension n _ fun _ z hz =>
    isDegenerate_or_lt_of_mem_marked_markedTensor n
      (fun W y hy => Or.inl (isDegenerate_of_mem_marked_markedBall_empty V W y hy))
      (isDegenerate_or_lt_of_mem_marked_markedAtom n U hU hn) z hz

end Atoms.Diagrammatic
