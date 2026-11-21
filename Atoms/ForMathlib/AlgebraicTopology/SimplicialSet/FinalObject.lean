import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.RightFibration
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinProduct
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.MapOver
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open CategoryTheory Limits Simplicial Opposite MorphismProperty MonoidalCategory
  CartesianMonoidalCategory
open AugmentedSimplexCategory (inl'_eq_δ_last inl'_comp_σ_last inr'_comp_σ_last)

universe u

namespace SSet

noncomputable abbrev sliceAt (C : SSet.{u}) (c : C _⦋0⦌) : SSet.{u} :=
  (slice Δ[0]).obj (Under.mk (yonedaEquiv.symm c))

noncomputable def sliceAtπ (C : SSet.{u}) (c : C _⦋0⦌) : sliceAt C c ⟶ C :=
  joinInclLeft _ Δ[0] ≫
    ((joinRightUnderAdjunction Δ[0]).counit.app (Under.mk (yonedaEquiv.symm c))).right

theorem comp_sliceAtπ {X C : SSet.{u}} {c : C _⦋0⦌} (f : X ⟶ sliceAt C c) :
    f ≫ sliceAtπ C c =
      joinInclLeft X Δ[0] ≫ (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm f).right := by
  rw [Adjunction.homEquiv_counit, Under.comp_right, sliceAtπ]
  exact (joinInclLeft_comp_joinMap_assoc f (𝟙 Δ[0]) _).symm

private noncomputable def degenerateEdge {C : SSet.{u}} (c : C _⦋0⦌) :
    (joinRightUnder Δ[0]).obj Δ[0] ⟶ Under.mk (yonedaEquiv.symm c) :=
  Under.homMk (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm c) (by
    rw [← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
    rfl)

noncomputable def sliceId (C : SSet.{u}) (c : C _⦋0⦌) : (sliceAt C c) _⦋0⦌ :=
  yonedaEquiv ((joinRightUnderAdjunction Δ[0]).homEquiv _ _ (degenerateEdge c))

@[reassoc]
theorem sliceId_comp_sliceAtπ (C : SSet.{u}) (c : C _⦋0⦌) :
    yonedaEquiv.symm (sliceId C c) ≫ sliceAtπ C c = yonedaEquiv.symm c := by
  rw [comp_sliceAtπ, sliceId, Equiv.symm_apply_apply, Equiv.symm_apply_apply, degenerateEdge]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (stdSimplex.isTerminalObj₀.hom_ext _ (𝟙 _)))).trans (Category.id_comp _)

noncomputable abbrev pointedCone (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  pushout (joinMap (yonedaEquiv.symm x) (𝟙 Δ[0])) (stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0]))

theorem rightAnodyneExtensions_pointedCone_inr (X : SSet.{u}) (x : X _⦋0⦌) :
    rightAnodyneExtensions (pushout.inr (joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]))
      (stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0])) : Δ[0] ⟶ pointedCone X x) := by
  intro _ _ p hp
  have : Mono (yonedaEquiv.symm x) := stdSimplex.isTerminalObj₀.mono_from _
  have := rightAnodyneExtensions_joinMap_id (yonedaEquiv.symm x) p hp
  exact (IsPushout.of_hasPushout (joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]))
    (stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0]))).flip.hasLiftingProperty p

private lemma transpose_section {X : SSet.{u}} {x : X _⦋0⦌} {s : X ⟶ sliceAt X x}
    (hs : s ≫ sliceAtπ X x = 𝟙 X)
    (hx : yonedaEquiv.symm x ≫ s = yonedaEquiv.symm (sliceId X x)) :
    joinInclLeft X Δ[0] ≫ (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm s).right = 𝟙 X ∧
      joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]) ≫
        (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm s).right =
          stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm x := by
  refine ⟨(comp_sliceAtπ s).symm.trans hs, ?_⟩
  have h := congrArg Under.Hom.right
    ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left_symm (yonedaEquiv.symm x) s)
  rw [hx, sliceId, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Under.comp_right] at h
  exact h.symm

theorem rightAnodyneExtensions_of_section {X : SSet.{u}} {x : X _⦋0⦌} (s : X ⟶ sliceAt X x)
    (hs : s ≫ sliceAtπ X x = 𝟙 X)
    (hx : yonedaEquiv.symm x ≫ s = yonedaEquiv.symm (sliceId X x)) :
    rightAnodyneExtensions (yonedaEquiv.symm x : Δ[0] ⟶ X) := by
  let t := (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm s).right
  obtain ⟨ht₁, ht₂⟩ := transpose_section hs hx
  let r := pushout.desc t (yonedaEquiv.symm x) ht₂
  let j := joinInclLeft X Δ[0] ≫ pushout.inl (joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]))
    (stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0]))
  have hj : yonedaEquiv.symm x ≫ j = pushout.inr _ _ := by
    rw [← Category.assoc, ← joinInclLeft_comp_joinMap, Category.assoc,
      pushout.condition (f := joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]))
        (g := stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0])),
      ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
  let h : RetractArrow (yonedaEquiv.symm x : Δ[0] ⟶ X)
      (pushout.inr (joinMap (yonedaEquiv.symm x) (𝟙 Δ[0]))
        (stdSimplex.isTerminalObj₀.from (join Δ[0] Δ[0]))) :=
    { i := Arrow.homMk (𝟙 _) j (by rw [Category.id_comp]; exact hj.symm)
      r := Arrow.homMk (𝟙 _) r (by
        rw [Category.id_comp]
        exact (pushout.inr_desc t (yonedaEquiv.symm x) ht₂).symm)
      retract := Arrow.hom_ext _ _ (Category.comp_id _) ((Category.assoc _ _ _).trans
        ((congrArg _ (pushout.inl_desc t (yonedaEquiv.symm x) ht₂)).trans ht₁)) }
  intro _ _ p hp
  have := rightAnodyneExtensions_pointedCone_inr X x p hp
  exact h.leftLiftingProperty p

@[reassoc]
private lemma joinMap_comp_id {X X' X'' Y : SSet.{u}} (f : X ⟶ X') (f' : X' ⟶ X'') :
    joinMap (f ≫ f') (𝟙 Y) = joinMap f (𝟙 Y) ≫ joinMap f' (𝟙 Y) :=
  (congrArg (joinMap (f ≫ f')) (Category.comp_id (𝟙 Y)).symm).trans
    (joinFunctor.map_comp (X := (X, Y)) (Y := (X', Y)) (Z := (X'', Y)) (f, 𝟙 Y) (f', 𝟙 Y))

private lemma join_stdSimplex_hom_ext {m k N : ℕ} {f g : join Δ[m] Δ[k] ⟶ Δ[N]}
    (h₁ : joinInclLeft Δ[m] Δ[k] ≫ f = joinInclLeft Δ[m] Δ[k] ≫ g)
    (h₂ : joinInclRight Δ[m] Δ[k] ≫ f = joinInclRight Δ[m] Δ[k] ≫ g) : f = g := by
  obtain ⟨φ, hφ⟩ := stdSimplex.map_surjective ((stdSimplexJoinIso m k).inv ≫ f)
  obtain ⟨ψ, hψ⟩ := stdSimplex.map_surjective ((stdSimplexJoinIso m k).inv ≫ g)
  rw [← cancel_epi (stdSimplexJoinIso m k).inv, ← hφ, ← hψ]
  refine congrArg _ (AugmentedSimplexCategory.tensorObj_hom_ext (x := .of ⦋m⦌) (y := .of ⦋k⦌)
    (z := .of ⦋N⦌) φ ψ (stdSimplex.map_injective ?_) (stdSimplex.map_injective ?_))
  · change stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋k⦌ ≫ φ) =
      stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋k⦌ ≫ ψ)
    refine (stdSimplex.map_comp _ _).trans (Eq.trans ?_ (stdSimplex.map_comp _ _).symm)
    rw [hφ, hψ, ← joinInclLeft_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id_assoc, h₁]
  · change stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋k⦌ ≫ φ) =
      stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋k⦌ ≫ ψ)
    refine (stdSimplex.map_comp _ _).trans (Eq.trans ?_ (stdSimplex.map_comp _ _).symm)
    rw [hφ, hψ, ← joinInclRight_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id_assoc, h₂]

private noncomputable def mergeLast (n : ℕ) : join Δ[n + 1] Δ[0] ⟶ Δ[n + 1] :=
  (stdSimplexJoinIso (n + 1) 0).hom ≫ stdSimplex.map (SimplexCategory.σ (Fin.last (n + 1)))

@[reassoc]
private lemma joinInclLeft_comp_mergeLast (n : ℕ) :
    joinInclLeft Δ[n + 1] Δ[0] ≫ mergeLast n = 𝟙 _ := by
  rw [mergeLast, ← Category.assoc, joinInclLeft_comp_stdSimplexJoinIso_hom]
  exact (stdSimplex.map_comp _ _).symm.trans
    ((congrArg stdSimplex.map (inl'_comp_σ_last (n + 1))).trans (stdSimplex.map_id _))

@[reassoc]
private lemma joinInclRight_comp_mergeLast (n : ℕ) :
    joinInclRight Δ[n + 1] Δ[0] ≫ mergeLast n =
      stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) := by
  rw [mergeLast, ← Category.assoc, joinInclRight_comp_stdSimplexJoinIso_hom]
  exact (stdSimplex.map_comp _ _).symm.trans (congrArg stdSimplex.map (inr'_comp_σ_last n))

private abbrev joinPointMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  AugmentedSimplexCategory.tensorHomOf θ (𝟙 ⦋0⦌)

private lemma inl'_comp_joinPointMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌ ≫ joinPointMap θ =
      θ ≫ AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ :=
  AugmentedSimplexCategory.inl_comp_tensorHom (x₁ := .of ⦋m⦌) (y₁ := .of ⦋n⦌) (x₂ := .of ⦋0⦌)
    (y₂ := .of ⦋0⦌) θ (𝟙 _)

private lemma inr'_comp_joinPointMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ joinPointMap θ =
      AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ :=
  (AugmentedSimplexCategory.inr_comp_tensorHom (x₁ := .of ⦋m⦌) (y₁ := .of ⦋n⦌) (x₂ := .of ⦋0⦌)
    (y₂ := .of ⦋0⦌) θ (𝟙 _)).trans (Category.id_comp _)

private lemma joinMap_stdSimplexMap_comp_stdSimplexJoinIso {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (stdSimplex.map θ) (𝟙 Δ[0]) ≫ (stdSimplexJoinIso n 0).hom =
      (stdSimplexJoinIso m 0).hom ≫
        stdSimplex.map (joinPointMap θ) := by
  refine join_stdSimplex_hom_ext ?_ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_stdSimplexJoinIso_hom,
      ← Category.assoc, joinInclLeft_comp_stdSimplexJoinIso_hom]
    exact (stdSimplex.map_comp _ _).symm.trans ((congrArg stdSimplex.map
      (inl'_comp_joinPointMap θ).symm).trans (stdSimplex.map_comp _ _))
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp,
      joinInclRight_comp_stdSimplexJoinIso_hom, ← Category.assoc,
      joinInclRight_comp_stdSimplexJoinIso_hom]
    exact (congrArg stdSimplex.map (inr'_comp_joinPointMap θ).symm).trans
      (stdSimplex.map_comp _ _)

@[reassoc]
private lemma mergeLast_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (stdSimplex.map (joinPointMap θ)) (𝟙 Δ[0]) ≫
      mergeLast n =
        mergeLast m ≫ stdSimplex.map (joinPointMap θ) := by
  refine join_stdSimplex_hom_ext ?_ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_mergeLast, Category.comp_id,
      joinInclLeft_comp_mergeLast_assoc]
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_mergeLast,
      joinInclRight_comp_mergeLast_assoc]
    exact (congrArg stdSimplex.map (inr'_comp_joinPointMap θ).symm).trans
      (stdSimplex.map_comp _ _)

private noncomputable def mergeCone (n : ℕ) : join (join Δ[n] Δ[0]) Δ[0] ⟶ join Δ[n] Δ[0] :=
  joinMap (stdSimplexJoinIso n 0).hom (𝟙 Δ[0]) ≫ mergeLast n ≫ (stdSimplexJoinIso n 0).inv

@[reassoc]
private lemma mergeCone_naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (joinMap (stdSimplex.map θ) (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ mergeCone n =
      mergeCone m ≫ joinMap (stdSimplex.map θ) (𝟙 Δ[0]) := by
  have h := joinMap_stdSimplexMap_comp_stdSimplexJoinIso θ
  have h' : (stdSimplexJoinIso m 0).inv ≫ joinMap (stdSimplex.map θ) (𝟙 Δ[0]) =
      stdSimplex.map (joinPointMap θ) ≫
        (stdSimplexJoinIso n 0).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [mergeCone, mergeCone, ← joinMap_comp_id_assoc, h, joinMap_comp_id, Category.assoc,
    mergeLast_naturality_assoc, Category.assoc, Category.assoc, h']

@[reassoc]
private lemma joinMap_joinInclLeft_comp_mergeCone (n : ℕ) :
    joinMap (joinInclLeft Δ[n] Δ[0]) (𝟙 Δ[0]) ≫ mergeCone n = 𝟙 _ := by
  rw [mergeCone, ← joinMap_comp_id_assoc, joinInclLeft_comp_stdSimplexJoinIso_hom,
    ← Category.assoc, Iso.comp_inv_eq, Category.id_comp]
  refine join_stdSimplex_hom_ext ?_ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_mergeLast, Category.comp_id,
      joinInclLeft_comp_stdSimplexJoinIso_hom]
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_mergeLast,
      joinInclRight_comp_stdSimplexJoinIso_hom]

@[reassoc]
private lemma joinMap_joinInclRight_comp_mergeCone (n : ℕ) :
    joinMap (joinInclRight Δ[n] Δ[0]) (𝟙 Δ[0]) ≫ mergeCone n =
      stdSimplex.isTerminalObj₀.from _ ≫ joinInclRight Δ[n] Δ[0] := by
  rw [mergeCone, ← joinMap_comp_id_assoc, joinInclRight_comp_stdSimplexJoinIso_hom,
    ← Category.assoc, Iso.comp_inv_eq, Category.assoc, joinInclRight_comp_stdSimplexJoinIso_hom]
  refine join_stdSimplex_hom_ext ?_ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_mergeLast, Category.comp_id,
      ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_mergeLast,
      ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]

@[reassoc]
private lemma joinInclRight_comp_mergeCone (n : ℕ) :
    joinInclRight (join Δ[n] Δ[0]) Δ[0] ≫ mergeCone n = joinInclRight Δ[n] Δ[0] := by
  rw [mergeCone, joinInclRight_comp_joinMap_assoc, Category.id_comp, ← Category.assoc,
    Iso.comp_inv_eq, joinInclRight_comp_stdSimplexJoinIso_hom]
  exact joinInclRight_comp_mergeLast n

private lemma sliceObjEquiv_yonedaEquiv_homEquiv {T : SSet.{u}} {t : Under T} {n : ℕ}
    (g : (joinRightUnder T).obj Δ[n] ⟶ t) :
    sliceObjEquiv T t n (yonedaEquiv ((joinRightUnderAdjunction T).homEquiv _ _ g)) =
      ⟨g.right, Under.w g⟩ := by
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinRightUnder T)
    (Iso.refl _)
  have h : (uliftYonedaEquiv.symm (ULift.up (𝟙 ⦋n⦌)) : Δ[n] ⟶ Δ[n]) = 𝟙 _ :=
    uliftYonedaEquiv.symm_apply_eq.2 rfl
  have h' : yonedaEquiv ((joinRightUnderAdjunction T).homEquiv _ _ g) = ULift.up g := by
    refine (Presheaf.uliftYonedaAdjunction_homEquiv_app _ _ g (ULift.up (𝟙 ⦋n⦌))).trans ?_
    rw [h]
    exact congrArg ULift.up ((Category.id_comp _).trans ((congrArg (· ≫ g)
      ((joinRightUnder T).map_id _)).trans (Category.id_comp g)))
  rw [h']
  rfl

private lemma homEquiv_homMk_sliceObjEquiv {T : SSet.{u}} {t : Under T} {n : ℕ}
    (σ : ((slice T).obj t) _⦋n⦌) :
    (joinRightUnderAdjunction T).homEquiv _ _
      (Under.homMk (sliceObjEquiv T t n σ).1 (sliceObjEquiv T t n σ).2) = yonedaEquiv.symm σ := by
  rw [Equiv.eq_symm_apply]
  refine (sliceObjEquiv T t n).injective ((sliceObjEquiv_yonedaEquiv_homEquiv _).trans ?_)
  rfl

private lemma homEquiv_symm_yonedaEquiv_symm_right {T : SSet.{u}} {t : Under T} {n : ℕ}
    (σ : ((slice T).obj t) _⦋n⦌) :
    (((joinRightUnderAdjunction T).homEquiv _ _).symm (yonedaEquiv.symm σ)).right =
      (sliceObjEquiv T t n σ).1 := by
  rw [← homEquiv_homMk_sliceObjEquiv, Equiv.symm_apply_apply]
  rfl

private lemma sliceObjEquiv_map_coe {T : SSet.{u}} {t : Under T} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ((slice T).obj t) _⦋n⦌) :
    (sliceObjEquiv T t m (((slice T).obj t).map θ.op σ)).1 =
      joinMap (stdSimplex.map θ) (𝟙 T) ≫ (sliceObjEquiv T t n σ).1 :=
  rfl

private noncomputable def sliceSectionSimplex {C : SSet.{u}} {c : C _⦋0⦌} {n : ℕ}
    (σ : (sliceAt C c) _⦋n⦌) : join Δ[n] Δ[0] ⟶ sliceAt C c :=
  (joinRightUnderAdjunction Δ[0]).homEquiv _ _
    (Under.homMk (mergeCone n ≫ (sliceObjEquiv _ _ n σ).1)
      ((joinInclRight_comp_mergeCone_assoc n _).trans (sliceObjEquiv _ _ n σ).2))

private lemma joinInclRight_comp_sliceSectionSimplex {C : SSet.{u}} {c : C _⦋0⦌} {n : ℕ}
    (σ : (sliceAt C c) _⦋n⦌) :
    joinInclRight Δ[n] Δ[0] ≫ sliceSectionSimplex σ = yonedaEquiv.symm (sliceId C c) := by
  rw [sliceSectionSimplex, ← Adjunction.homEquiv_naturality_left, sliceId,
    Equiv.symm_apply_apply]
  exact congrArg _ (Under.UnderMorphism.ext ((joinMap_joinInclRight_comp_mergeCone_assoc n _).trans
    (congrArg (_ ≫ ·) (sliceObjEquiv _ _ n σ).2)))

private noncomputable def sliceSectionObj {C : SSet.{u}} {c : C _⦋0⦌} (n : ℕ)
    (σ : (sliceAt C c) _⦋n⦌) : (sliceAt (sliceAt C c) (sliceId C c)) _⦋n⦌ :=
  (sliceObjEquiv _ _ n).symm ⟨sliceSectionSimplex σ, joinInclRight_comp_sliceSectionSimplex σ⟩

private lemma sliceObjEquiv_sliceSectionObj {C : SSet.{u}} {c : C _⦋0⦌} {n : ℕ}
    (σ : (sliceAt C c) _⦋n⦌) :
    (sliceObjEquiv _ _ n (sliceSectionObj n σ)).1 = sliceSectionSimplex σ := by
  rw [sliceSectionObj, Equiv.apply_symm_apply]

private lemma sliceSectionObj_map {C : SSet.{u}} {c : C _⦋0⦌} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (sliceAt C c) _⦋n⦌) :
    sliceSectionObj m ((sliceAt C c).map θ.op σ) =
      (sliceAt (sliceAt C c) (sliceId C c)).map θ.op (sliceSectionObj n σ) := by
  refine (sliceObjEquiv _ _ m).injective (Subtype.ext ?_)
  rw [sliceObjEquiv_sliceSectionObj, sliceObjEquiv_map_coe, sliceObjEquiv_sliceSectionObj,
    sliceSectionSimplex, sliceSectionSimplex, ← Adjunction.homEquiv_naturality_left]
  exact congrArg _ (Under.UnderMorphism.ext ((congrArg (mergeCone m ≫ ·)
    (sliceObjEquiv_map_coe θ σ)).trans (mergeCone_naturality_assoc θ _).symm))

private noncomputable def sliceSection (C : SSet.{u}) (c : C _⦋0⦌) :
    sliceAt C c ⟶ sliceAt (sliceAt C c) (sliceId C c) where
  app n := TypeCat.ofHom (sliceSectionObj n.unop.len)
  naturality n m f := by
    ext σ
    exact sliceSectionObj_map f.unop σ

private lemma sliceSection_comp_sliceAtπ (C : SSet.{u}) (c : C _⦋0⦌) :
    sliceSection C c ≫ sliceAtπ (sliceAt C c) (sliceId C c) = 𝟙 _ := by
  refine hom_ext_yonedaEquiv_symm fun n σ ↦ ?_
  rw [← Category.assoc, yonedaEquiv_symm_comp, comp_sliceAtπ,
    homEquiv_symm_yonedaEquiv_symm_right, Category.comp_id]
  refine ((congrArg (joinInclLeft Δ[n] Δ[0] ≫ ·) (sliceObjEquiv_sliceSectionObj σ)).trans
    ?_).trans (homEquiv_homMk_sliceObjEquiv σ)
  rw [sliceSectionSimplex, ← Adjunction.homEquiv_naturality_left]
  exact congrArg _ (Under.UnderMorphism.ext (joinMap_joinInclLeft_comp_mergeCone_assoc n _))

private lemma sliceObjEquiv_sliceId (C : SSet.{u}) (c : C _⦋0⦌) :
    (sliceObjEquiv _ _ 0 (sliceId C c)).1 =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm c := by
  rw [sliceId, sliceObjEquiv_yonedaEquiv_homEquiv]
  rfl

private lemma sliceId_comp_sliceSection (C : SSet.{u}) (c : C _⦋0⦌) :
    yonedaEquiv.symm (sliceId C c) ≫ sliceSection C c =
      yonedaEquiv.symm (sliceId (sliceAt C c) (sliceId C c)) := by
  rw [yonedaEquiv_symm_comp]
  refine congrArg _ ((sliceObjEquiv _ _ 0).injective (Subtype.ext ?_))
  refine (sliceObjEquiv_sliceSectionObj _).trans ?_
  have hid : yonedaEquiv.symm (sliceId C c) =
      (joinRightUnderAdjunction Δ[0]).homEquiv _ _ (degenerateEdge c) := by
    rw [sliceId, Equiv.symm_apply_apply]
  refine Eq.trans ?_ ((congrArg (_ ≫ ·) hid.symm).trans (sliceObjEquiv_sliceId _ _).symm)
  rw [sliceSectionSimplex, ← Adjunction.homEquiv_naturality_left]
  refine congrArg _ (Under.UnderMorphism.ext ((congrArg (mergeCone 0 ≫ ·)
    (sliceObjEquiv_sliceId C c)).trans ?_))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (stdSimplex.isTerminalObj₀.hom_ext _ _)).trans (Category.assoc _ _ _))

theorem rightAnodyneExtensions_sliceId (C : SSet.{u}) (c : C _⦋0⦌) :
    rightAnodyneExtensions (yonedaEquiv.symm (sliceId C c) : Δ[0] ⟶ sliceAt C c) :=
  rightAnodyneExtensions_of_section (sliceSection C c) (sliceSection_comp_sliceAtπ C c)
    (sliceId_comp_sliceSection C c)

theorem trivialFibration_mapOverRestrict_sliceId (C : SSet.{u}) (c : C _⦋0⦌) {G : SSet.{u}}
    {pG : G ⟶ C} (hp : rightFibrations pG) :
    modelCategoryQuillen.I.rlp
      (mapOverRestrict (yonedaEquiv.symm (sliceId C c)) (sliceAtπ C c) pG) :=
  trivialFibration_mapOverRestrict (rightAnodyneExtensions_sliceId C c) (sliceAtπ C c) hp

theorem hasLiftingProperty_sliceAtπ_iff {K L : SSet.{u}} (i : K ⟶ L) (X : SSet.{u})
    (ω : X _⦋0⦌)
    (sq : (Functor.curry.obj joinFunctor).PushoutObjObj i (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι) :
    HasLiftingProperty i (sliceAtπ X ω) ↔ ∀ u : sq.pt ⟶ X,
      joinInclRight K Δ[0] ≫ sq.inr ≫ u = yonedaEquiv.symm ω → ∃ v, sq.ι ≫ v = u := by
  let eL := @asIso _ _ _ _ (joinInclLeft L ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}))
    (isIso_joinInclLeft_of_isEmpty _ _)
  have hL : eL.hom ≫ joinMap (𝟙 L) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι = joinInclLeft L Δ[0] :=
    (joinInclLeft_comp_joinMap _ _).trans (Category.id_comp _)
  have hK : joinInclLeft K _ ≫ joinMap (𝟙 K) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι =
      joinInclLeft K Δ[0] :=
    (joinInclLeft_comp_joinMap _ _).trans (Category.id_comp _)
  have hR : joinInclRight K Δ[0] ≫ joinMap i (𝟙 Δ[0]) = joinInclRight L Δ[0] :=
    (joinInclRight_comp_joinMap _ _).trans (Category.id_comp _)
  constructor
  · intro h u hu
    let a := (joinRightUnderAdjunction Δ[0]).homEquiv _ _
      (Under.homMk (sq.inr ≫ u) hu : (joinRightUnder Δ[0]).obj K ⟶ Under.mk (yonedaEquiv.symm ω))
    have hw : a ≫ sliceAtπ X ω = i ≫ eL.hom ≫ sq.inl ≫ u := by
      rw [comp_sliceAtπ, Equiv.symm_apply_apply]
      exact ((congrArg (· ≫ sq.inr ≫ u) hK).symm.trans (Category.assoc _ _ _)).trans
        ((congrArg (joinInclLeft K _ ≫ ·) (sq.isPushout.w_assoc u).symm).trans
          (joinInclLeft_comp_joinMap_assoc i (𝟙 _) _))
    obtain ⟨l⟩ := (h.sq_hasLift ⟨hw⟩).exists_lift
    let v : join L Δ[0] ⟶ X := (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm l.l).right
    refine ⟨v, sq.isPushout.hom_ext ?_ ?_⟩
    · refine (sq.inl_ι_assoc v).trans ((cancel_epi eL.hom).1 ?_)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v) hL).trans
        ((comp_sliceAtπ l.l).symm.trans l.fac_right))
    · refine (sq.inr_ι_assoc v).trans ?_
      have := congrArg Under.Hom.right
        ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left_symm i l.l)
      rw [l.fac_left, Equiv.symm_apply_apply, Under.comp_right] at this
      exact this.symm
  · intro h
    refine ⟨fun {a b} sqab ↦ ?_⟩
    have : IsIso (joinInclLeft K ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})) :=
      isIso_joinInclLeft_of_isEmpty _ _
    let a' : join K Δ[0] ⟶ X := (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm a).right
    have hw : joinMap i (𝟙 _) ≫ eL.inv ≫ b =
        joinMap (𝟙 _) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι ≫ a' := by
      rw [← cancel_epi (joinInclLeft K _), joinInclLeft_comp_joinMap_assoc]
      refine (congrArg (i ≫ ·) (eL.hom_inv_id_assoc b)).trans ?_
      exact sqab.w.symm.trans ((comp_sliceAtπ a).trans ((joinInclLeft_comp_joinMap_assoc (𝟙 _) _
        a').trans (Category.id_comp _)).symm)
    have ha : joinInclRight K Δ[0] ≫ a' = yonedaEquiv.symm ω :=
      Under.w (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm a)
    obtain ⟨v, hv⟩ := h (sq.isPushout.desc (eL.inv ≫ b) a' hw)
      ((congrArg (joinInclRight K Δ[0] ≫ ·) (sq.isPushout.inr_desc _ _ _)).trans ha)
    have hinr : joinMap i (𝟙 Δ[0]) ≫ v = a' :=
      (congrArg (· ≫ v) sq.inr_ι.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg _ hv).trans (sq.isPushout.inr_desc _ _ _)))
    have hl : joinInclRight L Δ[0] ≫ v = yonedaEquiv.symm ω :=
      (congrArg (· ≫ v) hR.symm).trans ((Category.assoc _ _ _).trans ((congrArg _ hinr).trans ha))
    refine ⟨⟨⟨(joinRightUnderAdjunction Δ[0]).homEquiv _ _ (Under.homMk v hl), ?_, ?_⟩⟩⟩
    · rw [← Adjunction.homEquiv_naturality_left]
      exact (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm_apply_eq.1
        (Under.UnderMorphism.ext hinr).symm).symm
    · rw [comp_sliceAtπ, Equiv.symm_apply_apply]
      refine ((joinInclLeft_comp_joinMap_assoc (𝟙 L) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
        v).symm.trans ?_).trans (eL.hom_inv_id_assoc b)
      exact congrArg (joinInclLeft _ _ ≫ ·) ((congrArg (· ≫ v) ((Category.id_comp _).trans
        sq.inl_ι.symm)).trans ((Category.assoc _ _ _).trans ((congrArg _ hv).trans
          (sq.isPushout.inl_desc _ _ _))))

theorem rightFibrations_sliceAtπ (C : SSet.{u}) [C.Quasicategory] (c : C _⦋0⦌) :
    rightFibrations (sliceAtπ C c) := by
  rintro _ _ _ @⟨n, k, hk⟩
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj joinFunctor) Λ[n + 1, k].ι
    (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  refine (hasLiftingProperty_sliceAtπ_iff _ C c sq₀).2 fun u _ ↦ ?_
  have hu := innerAnodyneExtensions_pushoutObjObjι_join sq₀ (rightAnodyneExtensions.horn_ι hk)
    _ (mem_innerFibrations (terminal.from C))
  obtain ⟨l⟩ := (hu.sq_hasLift (⟨terminal.hom_ext _ _⟩ :
    CommSq u sq₀.ι (terminal.from C) (terminal.from _))).exists_lift
  exact ⟨l.l, l.fac_left⟩

theorem trivialFibration_mapOverSliceAt (C : SSet.{u}) [C.Quasicategory] (x y : C _⦋0⦌) :
    modelCategoryQuillen.I.rlp
      (mapOverRestrict (yonedaEquiv.symm (sliceId C x)) (sliceAtπ C x) (sliceAtπ C y) ≫
        eqToHom (by rw [sliceId_comp_sliceAtπ]) ≫ (mapOverVertexIso x (sliceAtπ C y)).hom) :=
  modelCategoryQuillen.I.rlp.comp_mem _ _
    (trivialFibration_mapOverRestrict_sliceId C x (rightFibrations_sliceAtπ C y))
    (modelCategoryQuillen.I.rlp.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
      (MorphismProperty.rlp_of_isIso _ _))

def IsFinal {X : SSet.{u}} (ω : X _⦋0⦌) : Prop :=
  rightAnodyneExtensions (yonedaEquiv.symm ω : Δ[0] ⟶ X)

theorem isFinal_iff {X : SSet.{u}} (ω : X _⦋0⦌) :
    IsFinal ω ↔ rightAnodyneExtensions (yonedaEquiv.symm ω : Δ[0] ⟶ X) :=
  Iff.rfl

theorem isFinal_iso_hom_app_iff {X Y : SSet.{u}} (e : X ≅ Y) (v : X _⦋0⦌) :
    IsFinal (e.hom.app _ v) ↔ IsFinal v := by
  have : yonedaEquiv.symm (e.hom.app _ v) = yonedaEquiv.symm v ≫ e.hom :=
    yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply])
  rw [isFinal_iff, isFinal_iff, this]
  exact MorphismProperty.cancel_right_of_respectsIso _ _ _

private lemma exists_homotopy_of_rightFibrations_of_section {E B : SSet.{u}} {p : E ⟶ B}
    (hp : rightFibrations p) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (hsa : rightAnodyneExtensions s) :
    ∃ H : E ⊗ Δ[1] ⟶ E, H ≫ p = fst E Δ[1] ≫ p ∧ ι₀ (X := E) ≫ H = 𝟙 E ∧
      ι₁ (X := E) ≫ H = p ≫ s := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) s (∂Δ[1]).ι
  have hu : s ▷ _ ≫ boundaryOneDesc (𝟙 E) (p ≫ s) = B ◁ (∂Δ[1]).ι ≫ fst B Δ[1] ≫ s := by
    rw [whiskerRight_boundaryOneDesc, Category.comp_id, ← Category.assoc s p s, hs,
      Category.id_comp, boundaryOneDesc_self, whiskerLeft_fst_assoc]
  let u := sq.isPushout.desc (boundaryOneDesc (𝟙 E) (p ≫ s)) (fst B Δ[1] ≫ s) hu
  have w : u ≫ p = sq.ι ≫ fst E Δ[1] ≫ p := by
    refine sq.isPushout.hom_ext ?_ ?_
    · rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc, boundaryOneDesc_comp, Category.id_comp,
        Category.assoc, hs, Category.comp_id, boundaryOneDesc_self]
      exact (whiskerLeft_fst_assoc _ _ _).symm
    · rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc]
      exact (Category.assoc _ _ _).trans (whiskerRight_fst_assoc s _ p).symm
  have hsq := rightAnodyneExtensions_pushoutObjObjι_left sq hsa p hp
  obtain ⟨l⟩ := (hsq.sq_hasLift (⟨w⟩ : CommSq u sq.ι p (fst E Δ[1] ≫ p))).exists_lift
  have h : sq.inl ≫ sq.ι ≫ l.l = boundaryOneDesc (𝟙 E) (p ≫ s) :=
    (congrArg (sq.inl ≫ ·) l.fac_left).trans (sq.isPushout.inl_desc _ _ _)
  rw [← Category.assoc, sq.inl_ι] at h
  exact ⟨l.l, l.fac_right, ι_comp_of_boundaryOneDesc h⟩

theorem trivialFibration_of_rightFibrations_of_section {E B : SSet.{u}} {p : E ⟶ B}
    (hp : rightFibrations p) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (hsa : rightAnodyneExtensions s) :
    modelCategoryQuillen.I.rlp p := by
  obtain ⟨H, hH, hH₀, hH₁⟩ := exists_homotopy_of_rightFibrations_of_section hp s hs hsa
  rintro _ _ _ ⟨n⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  let sq₂ := Subcomplex.unionProd.pushoutObjObj (∂Δ[n]) Λ[1, 1]
  have hu : (∂Δ[n]).ι ▷ _ ≫ fst _ _ ≫ b ≫ s = _ ◁ Λ[1, 1].ι ≫ a ▷ Δ[1] ≫ H := by
    rw [whisker_exchange_assoc, whiskerLeft_horn_comp hH₁, whiskerRight_fst_assoc,
      whiskerRight_fst_assoc, ← sq.w_assoc]
  let u := sq₂.isPushout.desc (fst _ _ ≫ b ≫ s) (a ▷ Δ[1] ≫ H) hu
  have w : u ≫ p = sq₂.ι ≫ fst _ _ ≫ b := by
    refine sq₂.isPushout.hom_ext ?_ ?_
    · rw [sq₂.isPushout.inl_desc_assoc, sq₂.inl_ι_assoc, Category.assoc, Category.assoc, hs,
        Category.comp_id]
      exact (whiskerLeft_fst_assoc _ _ _).symm
    · rw [sq₂.isPushout.inr_desc_assoc, sq₂.inr_ι_assoc, Category.assoc, hH,
        whiskerRight_fst_assoc, sq.w]
      exact (whiskerRight_fst_assoc _ _ _).symm
  have hsq := rightAnodyneExtensions_pushoutObjObjι sq₂
    (rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1)) p hp
  obtain ⟨l⟩ := (hsq.sq_hasLift (⟨w⟩ : CommSq u sq₂.ι p (fst _ _ ≫ b))).exists_lift
  refine ⟨⟨⟨ι₀ ≫ l.l, ?_, ?_⟩⟩⟩
  · rw [← ι₀_comp_assoc]
    exact (congrArg (ι₀ ≫ ·) ((sq₂.inr_ι_assoc l.l).symm.trans ((congrArg (sq₂.inr ≫ ·)
      l.fac_left).trans (sq₂.isPushout.inr_desc _ _ _)))).trans
        (by rw [ι₀_comp_assoc, hH₀, Category.comp_id])
  · rw [Category.assoc, l.fac_right, ι₀_fst_assoc]
def boundary.lastVertex (n : ℕ) : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩

private lemma boundary_join_sup_top_join_bot (n : ℕ) :
    (∂Δ[n]).join ⊤ ⊔ (⊤ : (Δ[n] : SSet.{u}).Subcomplex).join ⊥ =
      (∂Δ[n + 1]).preimage (stdSimplexJoinIso.{u} n 0).hom := by
  have h := boundary_join_sup_join_boundary.{u} n 0
  rwa [boundary_zero] at h

private noncomputable def boundaryInl (n : ℕ) :
    join Δ[n] ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subcomplex.lift (joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι ≫
    (stdSimplexJoinIso n 0).hom) (by
      rw [Subcomplex.range_comp, Subcomplex.image_le_iff, ← boundary_join_sup_top_join_bot]
      exact (range_joinMap_le (Subcomplex.topIso _).inv (𝟙 _) (Iso.inv_hom_id _)
        (Category.id_comp _)).trans le_sup_right)

private noncomputable def boundaryInr (n : ℕ) :
    join (∂Δ[n] : SSet.{u}) Δ[0] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subcomplex.lift (joinMap (∂Δ[n]).ι (𝟙 Δ[0]) ≫ (stdSimplexJoinIso n 0).hom) (by
      rw [Subcomplex.range_comp, Subcomplex.image_le_iff, ← boundary_join_sup_top_join_bot]
      exact (range_joinMap_le (𝟙 _) (Subcomplex.topIso _).inv (Category.id_comp _)
        (Iso.inv_hom_id _)).trans le_sup_left)

@[reassoc]
private lemma boundaryInl_ι (n : ℕ) :
    boundaryInl n ≫ (boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv =
      joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι := by
  rw [boundaryInl, Subcomplex.lift_ι_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
private lemma boundaryInr_ι (n : ℕ) :
    boundaryInr n ≫ (boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv =
      joinMap (∂Δ[n]).ι (𝟙 Δ[0]) := by
  rw [boundaryInr, Subcomplex.lift_ι_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma isPushout_boundaryInl_boundaryInr (n : ℕ) :
    IsPushout (joinMap (∂Δ[n]).ι (𝟙 _)) (joinMap (𝟙 _) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι)
      (boundaryInl n) (boundaryInr n) :=
  IsPushout.of_forall_isPushout_app fun k ↦ by
    have m₁ : Mono ((joinMap (𝟙 Δ[n]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).app k) :=
      (NatTrans.mono_iff_mono_app _).1 (mono_joinMap _ _) k
    have m₂ : Mono (((boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv).app k) :=
      (NatTrans.mono_iff_mono_app _).1 inferInstance k
    refine @Types.isPushout_of_isPullback_of_mono _ _ _ _ _ _ _ _ _
      (((boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv).app k) _ _
      ((isPullback_joinMap (∂Δ[n]).ι (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).flip.app k)
      ((NatTrans.comp_app _ _ _).symm.trans (congr_app (boundaryInl_ι n) k))
      ((NatTrans.comp_app _ _ _).symm.trans (congr_app (boundaryInr_ι n) k)) m₁ m₂ ?_
      (fun x y _ _ h ↦ (mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app _).1 (mono_joinMap (∂Δ[n]).ι (𝟙 Δ[0])) k) h)
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : (stdSimplexJoinIso.{u} n 0).inv.app k x.1 ∈
        ((∂Δ[n]).join ⊤ ⊔ (⊤ : (Δ[n] : SSet.{u}).Subcomplex).join ⊥).obj k := by
      rw [boundary_join_sup_top_join_bot]
      rw [Subcomplex.preimage_obj, Set.mem_preimage, ← NatTrans.comp_app_apply, Iso.inv_hom_id]
      exact x.2
    have hinv (y) (hy : y = (stdSimplexJoinIso.{u} n 0).inv.app k x.1) :
        (stdSimplexJoinIso.{u} n 0).hom.app k y = x.1 := by
      rw [hy, ← NatTrans.comp_app_apply, Iso.inv_hom_id]
      rfl
    obtain hx | hx := hx
    · obtain ⟨y, hy⟩ := range_joinMap_le (𝟙 _) (Subcomplex.topIso _).hom (Category.id_comp _)
        (Category.comp_id _) _ hx
      exact Or.inr ⟨y, Subtype.ext (hinv _ hy)⟩
    · obtain ⟨y, hy⟩ := range_joinMap_le (Subcomplex.topIso _).hom (𝟙 _) (Category.comp_id _)
        (Category.id_comp _) _ hx
      exact Or.inl ⟨y, Subtype.ext (hinv _ hy)⟩

private noncomputable def boundaryPushoutObjObj (n : ℕ) :
    (Functor.curry.obj joinFunctor).PushoutObjObj (∂Δ[n]).ι
      (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι where
  pt := ∂Δ[n + 1]
  inl := boundaryInl n
  inr := boundaryInr n
  isPushout := isPushout_boundaryInl_boundaryInr n
  ι := (boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv
  inl_ι := boundaryInl_ι n
  inr_ι := boundaryInr_ι n

private lemma joinInclRight_comp_boundaryInr (n : ℕ) :
    joinInclRight (∂Δ[n] : SSet.{u}) Δ[0] ≫ boundaryInr n =
      yonedaEquiv.symm (boundary.lastVertex n) := by
  rw [← cancel_mono (boundary.{u} (n + 1)).ι, Category.assoc, boundaryInr, Subcomplex.lift_ι,
    joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_stdSimplexJoinIso_hom]
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_map, yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine stdSimplex.ext _ _ fun i ↦ ?_
  refine Fin.ext ((congrArg Fin.val (AugmentedSimplexCategory.inr'_eval ⦋n⦌ ⦋0⦌ i)).trans ?_)
  have hi : (i : ℕ) = 0 := by omega
  change n + 1 + (i : ℕ) = n + 1
  omega

theorem trivialFibration_sliceAtπ_iff {X : SSet.{u}} (ω : X _⦋0⦌) :
    modelCategoryQuillen.I.rlp (sliceAtπ X ω) ↔
      ∀ (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X), b.app _ (boundary.lastVertex n) = ω →
        ∃ v : Δ[n + 1] ⟶ X, (∂Δ[n + 1]).ι ≫ v = b := by
  have hcone (n : ℕ) (b : (∂Δ[n + 1] : SSet.{u}) ⟶ X) :
      joinInclRight (∂Δ[n] : SSet.{u}) Δ[0] ≫ boundaryInr n ≫ b = yonedaEquiv.symm ω ↔
        b.app _ (boundary.lastVertex n) = ω := by
    rw [← Category.assoc, joinInclRight_comp_boundaryInr, yonedaEquiv_symm_comp,
      Equiv.apply_eq_iff_eq]
  refine ⟨fun h n b hb ↦ ?_, fun h _ _ _ ⟨n⟩ ↦ ?_⟩
  · obtain ⟨v, hv⟩ := (hasLiftingProperty_sliceAtπ_iff _ X ω (boundaryPushoutObjObj n)).1
      (h _ ⟨n⟩) b ((hcone n b).2 hb)
    exact ⟨(stdSimplexJoinIso n 0).inv ≫ v, (Category.assoc _ _ _).symm.trans hv⟩
  · refine (hasLiftingProperty_sliceAtπ_iff _ X ω (boundaryPushoutObjObj n)).2 fun u hu ↦ ?_
    obtain ⟨v, hv⟩ := h n u ((hcone n u).1 hu)
    refine ⟨(stdSimplexJoinIso n 0).hom ≫ v, ?_⟩
    change ((boundary.{u} (n + 1)).ι ≫ (stdSimplexJoinIso.{u} n 0).inv) ≫ _ ≫ v = u
    rw [Category.assoc, Iso.inv_hom_id_assoc, hv]

theorem trivialFibration_sliceAtπ_iff_trivialFibration_fiber {X : SSet.{u}} [X.Quasicategory]
    (ω : X _⦋0⦌) : modelCategoryQuillen.I.rlp (sliceAtπ X ω) ↔ ∀ x : X _⦋0⦌,
      modelCategoryQuillen.I.rlp (pullback.snd (sliceAtπ X ω) (yonedaEquiv.symm x)) :=
  ⟨fun h _ ↦ MorphismProperty.pullback_snd (P := modelCategoryQuillen.I.rlp) _ _ h,
    trivialFibration_of_rightFibrations_of_fiber (rightFibrations_sliceAtπ X ω)⟩

private lemma exists_section_of_hasLiftingProperty {X : SSet.{u}} {ω : X _⦋0⦌}
    (h : HasLiftingProperty (yonedaEquiv.symm ω : Δ[0] ⟶ X) (sliceAtπ X ω)) :
    ∃ s : X ⟶ sliceAt X ω, s ≫ sliceAtπ X ω = 𝟙 X ∧
      yonedaEquiv.symm ω ≫ s = yonedaEquiv.symm (sliceId X ω) := by
  obtain ⟨l⟩ := (h.sq_hasLift (⟨(sliceId_comp_sliceAtπ X ω).trans (Category.comp_id _).symm⟩ :
    CommSq (yonedaEquiv.symm (sliceId X ω)) (yonedaEquiv.symm ω) (sliceAtπ X ω)
      (𝟙 X))).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

theorem isFinal_of_trivialFibration_sliceAtπ {X : SSet.{u}} {ω : X _⦋0⦌}
    (h : modelCategoryQuillen.I.rlp (sliceAtπ X ω)) : IsFinal ω := by
  have : Mono (yonedaEquiv.symm ω : Δ[0] ⟶ X) := stdSimplex.isTerminalObj₀.mono_from _
  rw [← rlp_monomorphisms] at h
  obtain ⟨s, hs, hω⟩ := exists_section_of_hasLiftingProperty (h _ (monomorphisms.infer_property _))
  exact rightAnodyneExtensions_of_section s hs hω

theorem exists_section_of_isFinal {X : SSet.{u}} [X.Quasicategory] {ω : X _⦋0⦌}
    (h : IsFinal ω) : ∃ s : X ⟶ sliceAt X ω, s ≫ sliceAtπ X ω = 𝟙 X ∧
      yonedaEquiv.symm ω ≫ s = yonedaEquiv.symm (sliceId X ω) :=
  exists_section_of_hasLiftingProperty (h _ (rightFibrations_sliceAtπ X ω))

theorem isFinal_iff_exists_section {X : SSet.{u}} [X.Quasicategory] (ω : X _⦋0⦌) :
    IsFinal ω ↔ ∃ s : X ⟶ sliceAt X ω, s ≫ sliceAtπ X ω = 𝟙 X ∧
      yonedaEquiv.symm ω ≫ s = yonedaEquiv.symm (sliceId X ω) :=
  ⟨exists_section_of_isFinal, fun ⟨s, hs, hω⟩ ↦ rightAnodyneExtensions_of_section s hs hω⟩

theorem isFinal_const {X : SSet.{u}} [X.Quasicategory] {x : X _⦋0⦌} (h : IsFinal x)
    (A : SSet.{u}) : IsFinal ((MonoidalClosed.curry (snd A X)).app _ x) := by
  obtain ⟨s, hs, hx⟩ := exists_section_of_isFinal h
  obtain ⟨ht₁, ht₂⟩ := transpose_section hs hx
  let t : join X Δ[0] ⟶ X := (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm s).right
  have ht₃ : joinInclRight X Δ[0] ≫ t = yonedaEquiv.symm x :=
    Under.w (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm s)
  let c := (MonoidalClosed.curry (snd A X)).app _ x
  have hc : yonedaEquiv.symm c = MonoidalClosed.curry (snd A Δ[0] ≫ yonedaEquiv.symm x) := by
    rw [← yonedaEquiv_symm_comp, ← MonoidalClosed.curry_natural_left, whiskerLeft_snd]
  let T : join ((ihom A).obj X) Δ[0] ⟶ (ihom A).obj X := MonoidalClosed.curry
    (tensorJoinMap A _ Δ[0] ≫ joinMap ((ihom.ev A).app X) (𝟙 Δ[0]) ≫ t)
  have hT : joinInclRight _ Δ[0] ≫ T = yonedaEquiv.symm c := by
    rw [hc, ← MonoidalClosed.curry_natural_left]
    refine congrArg MonoidalClosed.curry
      ((whiskerLeft_joinInclRight_comp_tensorJoinMap_assoc A _ Δ[0] _).trans ?_)
    exact congrArg (snd A Δ[0] ≫ ·) ((joinInclRight_comp_joinMap_assoc _ _ _).trans
      ((Category.id_comp _).trans ht₃))
  refine rightAnodyneExtensions_of_section
    ((joinRightUnderAdjunction Δ[0]).homEquiv _ _ (Under.homMk T hT)) ?_ ?_
  · rw [comp_sliceAtπ, Equiv.symm_apply_apply]
    refine (MonoidalClosed.curry_natural_left _ _).symm.trans ?_
    rw [MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_id_eq_ev]
    refine (whiskerLeft_joinInclLeft_comp_tensorJoinMap_assoc A _ Δ[0] _).trans
      ((joinInclLeft_comp_joinMap_assoc _ _ _).trans ?_)
    exact (congrArg (_ ≫ ·) ht₁).trans (Category.comp_id _)
  · rw [← Adjunction.homEquiv_naturality_left, sliceId, Equiv.symm_apply_apply]
    refine congrArg _ (Under.UnderMorphism.ext ?_)
    change joinMap (yonedaEquiv.symm c) (𝟙 Δ[0]) ≫ T =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm c
    rw [hc]
    refine (MonoidalClosed.curry_natural_left _ _).symm.trans
      (Eq.trans ?_ (MonoidalClosed.curry_natural_left _ _))
    refine congrArg MonoidalClosed.curry
      ((whiskerLeft_joinMap_comp_tensorJoinMap_assoc A _ _ _).trans ?_)
    have hu : A ◁ MonoidalClosed.curry (snd A Δ[0] ≫ yonedaEquiv.symm x) ≫ (ihom.ev A).app X =
        snd A Δ[0] ≫ yonedaEquiv.symm x :=
      (MonoidalClosed.uncurry_eq _).symm.trans (MonoidalClosed.uncurry_curry _)
    have hj : joinMap (A ◁ MonoidalClosed.curry (snd A Δ[0] ≫ yonedaEquiv.symm x)) (𝟙 Δ[0]) ≫
        joinMap ((ihom.ev A).app X) (𝟙 Δ[0]) ≫ t =
          joinMap (snd A Δ[0]) (𝟙 Δ[0]) ≫ stdSimplex.isTerminalObj₀.from _ ≫
            yonedaEquiv.symm x := by
      rw [← joinMap_comp_id_assoc, hu, joinMap_comp_id_assoc, ht₂]
    refine (congrArg (tensorJoinMap A Δ[0] Δ[0] ≫ ·) hj).trans ?_
    simp only [← Category.assoc]
    exact congrArg (· ≫ yonedaEquiv.symm x) (stdSimplex.isTerminalObj₀.hom_ext _ _)

def finalSubcomplex (X : SSet.{u}) : X.Subcomplex where
  obj n := {σ | ∀ i : Fin (n.unop.len + 1),
    IsFinal (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op σ)}
  map {n m} θ σ hσ i := by
    have h := hσ (θ.unop.toOrderHom i)
    rwa [← SimplexCategory.const_comp, op_comp, Functor.map_comp_apply] at h

theorem mem_finalSubcomplex_iff {X : SSet.{u}} {n : ℕ} (σ : X _⦋n⦌) :
    σ ∈ (finalSubcomplex X).obj _ ↔
      ∀ i : Fin (n + 1), IsFinal (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ) :=
  Iff.rfl

theorem mem_finalSubcomplex_obj_zero_iff {X : SSet.{u}} (ω : X _⦋0⦌) :
    ω ∈ (finalSubcomplex X).obj _ ↔ IsFinal ω := by
  rw [mem_finalSubcomplex_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · have h0 := h 0
    rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0), op_id,
      Functor.map_id_apply] at h0
  · rwa [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ i), op_id,
      Functor.map_id_apply]

private lemma map_yonedaEquiv {Z : SSet.{u}} {m k : ℕ} (f : ⦋k⦌ ⟶ ⦋m⦌) (g : Δ[m] ⟶ Z) :
    Z.map f.op (yonedaEquiv g) = yonedaEquiv (stdSimplex.map f ≫ g) := by
  rw [yonedaEquiv_comp, yonedaEquiv_map]
  exact (NatTrans.naturality_apply g _ _).symm.trans
    (congrArg (g.app _) (stdSimplex.ext _ _ fun _ ↦ rfl))

private noncomputable abbrev sliceTranspose {X : SSet.{u}} {ω : X _⦋0⦌} {m : ℕ}
    (ℓ : Δ[m] ⟶ sliceAt X ω) : join Δ[m] Δ[0] ⟶ X :=
  (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm ℓ).right

noncomputable def sliceSimplex {X : SSet.{u}} {ω : X _⦋0⦌} {m : ℕ}
    (ℓ : Δ[m] ⟶ sliceAt X ω) : X _⦋m + 1⦌ :=
  yonedaEquiv ((stdSimplexJoinIso m 0).inv ≫ sliceTranspose ℓ)

private lemma inr'_zero_eq_δ_zero :
    AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌ = SimplexCategory.δ 0 := by
  ext i
  fin_cases i
  simp [AugmentedSimplexCategory.inr'_eval, SimplexCategory.δ]

lemma δ_last_sliceSimplex {X : SSet.{u}} {ω : X _⦋0⦌} {m : ℕ} (ℓ : Δ[m] ⟶ sliceAt X ω) :
    X.δ (Fin.last (m + 1)) (sliceSimplex ℓ) = yonedaEquiv (ℓ ≫ sliceAtπ X ω) := by
  have h : stdSimplex.map (SimplexCategory.δ (Fin.last (m + 1))) ≫ (stdSimplexJoinIso m 0).inv =
      joinInclLeft Δ[m] Δ[0] := by
    rw [← inl'_eq_δ_last, ← joinInclLeft_comp_stdSimplexJoinIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [SimplicialObject.δ, sliceSimplex, map_yonedaEquiv, ← Category.assoc, h, comp_sliceAtπ]

lemma δ_castSucc_sliceSimplex {X : SSet.{u}} {ω : X _⦋0⦌} {m : ℕ}
    (ℓ : Δ[m + 1] ⟶ sliceAt X ω) (j : Fin (m + 2)) :
    X.δ j.castSucc (sliceSimplex ℓ) = sliceSimplex (stdSimplex.δ j ≫ ℓ) := by
  have hθ : joinPointMap (SimplexCategory.δ j) = SimplexCategory.δ j.castSucc := by
    refine AugmentedSimplexCategory.tensorObj_hom_ext (x := .of ⦋m⦌) (y := .of ⦋0⦌)
      (z := .of ⦋m + 2⦌) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌ ≫ joinPointMap _ =
        AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌ ≫ SimplexCategory.δ j.castSucc
      rw [inl'_comp_joinPointMap, inl'_eq_δ_last, inl'_eq_δ_last]
      exact SimplexCategory.δ_comp_δ (Fin.le_last j)
    · change AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ joinPointMap _ =
        AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ SimplexCategory.δ j.castSucc
      rw [inr'_comp_joinPointMap]
      ext i
      fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
        Function.comp_apply, AugmentedSimplexCategory.inr'_eval, Fin.cast_eq_self,
        SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply, Fin.succAbove]
      rw [if_neg (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.natAdd]; omega)]
      rfl
  have h := joinMap_stdSimplexMap_comp_stdSimplexJoinIso (SimplexCategory.δ j)
  rw [hθ] at h
  have h' : (stdSimplexJoinIso m 0).inv ≫ joinMap (stdSimplex.δ j) (𝟙 Δ[0]) =
      stdSimplex.map (SimplexCategory.δ j.castSucc) ≫ (stdSimplexJoinIso (m + 1) 0).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have h'' : joinMap (stdSimplex.δ j) (𝟙 Δ[0]) ≫ sliceTranspose ℓ =
      sliceTranspose (stdSimplex.δ j ≫ ℓ) :=
    (congrArg Under.Hom.right
      ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left_symm (stdSimplex.δ j) ℓ)).symm
  rw [SimplicialObject.δ, sliceSimplex, sliceSimplex, map_yonedaEquiv, ← h'', ← Category.assoc,
    ← h', Category.assoc]

lemma δ_zero_sliceSimplex {X : SSet.{u}} {ω : X _⦋0⦌} (ℓ : Δ[0] ⟶ sliceAt X ω) :
    X.δ 0 (sliceSimplex ℓ) = ω := by
  have h : stdSimplex.map (SimplexCategory.δ 0) ≫ (stdSimplexJoinIso 0 0).inv =
      joinInclRight Δ[0] Δ[0] := by
    rw [← inr'_zero_eq_δ_zero, ← joinInclRight_comp_stdSimplexJoinIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hω : joinInclRight Δ[0] Δ[0] ≫ sliceTranspose ℓ = yonedaEquiv.symm ω :=
    Under.w (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm ℓ)
  rw [SimplicialObject.δ, sliceSimplex, map_yonedaEquiv, ← Category.assoc, h, hω,
    Equiv.apply_symm_apply]

lemma sliceSimplex_sliceId (X : SSet.{u}) (ω : X _⦋0⦌) :
    sliceSimplex (yonedaEquiv.symm (sliceId X ω)) = X.σ 0 ω := by
  have h : sliceTranspose (yonedaEquiv.symm (sliceId X ω)) =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm ω := by
    rw [sliceTranspose, sliceId, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  rw [sliceSimplex, h, ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _)
    (stdSimplex.map (SimplexCategory.σ 0)), ← map_yonedaEquiv, Equiv.apply_symm_apply]
  rfl

private lemma stdSimplex_map_comp_yonedaEquiv_symm {Z : SSet.{u}} {m k : ℕ} (f : ⦋k⦌ ⟶ ⦋m⦌)
    (z : Z _⦋m⦌) : stdSimplex.map f ≫ yonedaEquiv.symm z = yonedaEquiv.symm (Z.map f.op z) :=
  yonedaEquiv.injective (((map_yonedaEquiv f _).symm.trans
    (congrArg _ (Equiv.apply_symm_apply _ _))).trans (Equiv.apply_symm_apply _ _).symm)

private lemma exists_boundaryOne_hom {Z : SSet.{u}} (z₀ z₁ : Z _⦋0⦌) :
    ∃ a : (∂Δ[1] : SSet.{u}) ⟶ Z, boundary.ι 1 ≫ a = yonedaEquiv.symm z₀ ∧
      boundary.ι 0 ≫ a = yonedaEquiv.symm z₁ := by
  have hpt (y : (Δ[0] : SSet.{u}) _⦋0⦌) (z : Z _⦋0⦌) : (yonedaEquiv.symm z).app _ y = z := by
    obtain rfl : y = yonedaEquiv (𝟙 _) :=
      stdSimplex.obj₀Equiv.injective ((Fin.eq_zero _).trans (Fin.eq_zero _).symm)
    rw [← yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  refine ⟨lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _) ≫
    boundaryOneDesc (yonedaEquiv.symm z₀) (yonedaEquiv.symm z₁), yonedaEquiv.injective ?_,
    yonedaEquiv.injective ?_⟩
  · rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine (boundaryOneDesc_app (yonedaEquiv.symm z₀) (yonedaEquiv.symm z₁) _
      ((lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _)).app _ (yonedaEquiv (boundary.ι 1)))).trans ?_
    exact (if_pos rfl).trans (hpt _ _)
  · rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine (boundaryOneDesc_app (yonedaEquiv.symm z₀) (yonedaEquiv.symm z₁) _
      ((lift (stdSimplex.isTerminalObj₀.from _) (𝟙 _)).app _ (yonedaEquiv (boundary.ι 0)))).trans ?_
    exact (if_neg (fun h ↦ absurd h (by decide) : ¬ (1 : Fin 2) = 0)).trans (hpt _ _)

private noncomputable def sliceVertex {X : SSet.{u}} {x ω : X _⦋0⦌} (e : Edge x ω) :
    (sliceAt X ω) _⦋0⦌ :=
  yonedaEquiv ((joinRightUnderAdjunction Δ[0]).homEquiv _ _
    (Under.homMk ((stdSimplexJoinIso 0 0).hom ≫ yonedaEquiv.symm e.edge) (by
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yonedaEquiv.symm e.edge)
        ((joinInclRight_comp_stdSimplexJoinIso_hom 0 0).trans
          (congrArg stdSimplex.map inr'_zero_eq_δ_zero)))).trans
        ((stdSimplex_map_comp_yonedaEquiv_symm _ _).trans (congrArg yonedaEquiv.symm e.tgt_eq))) :
      (joinRightUnder Δ[0]).obj Δ[0] ⟶ Under.mk (yonedaEquiv.symm ω)))

private lemma sliceSimplex_sliceVertex {X : SSet.{u}} {x ω : X _⦋0⦌} (e : Edge x ω) :
    sliceSimplex (yonedaEquiv.symm (sliceVertex e)) = e.edge := by
  rw [sliceSimplex, sliceTranspose, sliceVertex, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact (congrArg yonedaEquiv (Iso.inv_hom_id_assoc _ _)).trans (Equiv.apply_symm_apply _ _)

private lemma sliceVertex_comp_sliceAtπ {X : SSet.{u}} {x ω : X _⦋0⦌} (e : Edge x ω) :
    yonedaEquiv.symm (sliceVertex e) ≫ sliceAtπ X ω = yonedaEquiv.symm x := by
  rw [comp_sliceAtπ, sliceVertex, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yonedaEquiv.symm e.edge)
    ((joinInclLeft_comp_stdSimplexJoinIso_hom 0 0).trans
      (congrArg stdSimplex.map (inl'_eq_δ_last 0))))).trans
    ((stdSimplex_map_comp_yonedaEquiv_symm _ _).trans (congrArg yonedaEquiv.symm e.src_eq))

private lemma nonempty_compStruct_of_rlp {X : SSet.{u}} {ω : X _⦋0⦌}
    (h : (monomorphisms SSet.{u}).rlp (sliceAtπ X ω)) {x : X _⦋0⦌} (f g : Edge x ω) :
    Nonempty (Edge.CompStruct f (Edge.id ω) g) := by
  obtain ⟨a, ha₁, ha₀⟩ := exists_boundaryOne_hom (sliceVertex g) (sliceId X ω)
  have w : a ≫ sliceAtπ X ω = (∂Δ[1]).ι ≫ yonedaEquiv.symm f.edge := by
    refine boundary.hom_ext fun i ↦ ?_
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sliceAtπ X ω) ha₀).trans
        ((sliceId_comp_sliceAtπ X ω).trans ((congrArg yonedaEquiv.symm f.tgt_eq.symm).trans
          ((stdSimplex_map_comp_yonedaEquiv_symm _ _).symm.trans
            (boundary.ι_ι_assoc _ _).symm))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sliceAtπ X ω) ha₁).trans
        ((sliceVertex_comp_sliceAtπ g).trans ((congrArg yonedaEquiv.symm f.src_eq.symm).trans
          ((stdSimplex_map_comp_yonedaEquiv_symm _ _).symm.trans
            (boundary.ι_ι_assoc _ _).symm))))
  obtain ⟨l⟩ := ((h _ (monomorphisms.infer_property (∂Δ[1]).ι)).sq_hasLift ⟨w⟩).exists_lift
  have hδ (i : Fin 2) : stdSimplex.δ i ≫ l.l = boundary.ι i ≫ a := by
    rw [← boundary.ι_ι_assoc, l.fac_left]
  refine ⟨Edge.CompStruct.mk (sliceSimplex l.l) ?_ ?_ ?_⟩
  · exact (δ_last_sliceSimplex l.l).trans ((congrArg yonedaEquiv l.fac_right).trans
      (Equiv.apply_symm_apply _ _))
  · exact (δ_castSucc_sliceSimplex l.l 0).trans ((congrArg sliceSimplex ((hδ 0).trans ha₀)).trans
      (sliceSimplex_sliceId X ω))
  · exact (δ_castSucc_sliceSimplex l.l 1).trans ((congrArg sliceSimplex ((hδ 1).trans ha₁)).trans
      (sliceSimplex_sliceVertex g))

noncomputable def isTerminalOfTrivialFibrationSliceAtπ {X : SSet.{u}} [X.Quasicategory]
    {ω : X _⦋0⦌} (h : modelCategoryQuillen.I.rlp (sliceAtπ X ω)) :
    IsTerminal (Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) ω) := by
  rw [← rlp_monomorphisms] at h
  have hne (a : Truncated.HomotopyCategory ((truncation 2).obj X)) :
      Nonempty (a ⟶ Truncated.HomotopyCategory.mk ω) := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    have : Mono (yonedaEquiv.symm ω : Δ[0] ⟶ X) := stdSimplex.isTerminalObj₀.mono_from _
    obtain ⟨s, hs, -⟩ := exists_section_of_hasLiftingProperty (h _ (monomorphisms.infer_property _))
    let ℓ : Δ[0] ⟶ sliceAt X ω := yonedaEquiv.symm x ≫ s
    have hx : X.δ 1 (sliceSimplex ℓ) = x := (δ_last_sliceSimplex ℓ).trans
      ((congrArg yonedaEquiv (by rw [Category.assoc, hs, Category.comp_id]; rfl)).trans
        (Equiv.apply_symm_apply _ x))
    exact ⟨Truncated.HomotopyCategory.homMk
      (Edge.mk (sliceSimplex ℓ) hx (δ_zero_sliceSimplex ℓ)).toTruncated⟩
  have hsub (a : Truncated.HomotopyCategory ((truncation 2).obj X))
      (f g : a ⟶ Truncated.HomotopyCategory.mk ω) : f = g := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective f
    obtain ⟨e', rfl⟩ := Truncated.HomotopyCategory.homMk_surjective g
    obtain ⟨c⟩ := nonempty_compStruct_of_rlp h (Edge.ofTruncated e) (Edge.ofTruncated e')
    exact (Truncated.HomotopyCategory.homMk_eq_homMk_iff e e').2 ⟨c.toTruncated⟩
  exact IsTerminal.ofUniqueHom (fun a ↦ (hne a).some) (fun a m ↦ hsub a _ _)

section Restriction

variable {K X : SSet.{u}}

noncomputable def sliceIsoOfEq {a b : K ⟶ X} (h : a = b) :
    (slice K).obj (Under.mk a) ≅ (slice K).obj (Under.mk b) :=
  (slice K).mapIso (Under.isoMk (Iso.refl X) ((Category.comp_id _).trans h))

@[reassoc]
theorem sliceIsoOfEq_hom_sliceπ {a b : K ⟶ X} (h : a = b) :
    (sliceIsoOfEq h).hom ≫ sliceπ (Under.mk b) = sliceπ (Under.mk a) :=
  (slice_map_sliceπ (Under.isoMk (Iso.refl X) ((Category.comp_id _).trans h) :
    Under.mk a ≅ Under.mk b).hom).trans (Category.comp_id _)

noncomputable def sliceToSliceAt (d : K ⟶ X) (k : Δ[0] ⟶ K) {z : X _⦋0⦌}
    (hz : k ≫ d = yonedaEquiv.symm z) : (slice K).obj (Under.mk d) ⟶ sliceAt X z :=
  sliceRes k (Under.mk d) ≫ (sliceIsoOfEq hz).hom

@[reassoc]
theorem sliceToSliceAt_comp_sliceAtπ (d : K ⟶ X) (k : Δ[0] ⟶ K) {z : X _⦋0⦌}
    (hz : k ≫ d = yonedaEquiv.symm z) :
    sliceToSliceAt d k hz ≫ sliceAtπ X z = sliceπ (Under.mk d) :=
  (Category.assoc _ _ _).trans ((congrArg (sliceRes k (Under.mk d) ≫ ·)
    (sliceIsoOfEq_hom_sliceπ hz)).trans (sliceRes_sliceπ k (Under.mk d)))

theorem sliceAtπ_app_sliceToSliceAt_app (d : K ⟶ X) (k : Δ[0] ⟶ K) {z : X _⦋0⦌}
    (hz : k ≫ d = yonedaEquiv.symm z) (c : ((slice K).obj (Under.mk d)) _⦋0⦌) :
    (sliceAtπ X z).app _ ((sliceToSliceAt d k hz).app _ c) = (sliceπ (Under.mk d)).app _ c :=
  congrArg (fun f ↦ f.app _ c) (sliceToSliceAt_comp_sliceAtπ d k hz)

end Restriction

end SSet
