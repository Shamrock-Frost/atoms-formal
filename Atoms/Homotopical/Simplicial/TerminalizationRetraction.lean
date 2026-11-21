import Atoms.Homotopical.Simplicial.Cartesian
import Atoms.Homotopical.Simplicial.Terminalization

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace SSet

section Merge

open AugmentedSimplexCategory Opposite MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.DayConvolution

private abbrev coneHom {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) : ⦋n + 0 + 1⦌ ⟶ ⦋m + 0 + 1⦌ :=
  WithInitial.down (inclusion.map f ⊗ₘ inclusion.map (𝟙 ⦋0⦌))

private theorem coneHom_apply_castSucc {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    ((coneHom f).toOrderHom i.castSucc).val = (f.toOrderHom i).val :=
  val_toFun_tensorHom_of_lt (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋m⦌)
    (inclusion.map f) (inclusion.map (𝟙 ⦋0⦌)) (x₂ := WithInitial.of ⦋0⦌) i.castSucc
    (by simp only [card, Fin.val_castSucc]; omega)

private theorem coneHom_apply_last {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    ((coneHom f).toOrderHom (Fin.last _)).val = m + 1 := by
  refine (val_toFun_tensorHom_of_le (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋m⦌)
    (inclusion.map f) (inclusion.map (𝟙 ⦋0⦌)) (x₂ := WithInitial.of ⦋0⦌) (Fin.last _)
    (by simp [card])).trans ?_
  change m + 1 + ((Fin.last (n + 0 + 1)).val - (n + 1)) = m + 1
  simp

private theorem val_σ_last_apply (n : ℕ) (x : Fin (n + 2)) :
    ((SimplexCategory.σ (Fin.last n)).toOrderHom x).val = min x.val n := by
  change (Fin.predAbove (Fin.last n) x).val = min x.val n
  rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl
  · rw [Fin.predAbove_last_castSucc, Fin.val_castSucc]
    exact (min_eq_left (Nat.le_of_lt_succ y.isLt)).symm
  · rw [Fin.predAbove_right_last]
    simp

private theorem coneHom_inl'_comp_σ_last (n : ℕ) :
    (coneHom (inl' ⦋n⦌ ⦋0⦌) ≫ SimplexCategory.σ (Fin.last (n + 0 + 1)) :
      ⦋n + 0 + 1⦌ ⟶ ⦋n + 0 + 1⦌) = 𝟙 _ := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  change ((SimplexCategory.σ _).toOrderHom ((coneHom _).toOrderHom i)).val = i.val
  rw [val_σ_last_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [coneHom_apply_castSucc, inl'_eval]
    simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc]
    omega
  · rw [coneHom_apply_last]
    simp

private theorem coneHom_inr'_comp_σ_last (n : ℕ) :
    (coneHom (inr' ⦋n⦌ ⦋0⦌) ≫ SimplexCategory.σ (Fin.last (n + 0 + 1)) :
      ⦋0 + 0 + 1⦌ ⟶ ⦋n + 0 + 1⦌) = SimplexCategory.σ 0 ≫ inr' ⦋n⦌ ⦋0⦌ := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  change ((SimplexCategory.σ _).toOrderHom ((coneHom _).toOrderHom i)).val =
    ((inr' ⦋n⦌ ⦋0⦌).toOrderHom ((SimplexCategory.σ 0).toOrderHom i)).val
  rw [val_σ_last_apply, inr'_eval]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [coneHom_apply_castSucc, inr'_eval]
    simp
  · rw [coneHom_apply_last]
    simp

private theorem coneHom_coneHom_comp_σ_last {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (coneHom (coneHom f) ≫ SimplexCategory.σ (Fin.last (m + 0 + 1)) :
      ⦋n + 0 + 1 + 0 + 1⦌ ⟶ ⦋m + 0 + 1⦌) =
        SimplexCategory.σ (Fin.last (n + 0 + 1)) ≫ coneHom f := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  change ((SimplexCategory.σ _).toOrderHom ((coneHom _).toOrderHom i)).val =
    ((coneHom f).toOrderHom ((SimplexCategory.σ _).toOrderHom i)).val
  rw [val_σ_last_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [coneHom_apply_castSucc]
    change min ((coneHom f).toOrderHom j).val (m + 0 + 1) =
      ((coneHom f).toOrderHom (Fin.predAbove (Fin.last _) j.castSucc)).val
    rw [Fin.predAbove_last_castSucc]
    exact min_eq_left (Nat.le_of_lt_succ ((coneHom f).toOrderHom j).isLt)
  · rw [coneHom_apply_last]
    change min (m + 0 + 1 + 1) (m + 0 + 1) =
      ((coneHom f).toOrderHom (Fin.predAbove (Fin.last _) (Fin.last _))).val
    rw [Fin.predAbove_right_last, coneHom_apply_last]
    simp

private noncomputable def mergeStd (n : ℕ) :
    join (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ⟶ join (Δ[n] : SSet.{u}) Δ[0] :=
  joinMap (stdSimplexJoinIso n 0).hom (𝟙 Δ[0]) ≫ (stdSimplexJoinIso (n + 0 + 1) 0).hom ≫
    stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) ≫ (stdSimplexJoinIso n 0).inv

private theorem joinInclLeft_comp_mergeStd (n : ℕ) :
    joinInclLeft (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ≫ mergeStd n = 𝟙 _ := by
  rw [mergeStd, joinInclLeft_comp_joinMap_assoc,
    reassoc_of% (joinInclLeft_comp_stdSimplexJoinIso_hom.{u} (n + 0 + 1) 0)]
  have h : stdSimplex.map (inl' ⦋n + 0 + 1⦌ ⦋0⦌) ≫
      stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) = 𝟙 (Δ[n + 0 + 1] : SSet.{u}) :=
    (stdSimplex.map_comp _ _).symm.trans ((congrArg stdSimplex.map (inl'_comp_σ_last _)).trans
      (stdSimplex.map_id _))
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h).trans (Category.id_comp _)))).trans (Iso.hom_inv_id _)

private theorem joinMap_stdSimplex_map_comp_hom {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    joinMap (stdSimplex.map f) (𝟙 Δ[0]) ≫ (stdSimplexJoinIso.{u} m 0).hom =
      (stdSimplexJoinIso n 0).hom ≫ stdSimplex.map (coneHom f) := by
  exact (congrArg (fun g ↦ joinMap (stdSimplex.map f) g ≫ (stdSimplexJoinIso.{u} m 0).hom)
    (stdSimplex.map_id ⦋0⦌)).symm.trans
      (joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom f (𝟙 ⦋0⦌))

private theorem joinMap_joinInclLeft_comp_mergeStd (n : ℕ) :
    joinMap (joinInclLeft (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫ mergeStd n = 𝟙 _ := by
  have h₁ : joinMap (joinInclLeft (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫
      joinMap (stdSimplexJoinIso n 0).hom (𝟙 Δ[0]) =
        joinMap (stdSimplex.map (inl' ⦋n⦌ ⦋0⦌)) (𝟙 Δ[0]) :=
    (joinMap_comp_joinMap_id _ _ _).trans
      (congrArg (fun g ↦ joinMap g (𝟙 Δ[0])) (joinInclLeft_comp_stdSimplexJoinIso_hom n 0))
  have h₂ : joinMap (stdSimplex.map (inl' ⦋n⦌ ⦋0⦌)) (𝟙 Δ[0]) ≫
      (stdSimplexJoinIso.{u} (n + 0 + 1) 0).hom =
        (stdSimplexJoinIso n 0).hom ≫ stdSimplex.map (coneHom (inl' ⦋n⦌ ⦋0⦌)) :=
    joinMap_stdSimplex_map_comp_hom _
  have h₃ : stdSimplex.map (coneHom (inl' ⦋n⦌ ⦋0⦌)) ≫
      stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) =
        𝟙 (Δ[n + 0 + 1] : SSet.{u}) :=
    (stdSimplex.map_comp _ _).symm.trans
      ((congrArg stdSimplex.map (coneHom_inl'_comp_σ_last n)).trans (stdSimplex.map_id _))
  rw [mergeStd, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, Iso.hom_inv_id]

private theorem joinInclRight_comp_mergeStd (n : ℕ) :
    joinInclRight (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ≫ mergeStd n = joinInclRight _ Δ[0] := by
  have h : stdSimplex.map (inr' ⦋n + 0 + 1⦌ ⦋0⦌) ≫
      stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) =
        (stdSimplex.map (inr' ⦋n⦌ ⦋0⦌) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 0 + 1]) :=
    (stdSimplex.map_comp _ _).symm.trans (congrArg stdSimplex.map (inr'_comp_σ_last n))
  rw [mergeStd, joinInclRight_comp_joinMap_assoc, Category.id_comp,
    reassoc_of% (joinInclRight_comp_stdSimplexJoinIso_hom.{u} (n + 0 + 1) 0), reassoc_of% h,
    ← joinInclRight_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem joinMap_joinInclRight_comp_mergeStd (n : ℕ) :
    joinMap (joinInclRight (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫ mergeStd n =
      stdSimplex.isTerminalObj₀.from _ ≫ joinInclRight _ Δ[0] := by
  have h₁ : joinMap (joinInclRight (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫
      joinMap (stdSimplexJoinIso n 0).hom (𝟙 Δ[0]) =
        joinMap (stdSimplex.map (inr' ⦋n⦌ ⦋0⦌)) (𝟙 Δ[0]) :=
    (joinMap_comp_joinMap_id _ _ _).trans
      (congrArg (fun g ↦ joinMap g (𝟙 Δ[0])) (joinInclRight_comp_stdSimplexJoinIso_hom n 0))
  have h₂ : joinMap (stdSimplex.map (inr' ⦋n⦌ ⦋0⦌)) (𝟙 Δ[0]) ≫
      (stdSimplexJoinIso.{u} (n + 0 + 1) 0).hom =
        (stdSimplexJoinIso 0 0).hom ≫ stdSimplex.map (coneHom (inr' ⦋n⦌ ⦋0⦌)) :=
    joinMap_stdSimplex_map_comp_hom _
  have h₃ : stdSimplex.map (coneHom (inr' ⦋n⦌ ⦋0⦌)) ≫
      stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) =
        (stdSimplex.map (SimplexCategory.σ 0) ≫ stdSimplex.map (inr' ⦋n⦌ ⦋0⦌) :
          (Δ[0 + 0 + 1] : SSet.{u}) ⟶ Δ[n + 0 + 1]) :=
    (stdSimplex.map_comp _ _).symm.trans ((congrArg stdSimplex.map
      (coneHom_inr'_comp_σ_last n)).trans (stdSimplex.map_comp _ _))
  have h₄ : (stdSimplexJoinIso.{u} 0 0).hom ≫ stdSimplex.map (SimplexCategory.σ 0) =
      stdSimplex.isTerminalObj₀.from _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [mergeStd, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄,
    ← joinInclRight_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem joinMap_joinMap_comp_mergeStd {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    joinMap (joinMap (stdSimplex.map f) (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ mergeStd.{u} m =
      mergeStd n ≫ joinMap (stdSimplex.map f) (𝟙 Δ[0]) := by
  have h₁ : joinMap (joinMap (stdSimplex.map f) (𝟙 Δ[0])) (𝟙 Δ[0]) ≫
      joinMap (stdSimplexJoinIso m 0).hom (𝟙 Δ[0]) =
        joinMap (stdSimplexJoinIso.{u} n 0).hom (𝟙 Δ[0]) ≫
          joinMap (stdSimplex.map (coneHom f)) (𝟙 Δ[0]) :=
    (joinMap_comp_joinMap_id _ _ _).trans ((congrArg (fun g ↦ joinMap g (𝟙 Δ[0]))
      (joinMap_stdSimplex_map_comp_hom f)).trans (joinMap_comp_joinMap_id _ _ _).symm)
  have h₂ : joinMap (stdSimplex.map (coneHom f)) (𝟙 Δ[0]) ≫
      (stdSimplexJoinIso.{u} (m + 0 + 1) 0).hom =
        (stdSimplexJoinIso (n + 0 + 1) 0).hom ≫ stdSimplex.map (coneHom (coneHom f)) :=
    joinMap_stdSimplex_map_comp_hom _
  have h₃ : stdSimplex.map (coneHom (coneHom f)) ≫
      stdSimplex.map (SimplexCategory.σ (Fin.last (m + 0 + 1))) =
        (stdSimplex.map (SimplexCategory.σ (Fin.last (n + 0 + 1))) ≫
          stdSimplex.map (coneHom f) : (Δ[n + 0 + 1 + 0 + 1] : SSet.{u}) ⟶ Δ[m + 0 + 1]) :=
    (stdSimplex.map_comp _ _).symm.trans ((congrArg stdSimplex.map
      (coneHom_coneHom_comp_σ_last f)).trans (stdSimplex.map_comp _ _))
  have h₄ : (stdSimplexJoinIso.{u} n 0).inv ≫ joinMap (stdSimplex.map f) (𝟙 Δ[0]) =
      stdSimplex.map (coneHom f) ≫ (stdSimplexJoinIso m 0).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← joinMap_stdSimplex_map_comp_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [mergeStd, mergeStd, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, Category.assoc,
    Category.assoc, Category.assoc, h₄]

private noncomputable def mergeStdUnder (n : ℕ) :
    (joinRightUnder Δ[0]).obj (join (Δ[n] : SSet.{u}) Δ[0]) ⟶ (joinRightUnder Δ[0]).obj Δ[n] :=
  Under.homMk (mergeStd n) (joinInclRight_comp_mergeStd n)

private noncomputable def constUnder (X : Under (Δ[0] : SSet.{u})) :
    (joinRightUnder Δ[0]).obj Δ[0] ⟶ X :=
  Under.homMk (stdSimplex.isTerminalObj₀.from _ ≫ X.hom)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom)
      (stdSimplex.isTerminalObj₀.hom_ext _ (𝟙 _))).trans (Category.id_comp _)))

private noncomputable def idVertex (X : Under (Δ[0] : SSet.{u})) :
    Δ[0] ⟶ (slice Δ[0]).obj X :=
  (joinRightUnderAdjunction Δ[0]).homEquiv _ _ (constUnder X)

private noncomputable def pointedSlice : Under (Δ[0] : SSet.{u}) ⥤ Under (Δ[0] : SSet.{u}) where
  obj X := Under.mk (idVertex X)
  map {X Y} g := Under.homMk ((slice Δ[0]).map g) (by
    refine ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_right _ _).symm.trans ?_
    exact congrArg _ (Under.UnderMorphism.ext ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Under.w g)))))
  map_id X := Under.UnderMorphism.ext ((slice Δ[0]).map_id X)
  map_comp f g := Under.UnderMorphism.ext ((slice Δ[0]).map_comp f g)

private noncomputable def sliceProj (X : Under (Δ[0] : SSet.{u})) :
    (slice Δ[0]).obj X ⟶ X.right :=
  joinInclLeft _ Δ[0] ≫ ((joinRightUnderAdjunction Δ[0]).counit.app X).right

private theorem slice_map_comp_sliceProj {X Y : Under (Δ[0] : SSet.{u})} (g : X ⟶ Y) :
    (slice Δ[0]).map g ≫ sliceProj Y = sliceProj X ≫ g.right := by
  have h := congrArg Under.Hom.right ((joinRightUnderAdjunction Δ[0]).counit.naturality g)
  rw [Under.comp_right, Under.comp_right] at h
  exact (joinInclLeft_comp_joinMap_assoc ((slice Δ[0]).map g) (𝟙 Δ[0]) _).symm.trans
    ((congrArg (joinInclLeft _ Δ[0] ≫ ·) h).trans (Category.assoc _ _ _).symm)

private theorem homEquiv_comp_sliceProj {K : SSet.{u}} {X : Under (Δ[0] : SSet.{u})}
    (f : (joinRightUnder Δ[0]).obj K ⟶ X) :
    (joinRightUnderAdjunction Δ[0]).homEquiv _ _ f ≫ sliceProj X =
      joinInclLeft K Δ[0] ≫ f.right := by
  let adj := joinRightUnderAdjunction (Δ[0] : SSet.{u})
  have h₁ := slice_map_comp_sliceProj f
  have h₂ : adj.unit.app K ≫ sliceProj ((joinRightUnder Δ[0]).obj K) = joinInclLeft K Δ[0] := by
    have h := congrArg Under.Hom.right (adj.left_triangle_components K)
    rw [Under.comp_right, Under.id_right] at h
    exact (joinInclLeft_comp_joinMap_assoc (adj.unit.app K) (𝟙 Δ[0]) _).symm.trans
      ((congrArg (joinInclLeft K Δ[0] ≫ ·) h).trans (Category.comp_id _))
  rw [Adjunction.homEquiv_unit, Category.assoc, h₁, reassoc_of% h₂]
  rfl

private noncomputable def sliceProjNat : pointedSlice ⟶ 𝟭 (Under (Δ[0] : SSet.{u})) where
  app X := Under.homMk (sliceProj X) ((homEquiv_comp_sliceProj (constUnder X)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom)
      (stdSimplex.isTerminalObj₀.hom_ext _ (𝟙 _))).trans (Category.id_comp _))))
  naturality _ _ g := Under.UnderMorphism.ext (slice_map_comp_sliceProj g)

private instance isLeftKanExtension_joinRightUnder :
    (joinRightUnder (Δ[0] : SSet.{u})).IsLeftKanExtension
      (Iso.refl (uliftYoneda.{u} ⋙ joinRightUnder (Δ[0] : SSet.{u}))).hom :=
  have : PreservesColimitsOfSize.{0, u} (joinRightUnder (Δ[0] : SSet.{u})) :=
    preservesColimitsOfSize_shrink _
  Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} _ (Iso.refl _)

private noncomputable def mergeRestriction :
    uliftYoneda.{u} ⋙ joinRightUnder (Δ[0] : SSet.{u}) ⟶
      uliftYoneda.{u} ⋙ joinRightUnder Δ[0] ⋙ pointedSlice where
  app n := Under.homMk ((joinRightUnderAdjunction Δ[0]).homEquiv _ _ (mergeStdUnder n.len)) (by
    refine ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left _ _).symm.trans
      (congrArg _ (Under.UnderMorphism.ext ?_))
    exact joinMap_joinInclRight_comp_mergeStd n.len)
  naturality n m f := by
    refine Under.UnderMorphism.ext ?_
    refine ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left _ _).symm.trans
      (Eq.trans ?_ ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_right _ _))
    exact congrArg _ (Under.UnderMorphism.ext (joinMap_joinMap_comp_mergeStd f))

private noncomputable def mergeSection :
    joinRightUnder (Δ[0] : SSet.{u}) ⟶ joinRightUnder Δ[0] ⋙ pointedSlice :=
  (joinRightUnder (Δ[0] : SSet.{u})).descOfIsLeftKanExtension
    (Iso.refl (uliftYoneda.{u} ⋙ joinRightUnder (Δ[0] : SSet.{u}))).hom _ mergeRestriction

private instance isLeftKanExtension_id :
    (𝟭 SSet.{u}).IsLeftKanExtension (Iso.refl (uliftYoneda.{u} ⋙ 𝟭 SSet.{u})).hom :=
  Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} _ (Iso.refl _)

private theorem mergeSection_app_uliftYoneda (n : SimplexCategory) :
    mergeSection.app (uliftYoneda.{u}.obj n) = mergeRestriction.app n :=
  (Category.id_comp _).symm.trans
    ((joinRightUnder (Δ[0] : SSet.{u})).descOfIsLeftKanExtension_fac_app
      (Iso.refl (uliftYoneda.{u} ⋙ joinRightUnder (Δ[0] : SSet.{u}))).hom _ mergeRestriction n)

private theorem mergeSection_comp_sliceProj :
    mergeSection ≫ Functor.whiskerLeft (joinRightUnder Δ[0]) sliceProjNat =
      𝟙 (joinRightUnder (Δ[0] : SSet.{u})) := by
  refine (joinRightUnder (Δ[0] : SSet.{u})).hom_ext_of_isLeftKanExtension
    (Iso.refl (uliftYoneda.{u} ⋙ joinRightUnder (Δ[0] : SSet.{u}))).hom _ _ ?_
  ext n : 2
  simp only [NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Functor.whiskerLeft_app,
    Category.id_comp]
  rw [mergeSection_app_uliftYoneda]
  exact Under.UnderMorphism.ext ((homEquiv_comp_sliceProj (mergeStdUnder n.len)).trans
    (joinInclLeft_comp_mergeStd n.len))

private noncomputable def mergeSectionRestriction :
    𝟭 SSet.{u} ⟶ joinRightUnder Δ[0] ⋙ slice Δ[0] where
  app W := joinInclLeft W Δ[0] ≫ (mergeSection.app W).right
  naturality W W' f := by
    have h := congrArg Under.Hom.right (mergeSection.naturality f)
    rw [Under.comp_right, Under.comp_right] at h
    exact (joinInclLeft_comp_joinMap_assoc f (𝟙 Δ[0]) _).symm.trans
      ((congrArg (joinInclLeft W Δ[0] ≫ ·) h).trans (Category.assoc _ _ _).symm)

private theorem mergeSectionRestriction_eq :
    mergeSectionRestriction = (joinRightUnderAdjunction (Δ[0] : SSet.{u})).unit := by
  refine (𝟭 SSet.{u}).hom_ext_of_isLeftKanExtension
    (Iso.refl (uliftYoneda.{u} ⋙ 𝟭 SSet.{u})).hom _ _ ?_
  ext n : 2
  simp only [Iso.refl_hom, Functor.whiskerLeft_app, Category.id_comp]
  refine (congrArg (joinInclLeft _ Δ[0] ≫ ·)
    (congrArg Under.Hom.right (mergeSection_app_uliftYoneda n))).trans ?_
  refine ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left _ _).symm.trans
    (Eq.trans ?_ ((joinRightUnderAdjunction Δ[0]).homEquiv_id _))
  exact congrArg _ (Under.UnderMorphism.ext (joinMap_joinInclLeft_comp_mergeStd n.len))

private noncomputable def mergeCone (W : SSet.{u}) :
    (joinRightUnder Δ[0]).obj (join W Δ[0]) ⟶ (joinRightUnder Δ[0]).obj W :=
  ((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm (mergeSection.app W).right

private noncomputable def mergeMap (W : SSet.{u}) : join (join W Δ[0]) Δ[0] ⟶ join W Δ[0] :=
  (mergeCone W).right

private theorem joinInclLeft_comp_mergeMap (W : SSet.{u}) :
    joinInclLeft (join W Δ[0]) Δ[0] ≫ mergeMap W = 𝟙 _ := by
  have h := congrArg Under.Hom.right (congr_app mergeSection_comp_sliceProj W)
  have e : mergeMap W = joinMap (mergeSection.app W).right (𝟙 Δ[0]) ≫
      ((joinRightUnderAdjunction Δ[0]).counit.app ((joinRightUnder Δ[0]).obj W)).right :=
    congrArg Under.Hom.right (Adjunction.homEquiv_counit _ _ _ _)
  rw [e]
  exact (joinInclLeft_comp_joinMap_assoc _ (𝟙 Δ[0]) _).trans h

private theorem joinMap_joinInclLeft_comp_mergeMap (W : SSet.{u}) :
    joinMap (joinInclLeft W Δ[0]) (𝟙 Δ[0]) ≫ mergeMap W = 𝟙 _ := by
  have h := congr_app mergeSectionRestriction_eq W
  have h' : (joinRightUnder Δ[0]).map (joinInclLeft W Δ[0]) ≫ mergeCone W = 𝟙 _ :=
    ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left_symm _ _).symm.trans
      ((congrArg _ h).trans ((joinRightUnderAdjunction Δ[0]).homEquiv_symm_unit _))
  exact congrArg Under.Hom.right h'

private theorem joinMap_joinMap_comp_mergeMap {W W' : SSet.{u}} (f : W ⟶ W') :
    joinMap (joinMap f (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ mergeMap W' = mergeMap W ≫ joinMap f (𝟙 Δ[0]) := by
  have h := congrArg Under.Hom.right (mergeSection.naturality f)
  rw [Under.comp_right, Under.comp_right] at h
  have h' : (joinRightUnder Δ[0]).map (joinMap f (𝟙 Δ[0])) ≫ mergeCone W' =
      mergeCone W ≫ (joinRightUnder Δ[0]).map f :=
    ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_left_symm _ _).symm.trans
      ((congrArg _ h).trans ((joinRightUnderAdjunction Δ[0]).homEquiv_naturality_right_symm _ _))
  exact congrArg Under.Hom.right h'

end Merge

section Codiscrete

open Opposite

private theorem coherentIso_hom_ext {K : SSet.{u}} {f g : K ⟶ coherentIso.{u}}
    (h : ∀ x : K _⦋0⦌, f.app _ x = g.app _ x) : f = g := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
  refine coherentIso.simplexEquiv.injective (funext fun i ↦ ?_)
  have hf := congrArg (fun z ↦ coherentIso.simplexEquiv z 0)
    (NatTrans.naturality_apply f (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op y)
  have hg := congrArg (fun z ↦ coherentIso.simplexEquiv z 0)
    (NatTrans.naturality_apply g (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op y)
  exact hf.symm.trans ((congrArg (fun z ↦ coherentIso.simplexEquiv z 0) (h _)).trans hg)

private def coherentIsoMk {K : SSet.{u}} (φ : K _⦋0⦌ → Bool) :
    K ⟶ coherentIso.{u} where
  app n := TypeCat.ofHom fun y ↦ coherentIso.simplexEquiv.symm fun i ↦
    φ (K.map (SimplexCategory.const ⦋0⦌ n.unop i).op y)
  naturality n m g := by
    refine ConcreteCategory.hom_ext _ _ fun y ↦ coherentIso.simplexEquiv.injective
      (funext fun i ↦ ?_)
    change φ (K.map (SimplexCategory.const ⦋0⦌ m.unop i).op (K.map g y)) =
      φ (K.map (SimplexCategory.const ⦋0⦌ n.unop (g.unop.toOrderHom i)).op y)
    rw [← Functor.map_comp_apply, ← g.op_unop, ← op_comp, SimplexCategory.const_comp]
    rfl

private theorem coherentIsoMk_app_vertex {K : SSet.{u}} (φ : K _⦋0⦌ → Bool) (x : K _⦋0⦌) :
    (coherentIsoMk φ).app _ x = cond (φ x) coherentIso.x₁ coherentIso.x₀ := by
  refine coherentIso.simplexEquiv.injective (funext fun i ↦ ?_)
  obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ :=
    SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun _ ↦
      Subsingleton.elim (α := Fin 1) _ _))
  change φ (K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x) = _
  rw [h, op_id, CategoryTheory.Functor.map_id_apply]
  cases φ x <;> rfl

private theorem joinInclLeft_app_ne_joinInclRight_app {X Y : SSet.{u}} (x : X _⦋0⦌)
    (y : Y _⦋0⦌) : (joinInclLeft X Y).app _ x ≠ (joinInclRight X Y).app _ y := by
  intro h
  let q : join X Y ⟶ Δ[0 + 0 + 1] := joinMap (stdSimplex.isTerminalObj₀.from X)
    (stdSimplex.isTerminalObj₀.from Y) ≫ (stdSimplexJoinIso.{u} 0 0).hom
  have hl : joinInclLeft X Y ≫ q =
      stdSimplex.isTerminalObj₀.from X ≫
        stdSimplex.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌) := by
    rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_stdSimplexJoinIso_hom]
  have hr : joinInclRight X Y ≫ q =
      stdSimplex.isTerminalObj₀.from Y ≫
        stdSimplex.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌) := by
    rw [joinInclRight_comp_joinMap_assoc, joinInclRight_comp_stdSimplexJoinIso_hom]
  have h' := congrArg (q.app _) h
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hl, ← ConcreteCategory.comp_apply,
    ← NatTrans.comp_app, hr] at h'
  have h'' := congrArg (fun z : (Δ[0 + 0 + 1] : SSet.{u}) _⦋0⦌ ↦
    ((stdSimplex.objEquiv z).toOrderHom 0).val) h'
  have e : ∀ (z : (Δ[0] : SSet.{u}) _⦋0⦌) (f : ⦋0⦌ ⟶ ⦋0 + 0 + 1⦌),
      (stdSimplex.objEquiv ((stdSimplex.map f).app _ z)).toOrderHom 0 = f.toOrderHom 0 :=
    fun z f ↦ congrArg f.toOrderHom (Subsingleton.elim (α := Fin 1) _ _)
  rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, e, e, AugmentedSimplexCategory.inl'_eval,
    AugmentedSimplexCategory.inr'_eval] at h''
  simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero,
    SimplexCategory.len_mk] at h''
  omega

private theorem coherentIso_x₀_ne_x₁ : coherentIso.x₀.{u} ≠ coherentIso.x₁ := fun h ↦
  Bool.false_ne_true (congrArg (fun v ↦ coherentIso.simplexEquiv v 0) h)

private theorem stdSimplexJoin_vertex (n : ℕ) (x : (Δ[n + 0 + 1] : SSet.{u}) _⦋0⦌) :
    (∃ y : (Δ[n] : SSet.{u}) _⦋0⦌,
      (stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌)).app _ y = x) ∨
      ∃ y : (Δ[0] : SSet.{u}) _⦋0⦌,
        (stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌)).app _ y = x := by
  by_cases h : (x 0).val < n + 1
  · refine Or.inl ⟨stdSimplex.obj₀Equiv.symm ⟨_, h⟩, stdSimplex.ext _ _ fun i ↦ ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    refine Fin.ext ?_
    change ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom ⟨_, h⟩).val = (x 0).val
    rw [AugmentedSimplexCategory.inl'_eval]
    simp
  · refine Or.inr ⟨stdSimplex.obj₀Equiv.symm 0, stdSimplex.ext _ _ fun i ↦ ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    refine Fin.ext ?_
    change ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom 0).val = (x 0).val
    rw [AugmentedSimplexCategory.inr'_eval]
    have := (x 0).isLt
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero, SimplexCategory.len_mk] at this ⊢
    omega

private theorem join_hom_ext_coherentIso {n : ℕ}
    {f g : join (Δ[n] : SSet.{u}) Δ[0] ⟶ coherentIso.{u}}
    (hl : joinInclLeft _ _ ≫ f = joinInclLeft _ _ ≫ g)
    (hr : joinInclRight _ _ ≫ f = joinInclRight _ _ ≫ g) : f = g := by
  have hl' : stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌) ≫
      (stdSimplexJoinIso.{u} n 0).inv ≫ f =
        stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌) ≫
          (stdSimplexJoinIso.{u} n 0).inv ≫ g := by
    rw [← joinInclLeft_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id_assoc, hl]
  have hr' : stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫
      (stdSimplexJoinIso.{u} n 0).inv ≫ f =
        stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌) ≫
          (stdSimplexJoinIso.{u} n 0).inv ≫ g := by
    rw [← joinInclRight_comp_stdSimplexJoinIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id_assoc, hr]
  have e : (stdSimplexJoinIso.{u} n 0).inv ≫ f = (stdSimplexJoinIso n 0).inv ≫ g := by
    refine coherentIso_hom_ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := stdSimplexJoin_vertex n x
    · exact congrArg (fun φ ↦ φ.app _ y) hl'
    · exact congrArg (fun φ ↦ φ.app _ y) hr'
  rw [← Iso.hom_inv_id_assoc (stdSimplexJoinIso.{u} n 0) f, e, Iso.hom_inv_id_assoc]

private theorem stdSimplex_map_inr'_eq :
    (stdSimplex.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌) : (Δ[0] : SSet.{u}) ⟶ Δ[0 + 0 + 1]) =
      stdSimplex.δ 0 := by
  refine congrArg stdSimplex.map
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ ?_)))
  obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
  exact AugmentedSimplexCategory.inr'_eval ⦋0⦌ ⦋0⦌ 0

private theorem joinInclRight_comp_isoEdge :
    joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom ≫ isoEdge.{u} =
      yonedaEquiv.symm coherentIso.x₁ := by
  rw [reassoc_of% (joinInclRight_comp_stdSimplexJoinIso_hom.{u} 0 0)]
  refine (congrArg (· ≫ isoEdge) stdSimplex_map_inr'_eq).trans ?_
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, coherentIso.hom.tgt_eq]

open Classical in
private noncomputable def isoConeRetraction : join coherentIso.{u} Δ[0] ⟶ coherentIso.{u} :=
  coherentIsoMk fun w ↦ decide (w ≠ (joinInclLeft coherentIso.{u} Δ[0]).app _ coherentIso.x₀)

private theorem joinInclLeft_comp_isoConeRetraction :
    joinInclLeft coherentIso.{u} Δ[0] ≫ isoConeRetraction = 𝟙 _ := by
  refine coherentIso_hom_ext fun v ↦ ?_
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, isoConeRetraction,
    coherentIsoMk_app_vertex]
  obtain ⟨b, rfl⟩ := Atoms.Homotopical.coherentIso_vertex_eq v
  have hinj := (mono_iff_injective ((joinInclLeft coherentIso.{u} Δ[0]).app
    (Opposite.op ⦋0⦌))).1 inferInstance
  cases b
  · simp
  · have : (joinInclLeft coherentIso.{u} Δ[0]).app _ coherentIso.x₁ ≠
        (joinInclLeft coherentIso.{u} Δ[0]).app _ coherentIso.x₀ :=
      fun h ↦ coherentIso_x₀_ne_x₁ (hinj h).symm
    simp [this]

private theorem joinInclRight_comp_isoConeRetraction :
    joinInclRight coherentIso.{u} Δ[0] ≫ isoConeRetraction = yonedaEquiv.symm coherentIso.x₁ := by
  refine coherentIso_hom_ext fun y ↦ ?_
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, isoConeRetraction,
    coherentIsoMk_app_vertex]
  simp only [ne_eq, (joinInclLeft_app_ne_joinInclRight_app coherentIso.x₀ y).symm,
    not_false_eq_true, decide_true, cond_true]
  exact coherentIso.simplexEquiv.injective (funext fun _ ↦ rfl)

private theorem joinInclRight_comp_mergeMap (W : SSet.{u}) :
    joinInclRight (join W Δ[0]) Δ[0] ≫ mergeMap W = joinInclRight W Δ[0] :=
  Under.w (mergeCone W)

private theorem joinMap_isoEdge_comp_isoConeRetraction :
    joinMap isoEdge (𝟙 Δ[0]) ≫ isoConeRetraction =
      joinMap (stdSimplexJoinIso 0 0).inv (𝟙 Δ[0]) ≫ mergeMap Δ[0] ≫
        (stdSimplexJoinIso 0 0).hom ≫ isoEdge := by
  refine join_hom_ext_coherentIso (n := 1) ?_ ?_
  · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_isoConeRetraction, Category.comp_id,
      joinInclLeft_comp_joinMap_assoc, reassoc_of% (joinInclLeft_comp_mergeMap Δ[0]),
      Iso.inv_hom_id_assoc]
  · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp, joinInclRight_comp_isoConeRetraction,
      joinInclRight_comp_joinMap_assoc, Category.id_comp,
      reassoc_of% (joinInclRight_comp_mergeMap Δ[0]), joinInclRight_comp_isoEdge]

end Codiscrete

section Retraction

variable (Z : Under (Δ[0] : SSet.{u}))

private theorem isPushout_terminalization_join :
    IsPushout (joinMap (coneEdge Z) (𝟙 Δ[0])) (joinMap isoEdge (𝟙 Δ[0]))
      (joinMap (terminalizationInl Z) (𝟙 Δ[0])) (joinMap (terminalizationInr Z) (𝟙 Δ[0])) :=
  (isPushout_terminalization Z).map
    (joinRightUnder (Δ[0] : SSet.{u}) ⋙ Under.forget _)

private theorem retractionJoin_condition :
    joinMap (coneEdge Z) (𝟙 Δ[0]) ≫ mergeMap Z.right ≫ terminalizationInl Z =
      joinMap isoEdge (𝟙 Δ[0]) ≫ isoConeRetraction ≫ terminalizationInr Z := by
  have h₁ : joinMap (coneEdge Z) (𝟙 Δ[0]) = joinMap (stdSimplexJoinIso 0 0).inv (𝟙 Δ[0]) ≫
      joinMap (joinMap Z.hom (𝟙 Δ[0])) (𝟙 Δ[0]) :=
    (joinMap_comp_joinMap_id _ _ _).symm
  rw [h₁, Category.assoc, reassoc_of% (joinMap_joinMap_comp_mergeMap Z.hom),
    reassoc_of% joinMap_isoEdge_comp_isoConeRetraction, ← (isPushout_terminalization Z).w,
    coneEdge, Category.assoc, Iso.hom_inv_id_assoc]

private noncomputable def retractionJoin :
    join (terminalization.obj Z).right Δ[0] ⟶ (terminalization.obj Z).right :=
  (isPushout_terminalization_join Z).desc (mergeMap Z.right ≫ terminalizationInl Z)
    (isoConeRetraction ≫ terminalizationInr Z) (retractionJoin_condition Z)

private theorem joinInclLeft_comp_retractionJoin :
    joinInclLeft _ Δ[0] ≫ retractionJoin Z = 𝟙 _ := by
  refine (isPushout_terminalization Z).hom_ext ?_ ?_
  · rw [Category.comp_id, ← joinInclLeft_comp_joinMap_assoc, retractionJoin,
      (isPushout_terminalization_join Z).inl_desc, reassoc_of% (joinInclLeft_comp_mergeMap _)]
  · rw [Category.comp_id, ← joinInclLeft_comp_joinMap_assoc, retractionJoin,
      (isPushout_terminalization_join Z).inr_desc,
      reassoc_of% joinInclLeft_comp_isoConeRetraction]

private theorem retraction_condition :
    coneEdge (terminalization.obj Z) ≫ retractionJoin Z = isoEdge ≫ terminalizationInr Z := by
  have h : coneEdge (terminalization.obj Z) = (stdSimplexJoinIso 0 0).inv ≫
      joinMap (yonedaEquiv.symm coherentIso.x₀) (𝟙 Δ[0]) ≫
        joinMap (terminalizationInr Z) (𝟙 Δ[0]) :=
    (congrArg ((stdSimplexJoinIso 0 0).inv ≫ ·) ((congrArg (fun g ↦ joinMap g (𝟙 Δ[0]))
      (terminalization_obj_hom_eq Z)).trans (joinMap_comp_joinMap_id _ _ _).symm))
  have h' : joinMap (yonedaEquiv.symm coherentIso.x₀) (𝟙 Δ[0]) ≫ isoConeRetraction =
      (stdSimplexJoinIso 0 0).hom ≫ isoEdge := by
    refine join_hom_ext_coherentIso (n := 0) ?_ ?_
    · rw [joinInclLeft_comp_joinMap_assoc, joinInclLeft_comp_isoConeRetraction,
        Category.comp_id, joinInclLeft_comp_isoEdge]
    · rw [joinInclRight_comp_joinMap_assoc, Category.id_comp,
        joinInclRight_comp_isoConeRetraction, joinInclRight_comp_isoEdge]
  rw [h, Category.assoc, Category.assoc, retractionJoin,
    (isPushout_terminalization_join Z).inr_desc, reassoc_of% h', Iso.inv_hom_id_assoc]

private noncomputable def retraction :
    (terminalization.obj (terminalization.obj Z)).right ⟶ (terminalization.obj Z).right :=
  (isPushout_terminalization (terminalization.obj Z)).desc (retractionJoin Z)
    (terminalizationInr Z) (retraction_condition Z)

private theorem terminalizationUnit_app_comp_retraction :
    (terminalizationUnit.app (terminalization.obj Z)).right ≫ retraction Z = 𝟙 _ := by
  rw [terminalizationUnit_app_right, Category.assoc, retraction,
    (isPushout_terminalization _).inl_desc, joinInclLeft_comp_retractionJoin]
  rfl

private theorem terminalization_map_comp_retraction :
    (terminalization.map (terminalizationUnit.app Z)).right ≫ retraction Z = 𝟙 _ := by
  refine (isPushout_terminalization Z).hom_ext (Eq.trans ?_ (Category.comp_id _).symm)
    (Eq.trans ?_ (Category.comp_id _).symm)
  · rw [← joinMap_comp_terminalizationInl_assoc, retraction,
      (isPushout_terminalization _).inl_desc, terminalizationUnit_app_right,
      ← joinMap_comp_joinMap_id, Category.assoc, retractionJoin,
      (isPushout_terminalization_join Z).inl_desc,
      reassoc_of% (joinMap_joinInclLeft_comp_mergeMap Z.right)]
  · rw [terminalizationInr_comp_map_assoc, retraction,
      (isPushout_terminalization _).inr_desc]

end Retraction

open modelCategoryJoyal in
theorem weakEquivalence_terminalization_map_terminalizationUnit_app_right
    (Z : Under (Δ[0] : SSet.{u})) :
    WeakEquivalence (terminalization.map (terminalizationUnit.app Z)).right := by
  have := weakEquivalence_terminalizationUnit_app_right (terminalization.obj Z)
    (rightAnodyneExtensions_terminalization_obj_hom Z)
  have : WeakEquivalence ((terminalizationUnit.app (terminalization.obj Z)).right ≫
      retraction Z) := by
    rw [terminalizationUnit_app_comp_retraction]
    infer_instance
  have := weakEquivalence_of_precomp
    (terminalizationUnit.app (terminalization.obj Z)).right (retraction Z)
  have : WeakEquivalence ((terminalization.map (terminalizationUnit.app Z)).right ≫
      retraction Z) := by
    rw [terminalization_map_comp_retraction]
    infer_instance
  exact weakEquivalence_of_postcomp _ (retraction Z)

open modelCategoryJoyal in
theorem weakEquivalence_terminalization_map_pushout_inl_right
    {S Y : Under (Δ[0] : SSet.{u})} (i : S ⟶ Y) [Mono i.right] :
    WeakEquivalence (terminalization.map (pushout.inl i (terminalizationUnit.app S))).right := by
  have h : IsPushout (terminalization.map i).right
      (terminalization.map (terminalizationUnit.app S)).right
      (terminalization.map (pushout.inl i (terminalizationUnit.app S))).right
      (terminalization.map (pushout.inr i (terminalizationUnit.app S))).right :=
    (IsPushout.of_hasPushout i (terminalizationUnit.app S)).map
      (terminalization ⋙ Under.forget _)
  have := Atoms.Homotopical.joyalInterval.{u}.cylinder.isALocalizer_weakEquivalences _
    innerHornInclusions_le_monomorphisms
  have := mono_terminalization_map_right i
  have hη := weakEquivalence_terminalization_map_terminalizationUnit_app_right S
  rw [weakEquivalence_iff] at hη ⊢
  exact Atoms.Homotopical.IsALocalizer.mem_of_isPushout
    (V := Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions) h hη

end SSet
