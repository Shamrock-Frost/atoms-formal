import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

namespace MonoidalClosed

variable [MonoidalClosed C]

@[reassoc]
theorem curry_fst_comp_pre_app {S F F' : C} (i : F ⟶ F') (pF' : F' ⟶ S) :
    curry (fst F' (𝟙_ C) ≫ pF') ≫ (pre i).app S = curry (fst F (𝟙_ C) ≫ i ≫ pF') := by
  rw [curry_pre_app, whiskerRight_fst_assoc]

section Pullbacks

variable [HasPullbacks C]

noncomputable abbrev ihomOver {S F G : C} (pF : F ⟶ S) (pG : G ⟶ S) : C :=
  pullback ((ihom F).map pG) (curry (fst F (𝟙_ C) ≫ pF))

noncomputable def ihomOverHomEquiv {S F G : C} (pF : F ⟶ S) (pG : G ⟶ S) (K : C) :
    (K ⟶ ihomOver pF pG) ≃ {f : F ⊗ K ⟶ G // f ≫ pG = fst _ _ ≫ pF} where
  toFun g := ⟨uncurry (g ≫ pullback.fst _ _), by
    rw [← uncurry_natural_right, Category.assoc, pullback.condition, ← Category.assoc,
      uncurry_natural_left, uncurry_curry, whiskerLeft_fst_assoc]⟩
  invFun f := pullback.lift (curry f.1) (toUnit K) (by
    rw [← curry_natural_right, ← curry_natural_left, whiskerLeft_fst_assoc, f.2])
  left_inv g := pullback.hom_ext (by rw [pullback.lift_fst, curry_uncurry]) (toUnit_unique _ _)
  right_inv f := Subtype.ext ((congrArg uncurry (pullback.lift_fst _ _ _)).trans (uncurry_curry _))

noncomputable def ihomOverRestrict {S F F' G : C} (i : F ⟶ F') (pF' : F' ⟶ S) (pG : G ⟶ S) :
    ihomOver pF' pG ⟶ ihomOver (i ≫ pF') pG :=
  pullback.map _ _ _ _ ((pre i).app G) (𝟙 _) ((pre i).app S)
    (pre_comm_ihom_map i pG).symm (by rw [Category.id_comp, curry_fst_comp_pre_app])

@[reassoc (attr := simp)]
theorem ihomOverRestrict_fst {S F F' G : C} (i : F ⟶ F') (pF' : F' ⟶ S) (pG : G ⟶ S) :
    ihomOverRestrict i pF' pG ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (pre i).app G :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ihomOverRestrict_snd {S F F' G : C} (i : F ⟶ F') (pF' : F' ⟶ S) (pG : G ⟶ S) :
    ihomOverRestrict i pF' pG ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem isPullback_ihomOverRestrict {S F F' G : C} (i : F ⟶ F') (pF' : F' ⟶ S) (pG : G ⟶ S) :
    IsPullback (pullback.fst _ _) (ihomOverRestrict i pF' pG)
      (pullback.lift ((pre i).app G) ((ihom F').map pG) (pre_comm_ihom_map i pG))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ curry (fst F' (𝟙_ C) ≫ pF'))
        (by simp only [Category.assoc, curry_fst_comp_pre_app, pullback.condition]) :
        ihomOver (i ≫ pF') pG ⟶ pullback ((ihom F).map pG) ((pre i).app S)) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := pullback.snd _ _)
    (h₃₁ := curry (fst F' (𝟙_ C) ≫ pF')) ?_ ?_ ?_
  · simp only [ihomOverRestrict_snd, pullback.lift_snd]
    exact IsPullback.of_hasPullback ((ihom F').map pG) (curry (fst F' (𝟙_ C) ≫ pF'))
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, ihomOverRestrict_fst]
    · simp only [Category.assoc, pullback.lift_snd, ihomOverRestrict_snd_assoc, pullback.condition]
  · refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := (pre i).app S)
      (v₁₃ := (ihom F).map pG) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    simp only [pullback.lift_fst, curry_fst_comp_pre_app]
    exact IsPullback.of_hasPullback _ _

end Pullbacks

section Terminal

variable {T : C} (hT : IsTerminal T)

private noncomputable def ihomTerminalHom (X : C) : (ihom T).obj X ⟶ X :=
  lift (hT.from _) (𝟙 _) ≫ (ihom.ev T).app X

private lemma curry_comp_ihomTerminalHom {X Y : C} (g : T ⊗ Y ⟶ X) :
    curry g ≫ ihomTerminalHom hT X = lift (hT.from Y) (𝟙 Y) ≫ g := by
  have h : curry g ≫ lift (hT.from _) (𝟙 _) = lift (hT.from Y) (𝟙 Y) ≫ T ◁ curry g := by
    ext1
    · exact hT.hom_ext _ _
    · simp
  rw [ihomTerminalHom, ← Category.assoc, h, Category.assoc, whiskerLeft_curry_ihom_ev_app]

private lemma snd_comp_ihomTerminalHom (X : C) :
    snd T _ ≫ ihomTerminalHom hT X = (ihom.ev T).app X := by
  have h : snd T ((ihom T).obj X) ≫ lift (hT.from _) (𝟙 _) = 𝟙 _ := by
    ext1
    · exact hT.hom_ext _ _
    · simp
  rw [ihomTerminalHom, ← Category.assoc, h, Category.id_comp]

noncomputable def ihomTerminalIso (X : C) : (ihom T).obj X ≅ X where
  hom := ihomTerminalHom hT X
  inv := curry (snd T X)
  hom_inv_id := by
    rw [← curry_natural_left, whiskerLeft_snd, snd_comp_ihomTerminalHom,
      ← uncurry_id_eq_ev, curry_uncurry]
  inv_hom_id := by
    rw [curry_comp_ihomTerminalHom, lift_snd]

theorem curry_comp_ihomTerminalIso_hom {X Y : C} (g : T ⊗ Y ⟶ X) :
    curry g ≫ (ihomTerminalIso hT X).hom = lift (hT.from Y) (𝟙 Y) ≫ g :=
  curry_comp_ihomTerminalHom hT g

theorem ihom_map_comp_ihomTerminalIso_hom {X Y : C} (f : X ⟶ Y) :
    (ihom T).map f ≫ (ihomTerminalIso hT Y).hom = (ihomTerminalIso hT X).hom ≫ f := by
  change _ ≫ ihomTerminalHom hT Y = ihomTerminalHom hT X ≫ f
  rw [← curry_uncurry ((ihom T).map f), curry_comp_ihomTerminalHom, uncurry_ihom_map,
    ihomTerminalHom, Category.assoc]

end Terminal

end MonoidalClosed

end CategoryTheory
