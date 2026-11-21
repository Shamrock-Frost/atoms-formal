import Atoms.Homotopical.Simplicial.ExtensionUnit
import Atoms.Homotopical.Simplicial.SubdivisionAnodyne
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

noncomputable def exPow : ℕ → (SSet.{u} ⥤ SSet.{u})
  | 0 => 𝟭 SSet.{u}
  | n + 1 => exPow n ⋙ SSet.ex

noncomputable def exPowSucc (n : ℕ) : exPow.{u} n ⟶ exPow.{u} (n + 1) :=
  (Functor.rightUnitor (exPow.{u} n)).inv ≫ Functor.whiskerLeft (exPow.{u} n) exUnit

noncomputable def exTower : ℕ ⥤ (SSet.{u} ⥤ SSet.{u}) := Functor.ofSequence exPowSucc.{u}

noncomputable def exInfty : SSet.{u} ⥤ SSet.{u} := colimit exTower

noncomputable def exInftyι (m : ℕ) : exTower.{u}.obj m ⟶ exInfty.{u} := colimit.ι exTower.{u} m

noncomputable def exInftyUnit : 𝟭 SSet.{u} ⟶ exInfty := exInftyι 0

noncomputable def exInftyRelativeUnit {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ pullback (exInftyUnit.{u}.app Y) (exInfty.{u}.map f) :=
  pullback.lift f (exInftyUnit.{u}.app X) (exInftyUnit.{u}.naturality f)

noncomputable def exTowerEvalIsColimit (X : SSet.{u}) :
    IsColimit (((evaluation SSet.{u} SSet.{u}).obj X).mapCocone (colimit.cocone exTower.{u})) :=
  isColimitOfPreserves ((evaluation SSet.{u} SSet.{u}).obj X) (colimit.isColimit exTower.{u})

theorem exTower_map_succ_app (n : ℕ) (X : SSet.{u}) :
    (exTower.{u}.map (homOfLE (Nat.le_add_right n 1))).app X =
      exUnit.app ((exTower.{u}.obj n).obj X) := by
  simp only [exTower, Functor.ofSequence_map_homOfLE_succ, exPowSucc]
  exact Category.id_comp _

theorem anodyneExtensions_exInftyUnit_app (X : SSet.{u}) :
    SSet.anodyneExtensions (exInftyUnit.{u}.app X) := by
  let h : SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ (exInftyUnit.{u}.app X) :=
    { F := exTower.{u} ⋙ (evaluation SSet.{u} SSet.{u}).obj X
      isoBot := Iso.refl _
      incl := (((evaluation SSet.{u} SSet.{u}).obj X).mapCocone (colimit.cocone exTower.{u})).ι
      isColimit := exTowerEvalIsColimit X
      fac := Category.id_comp _
      map_mem n _ := by
        change SSet.anodyneExtensions
          ((exTower.{u}.map (homOfLE (Nat.le_add_right n 1))).app X)
        rw [exTower_map_succ_app]
        exact SSet.strongAnodyneExtensions_le_anodyneExtensions _
          (strongAnodyneExtensions_exUnit_app _) }
  exact SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ _ h.mem

instance preservesLimits_exPow (n : ℕ) : PreservesLimits (exPow.{u} n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesLimits (𝟭 SSet.{u}))
  | succ n ih => exact inferInstanceAs (PreservesLimits (exPow.{u} n ⋙ SSet.ex))

instance preservesFiniteLimits_exInfty : PreservesFiniteLimits exInfty.{u} := by
  have : PreservesFiniteLimits exTower.{u}.flip :=
    preservesFiniteLimits_of_evaluation _ (fun n ↦ by
      change PreservesFiniteLimits (exPow.{u} n)
      infer_instance)
  have : PreservesFiniteLimits (colim (J := ℕ) (C := SSet.{u})) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (exTower.{u}.flip ⋙ colim) :=
    comp_preservesFiniteLimits exTower.{u}.flip (colim (J := ℕ) (C := SSet.{u}))
  exact preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim exTower.{u}).symm

@[reassoc]
theorem exTower_map_app_comp_ι_app {m k : ℕ} (h : m ≤ k) (X : SSet.{u}) :
    (exTower.{u}.map (homOfLE h)).app X ≫ (exInftyι.{u} k).app X =
      (exInftyι.{u} m).app X := by
  exact NatTrans.congr_app (colimit.w exTower.{u} (homOfLE h)) X

theorem exists_comp_ι_app_eq {K X : SSet.{u}} [IsFinitelyPresentable.{u} K]
    (t : K ⟶ exInfty.{u}.obj X) :
    ∃ (m : ℕ) (t' : K ⟶ (exTower.{u}.obj m).obj X), t' ≫ (exInftyι.{u} m).app X = t := by
  have : IsFinitelyPresentable.{0} K := isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.2
    (preservesFilteredColimitsOfSize_of_univLE.{u, u} (coyoneda.obj (Opposite.op K)))
  exact IsFinitelyPresentable.exists_hom_of_isColimit (exTowerEvalIsColimit X) t

theorem exists_comp_exTower_map_app_eq {K X : SSet.{u}} [IsFinitelyPresentable.{u} K] {m : ℕ}
    (u v : K ⟶ (exTower.{u}.obj m).obj X)
    (h : u ≫ (exInftyι.{u} m).app X = v ≫ (exInftyι.{u} m).app X) :
    ∃ (k : ℕ) (hk : m ≤ k), u ≫ (exTower.{u}.map (homOfLE hk)).app X =
      v ≫ (exTower.{u}.map (homOfLE hk)).app X := by
  have : IsFinitelyPresentable.{0} K := isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.2
    (preservesFilteredColimitsOfSize_of_univLE.{u, u} (coyoneda.obj (Opposite.op K)))
  obtain ⟨k, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    (exTowerEvalIsColimit X) u v h
  obtain rfl : a = b := Subsingleton.elim _ _
  exact ⟨k, leOfHom a, hab⟩

theorem J_rlp_exPow_map (n : ℕ) {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp ((exPow.{u} n).map p) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact J_rlp_ex_map ih

theorem hasLift_exInfty_map {A B X Y : SSet.{u}}
    [IsFinitelyPresentable.{u} A] [IsFinitelyPresentable.{u} B] {i : A ⟶ B} {p : X ⟶ Y}
    (hp : ∀ l, HasLiftingProperty i ((exTower.{u}.obj l).map p))
    {t : A ⟶ exInfty.{u}.obj X} {b : B ⟶ exInfty.{u}.obj Y}
    (sq : CommSq t i (exInfty.{u}.map p) b) : sq.HasLift := by
  obtain ⟨m₁, b₁, rfl⟩ := exists_comp_ι_app_eq b
  obtain ⟨m₂, t₂, rfl⟩ := exists_comp_ι_app_eq t
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m₁ ≤ m ∧ m₂ ≤ m := ⟨max m₁ m₂, le_max_left _ _, le_max_right _ _⟩
  let tm := t₂ ≫ (exTower.{u}.map (homOfLE hm₂)).app X
  let bm := b₁ ≫ (exTower.{u}.map (homOfLE hm₁)).app Y
  have ht : tm ≫ (exInftyι.{u} m).app X = t₂ ≫ (exInftyι.{u} m₂).app X := by
    simp only [tm, Category.assoc, exTower_map_app_comp_ι_app]
  have hb : bm ≫ (exInftyι.{u} m).app Y = b₁ ≫ (exInftyι.{u} m₁).app Y := by
    simp only [bm, Category.assoc, exTower_map_app_comp_ι_app]
  obtain ⟨l, hl, hkl⟩ := exists_comp_exTower_map_app_eq (tm ≫ (exTower.{u}.obj m).map p)
    (i ≫ bm) (by
      rw [Category.assoc, (exInftyι.{u} m).naturality, reassoc_of% ht, ← Category.assoc, sq.w,
        Category.assoc, hb])
  let tl := tm ≫ (exTower.{u}.map (homOfLE hl)).app X
  let bl := bm ≫ (exTower.{u}.map (homOfLE hl)).app Y
  have sq' : CommSq tl i ((exTower.{u}.obj l).map p) bl := ⟨by
    simpa only [tl, bl, Category.assoc, NatTrans.naturality] using hkl⟩
  refine ⟨⟨{ l := sq'.lift ≫ (exInftyι.{u} l).app X, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [sq'.fac_left_assoc, ← ht]
    simp only [tl, Category.assoc, exTower_map_app_comp_ι_app]
  · rw [Category.assoc, ← (exInftyι.{u} l).naturality, sq'.fac_right_assoc, ← hb]
    simp only [bl, Category.assoc, exTower_map_app_comp_ι_app]

theorem J_rlp_exInfty_map {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.modelCategoryQuillen.J.rlp (exInfty.{u}.map p) := by
  intro A B j hj
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  exact ⟨fun sq ↦ hasLift_exInfty_map (fun l ↦
    J_rlp_exPow_map l hp _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) k)) sq⟩

theorem anodyneExtensions_pullback_lift_exUnit {Y A B : SSet.{u}} (β : Y ⟶ B) (g : A ⟶ B)
    (β' : Y ⟶ SSet.ex.obj B) (hβ : β' = β ≫ exUnit.app B) (g' : SSet.ex.obj A ⟶ SSet.ex.obj B)
    (hg : g' = SSet.ex.map g)
    (w : pullback.fst β g ≫ β' = (pullback.snd β g ≫ exUnit.app A) ≫ g') :
    SSet.anodyneExtensions (pullback.lift (pullback.fst β g)
      (pullback.snd β g ≫ exUnit.app A) w : pullback β g ⟶ pullback β' g') := by
  subst hβ hg
  have h₁ : IsPullback (pullback.fst (exUnit.app Y) (SSet.ex.map (pullback.fst β g)))
      (pullback.snd _ _) (exUnit.app Y) (SSet.ex.map (pullback.fst β g)) :=
    IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (SSet.ex.map (pullback.snd β g)) (SSet.ex.map (pullback.fst β g))
      (SSet.ex.map g) (SSet.ex.map β) :=
    (IsPullback.of_hasPullback β g).flip.map SSet.ex
  have h := (h₁.flip.paste_horiz h₂).flip
  have hβ : exUnit.app Y ≫ SSet.ex.map β = β ≫ exUnit.app B := (exUnit.naturality β).symm
  rw [hβ] at h
  convert (MorphismProperty.cancel_right_of_respectsIso SSet.anodyneExtensions
    (exRelativeUnit (pullback.fst β g)) h.isoPullback.hom).2
      (SSet.strongAnodyneExtensions_le_anodyneExtensions _
        (strongAnodyneExtensions_exRelativeUnit (pullback.fst β g))) using 1
  apply pullback.hom_ext
  · rw [Category.assoc, h.isoPullback_hom_fst, exRelativeUnit, pullback.lift_fst,
      pullback.lift_fst]
  · rw [Category.assoc, h.isoPullback_hom_snd, exRelativeUnit, pullback.lift_snd,
      pullback.lift_snd_assoc]
    exact exUnit.naturality (pullback.snd β g)

noncomputable def exTowerUnit (Y : SSet.{u}) :
    (Functor.const ℕ).obj Y ⟶ exTower.{u} ⋙ (evaluation SSet.{u} SSet.{u}).obj Y where
  app n := (exTower.{u}.map (homOfLE (Nat.zero_le n))).app Y
  naturality i _ g :=
    (Category.id_comp _).trans
      (NatTrans.congr_app (exTower.{u}.map_comp (homOfLE (Nat.zero_le i)) g) Y)

noncomputable def exTowerMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    exTower.{u} ⋙ (evaluation SSet.{u} SSet.{u}).obj X ⟶
      exTower.{u} ⋙ (evaluation SSet.{u} SSet.{u}).obj Y :=
  Functor.whiskerLeft exTower.{u} ((evaluation SSet.{u} SSet.{u}).map f)

noncomputable abbrev relTower {X Y : SSet.{u}} (f : X ⟶ Y) : ℕ ⥤ SSet.{u} :=
  pullback (exTowerUnit Y) (exTowerMap f)

theorem exTowerUnit_app_succ (Y : SSet.{u}) (n : ℕ) :
    (exTowerUnit Y).app (n + 1) =
      (exTowerUnit Y).app n ≫ exUnit.app ((exTower.{u}.obj n).obj Y) := by
  rw [← exTower_map_succ_app]
  change _ = ((exTower.{u}.map _) ≫ (exTower.{u}.map _)).app Y
  rw [← Functor.map_comp]
  rfl

theorem anodyneExtensions_relTower_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    SSet.anodyneExtensions ((relTower f).map (homOfLE (Nat.le_add_right n 1))) := by
  let e := pullbackObjIso (exTowerUnit Y) (exTowerMap f)
  have w₀ : pullback.fst ((exTowerUnit Y).app n) ((exTowerMap f).app n) ≫
      (exTowerUnit Y).app n ≫ exUnit.app _ = (pullback.snd ((exTowerUnit Y).app n)
        ((exTowerMap f).app n) ≫ exUnit.app _) ≫ SSet.ex.map ((exTowerMap f).app n) := by
    rw [pullback.condition_assoc, Category.assoc]
    exact congrArg (pullback.snd _ _ ≫ ·) (exUnit.naturality ((exTowerMap f).app n))
  have w : pullback.fst ((exTowerUnit Y).app n) ((exTowerMap f).app n) ≫
      (exTowerUnit Y).app (n + 1) = (pullback.snd ((exTowerUnit Y).app n)
        ((exTowerMap f).app n) ≫ exUnit.app _) ≫ (exTowerMap f).app (n + 1) :=
    (congrArg (pullback.fst _ _ ≫ ·) (exTowerUnit_app_succ Y n)).trans w₀
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (e n) (e (n + 1)) ?_)).2
    (anodyneExtensions_pullback_lift_exUnit _ _ _ (exTowerUnit_app_succ Y n) _ rfl w)
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine ((congrArg ((e n).hom ≫ ·) (pullback.lift_fst _ _ _)).trans ?_).trans
      (congrArg ((relTower f).map _ ≫ ·) (pullbackObjIso_hom_comp_fst _ _ _)).symm
    exact (pullbackObjIso_hom_comp_fst _ _ _).trans
      (((pullback.fst (exTowerUnit Y) (exTowerMap f)).naturality
        (homOfLE (Nat.le_add_right n 1))).trans (Category.comp_id _)).symm
  · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine ((congrArg ((e n).hom ≫ ·) (pullback.lift_snd _ _ _)).trans ?_).trans
      (congrArg ((relTower f).map _ ≫ ·) (pullbackObjIso_hom_comp_snd _ _ _)).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (pullbackObjIso_hom_comp_snd _ _ _)).trans ?_
    refine Eq.trans ?_ ((pullback.snd (exTowerUnit Y) (exTowerMap f)).naturality
      (homOfLE (Nat.le_add_right n 1))).symm
    exact congrArg (_ ≫ ·) (exTower_map_succ_app n X).symm

noncomputable def colimitConstIso (Y : SSet.{u}) : colimit ((Functor.const ℕ).obj Y) ≅ Y :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone ℕ Y)

@[reassoc]
theorem ι_colimitConstIso_hom (Y : SSet.{u}) (n : ℕ) :
    colimit.ι ((Functor.const ℕ).obj Y) n ≫ (colimitConstIso Y).hom = 𝟙 Y :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n

theorem isPullback_colimit_relTower {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsPullback (colimMap (pullback.fst (exTowerUnit Y) (exTowerMap f)) ≫ (colimitConstIso Y).hom)
      (colimMap (pullback.snd (exTowerUnit Y) (exTowerMap f)) ≫
        (colimitObjIsoColimitCompEvaluation exTower.{u} X).inv)
      (exInftyUnit.{u}.app Y) (exInfty.{u}.map f) := by
  refine ((IsPullback.of_hasPullback (exTowerUnit Y) (exTowerMap f)).map colim).of_iso
    (Iso.refl _) (colimitConstIso Y) (colimitObjIsoColimitCompEvaluation exTower.{u} X).symm
    (colimitObjIsoColimitCompEvaluation exTower.{u} Y).symm (Category.id_comp _).symm
    (Category.id_comp _).symm ?_ ?_
  · apply colimit.hom_ext
    intro n
    change colimit.ι _ n ≫ colimMap (exTowerUnit Y) ≫ _ = colimit.ι _ n ≫ _ ≫ _
    rw [ι_colimMap_assoc]
    exact ((congrArg ((exTowerUnit Y).app n ≫ ·)
      (colimitObjIsoColimitCompEvaluation_ι_inv exTower.{u} n Y)).trans
        (exTower_map_app_comp_ι_app (Nat.zero_le n) Y)).trans
          ((ι_colimitConstIso_hom_assoc Y n _).trans (Category.id_comp _)).symm
  · apply colimit.hom_ext
    intro n
    change colimit.ι _ n ≫ colimMap (exTowerMap f) ≫ _ = colimit.ι _ n ≫ _ ≫ _
    rw [ι_colimMap_assoc]
    exact ((congrArg ((exTowerMap f).app n ≫ ·)
      (colimitObjIsoColimitCompEvaluation_ι_inv exTower.{u} n Y)).trans
        ((exInftyι.{u} n).naturality f)).trans
          (colimitObjIsoColimitCompEvaluation_ι_inv_assoc exTower.{u} n X _).symm

theorem exTowerUnit_app_zero (Y : SSet.{u}) : (exTowerUnit Y).app 0 = 𝟙 Y := by
  change (exTower.{u}.map (𝟙 0)).app Y = 𝟙 Y
  rw [exTower.{u}.map_id]
  rfl

instance isIso_exTowerUnit_app_zero (Y : SSet.{u}) : IsIso ((exTowerUnit Y).app 0) := by
  rw [exTowerUnit_app_zero]
  exact IsIso.id Y

theorem anodyneExtensions_exInftyRelativeUnit {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.anodyneExtensions (exInftyRelativeUnit f) := by
  have hP := isPullback_colimit_relTower f
  let T : SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ
      (colimit.ι (relTower f) 0) :=
    { F := relTower f
      isoBot := Iso.refl _
      incl := (colimit.cocone (relTower f)).ι
      isColimit := colimit.isColimit _
      fac := Category.id_comp _
      map_mem n _ := anodyneExtensions_relTower_map f n }
  have h₀ := SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ _ T.mem
  have hs : IsIso (pullback.snd ((exTowerUnit Y).app 0) ((exTowerMap f).app 0)) :=
    pullback_snd_iso_of_left_iso _ _
  let e₀ : (relTower f).obj 0 ≅ X := pullbackObjIso _ _ 0 ≪≫
    @asIso _ _ _ _ (pullback.snd ((exTowerUnit Y).app 0) ((exTowerMap f).app 0)) hs
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk e₀ hP.isoPullback ?_)).1 h₀
  have h₁ : (pullbackObjIso _ _ 0).hom ≫ pullback.snd _ _ ≫ (exTowerMap f).app 0 =
      (pullback.fst (exTowerUnit Y) (exTowerMap f)).app 0 :=
    (congrArg ((pullbackObjIso _ _ 0).hom ≫ ·) pullback.condition.symm).trans
      ((pullbackObjIso_hom_comp_fst_assoc _ _ 0 _).trans
        ((congrArg ((pullback.fst (exTowerUnit Y) (exTowerMap f)).app 0 ≫ ·)
          (exTowerUnit_app_zero Y)).trans (Category.comp_id _)))
  have h₂ : colimit.ι (relTower f) 0 ≫ hP.isoPullback.hom ≫ pullback.fst _ _ =
      (pullback.fst (exTowerUnit Y) (exTowerMap f)).app 0 := by
    rw [hP.isoPullback_hom_fst]
    change colimit.ι _ 0 ≫ colimMap _ ≫ _ = _
    rw [ι_colimMap_assoc, ι_colimitConstIso_hom]
    exact Category.comp_id _
  have h₃ : colimit.ι (relTower f) 0 ≫ hP.isoPullback.hom ≫ pullback.snd _ _ =
      (pullback.snd (exTowerUnit Y) (exTowerMap f)).app 0 ≫ exInftyUnit.{u}.app X := by
    rw [hP.isoPullback_hom_snd]
    change colimit.ι _ 0 ≫ colimMap _ ≫ _ = _
    rw [ι_colimMap_assoc]
    exact congrArg (_ ≫ ·) (colimitObjIsoColimitCompEvaluation_ι_inv exTower.{u} 0 X)
  apply pullback.hom_ext
  · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine (congrArg (e₀.hom ≫ ·) (pullback.lift_fst _ _ _)).trans ?_
    exact ((Category.assoc _ _ _).trans h₁).trans h₂.symm
  · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
    refine (congrArg (e₀.hom ≫ ·) (pullback.lift_snd _ _ _)).trans ?_
    exact ((Category.assoc _ _ _).trans (pullbackObjIso_hom_comp_snd_assoc _ _ 0 _)).trans
      h₃.symm

end Atoms.Homotopical
