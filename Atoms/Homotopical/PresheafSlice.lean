import Atoms.ForMathlib.CategoryTheory.Comma.Presheaf.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.LiftingProperties.Over

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

def sliceForget (X : Aᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) ⥤ (Aᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow X).inverse ⋙ Over.forget X

def sliceForgetπ (X : Aᵒᵖ ⥤ Type v) :
    sliceForget X ⟶ (Functor.const _).obj X :=
  Functor.whiskerLeft (overEquivPresheafCostructuredArrow X).inverse (Over.forgetCocone X).ι

def sliceHom {X K L : Aᵒᵖ ⥤ Type v} (f : K ⟶ L) (l : L ⟶ X) :
    (overEquivPresheafCostructuredArrow X).functor.obj (Over.mk (f ≫ l)) ⟶
      (overEquivPresheafCostructuredArrow X).functor.obj (Over.mk l) :=
  (overEquivPresheafCostructuredArrow X).functor.map (Over.homMk f)

theorem sliceHom_comp {X K L M : Aᵒᵖ ⥤ Type v} (f : K ⟶ L) (g : L ⟶ M) (h : M ⟶ X) :
    sliceHom (f ≫ g) h =
      (overEquivPresheafCostructuredArrow X).functor.map
          (Over.isoMk (f := Over.mk ((f ≫ g) ≫ h)) (g := Over.mk (f ≫ g ≫ h))
            (Iso.refl K) (by simp)).hom ≫
        sliceHom f (g ≫ h) ≫ sliceHom g h := by
  simp only [sliceHom, ← Functor.map_comp]
  congr 1

def sliceYonedaOverIso (X : Aᵒᵖ ⥤ Type v) :
    yoneda ⋙ (overEquivPresheafCostructuredArrow X).inverse ≅
      CostructuredArrow.toOver yoneda X :=
  Functor.isoWhiskerRight (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow X).symm
      (overEquivPresheafCostructuredArrow X).inverse ≪≫
    Functor.isoWhiskerLeft (CostructuredArrow.toOver yoneda X)
      (overEquivPresheafCostructuredArrow X).unitIso.symm

def sliceForgetYonedaNatIso (X : Aᵒᵖ ⥤ Type v) :
    yoneda ⋙ sliceForget X ≅ CostructuredArrow.proj yoneda X ⋙ yoneda :=
  Functor.isoWhiskerRight (sliceYonedaOverIso X) (Over.forget X)

def sliceForgetYonedaIso {X : Aᵒᵖ ⥤ Type v} (x : CostructuredArrow yoneda X) :
    (sliceForget X).obj (yoneda.obj x) ≅ yoneda.obj x.left :=
  (sliceForgetYonedaNatIso X).app x

theorem sliceForgetYonedaIso_inv_comp_map_yoneda_map {X : Aᵒᵖ ⥤ Type v}
    {e e' : CostructuredArrow yoneda X} (h : e ⟶ e') :
    (sliceForgetYonedaIso e).inv ≫ (sliceForget X).map (yoneda.map h) =
      yoneda.map h.left ≫ (sliceForgetYonedaIso e').inv :=
  ((sliceForgetYonedaNatIso X).inv.naturality h).symm

noncomputable def sliceForgetAdjStar (X : Aᵒᵖ ⥤ Type v) :
    sliceForget X ⊣ Over.star X ⋙ (overEquivPresheafCostructuredArrow X).functor :=
  (overEquivPresheafCostructuredArrow X).symm.toAdjunction.comp (Over.forgetAdjStar X)

noncomputable def sliceStarObjEquiv (X K : Aᵒᵖ ⥤ Type v) (s : CostructuredArrow yoneda X) :
    ((Over.star X ⋙ (overEquivPresheafCostructuredArrow X).functor).obj K).obj (Opposite.op s) ≃
      K.obj (Opposite.op s.left) :=
  yonedaEquiv.symm.trans <| ((sliceForgetAdjStar X).homEquiv _ _).symm.trans <|
    ((sliceForgetYonedaIso s).homCongr (Iso.refl K)).trans yonedaEquiv

theorem sliceStarObjEquiv_apply (X K : Aᵒᵖ ⥤ Type v) (s : CostructuredArrow yoneda X) (x) :
    sliceStarObjEquiv X K s x = yonedaEquiv ((sliceForgetYonedaIso s).inv ≫
      ((sliceForgetAdjStar X).homEquiv _ _).symm (yonedaEquiv.symm x)) := by
  simp [sliceStarObjEquiv, Iso.homCongr_apply]

theorem sliceStarObjEquiv_naturality (X K : Aᵒᵖ ⥤ Type v) {s s' : CostructuredArrow yoneda X}
    (f : s' ⟶ s) (x) :
    sliceStarObjEquiv X K s'
        (((Over.star X ⋙ (overEquivPresheafCostructuredArrow X).functor).obj K).map f.op x) =
      K.map f.left.op (sliceStarObjEquiv X K s x) := by
  rw [sliceStarObjEquiv_apply, sliceStarObjEquiv_apply, yonedaEquiv_symm_map,
    Adjunction.homEquiv_naturality_left_symm, yonedaEquiv_naturality, Quiver.Hom.unop_op,
    reassoc_of% (sliceForgetYonedaIso_inv_comp_map_yoneda_map f)]

theorem sliceStarObjEquiv_naturality_right (X : Aᵒᵖ ⥤ Type v) {K K' : Aᵒᵖ ⥤ Type v}
    (k : K ⟶ K') (s : CostructuredArrow yoneda X) (x) :
    sliceStarObjEquiv X K' s
        (((Over.star X ⋙ (overEquivPresheafCostructuredArrow X).functor).map k).app _ x) =
      k.app _ (sliceStarObjEquiv X K s x) := by
  rw [sliceStarObjEquiv_apply, sliceStarObjEquiv_apply, ← yonedaEquiv_symm_naturality_right,
    Adjunction.homEquiv_naturality_right_symm, ← yonedaEquiv_comp, Category.assoc]

noncomputable def sliceStarIso (X : Aᵒᵖ ⥤ Type v) :
    Over.star X ⋙ (overEquivPresheafCostructuredArrow X).functor ≅
      (Functor.whiskeringLeft _ _ (Type v)).obj (CostructuredArrow.proj yoneda X).op :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun s => (sliceStarObjEquiv X K s.unop).toIso)
      (fun {s s'} f => by
        ext x
        exact sliceStarObjEquiv_naturality X K f.unop x))
    (fun {K K'} k => by
      ext s x
      exact sliceStarObjEquiv_naturality_right X k s.unop x)

noncomputable def sliceForgetAdjunction (X : Aᵒᵖ ⥤ Type v) :
    sliceForget X ⊣
      (Functor.whiskeringLeft _ _ (Type v)).obj (CostructuredArrow.proj yoneda X).op :=
  (sliceForgetAdjStar X).ofNatIsoRight (sliceStarIso X)

instance preservesColimitsOfSize_sliceForget (X : Aᵒᵖ ⥤ Type v) :
    PreservesColimitsOfSize.{v, v} (sliceForget X) :=
  (sliceForgetAdjunction X).leftAdjoint_preservesColimits

instance faithful_sliceForget (X : Aᵒᵖ ⥤ Type v) : (sliceForget X).Faithful :=
  inferInstanceAs (((overEquivPresheafCostructuredArrow X).inverse ⋙ Over.forget X).Faithful)

def sliceForgetMapSliceHomIso {X K L : Aᵒᵖ ⥤ Type v} (f : K ⟶ L) (l : L ⟶ X) :
    Arrow.mk ((sliceForget X).map (sliceHom f l)) ≅ Arrow.mk f :=
  Arrow.isoMk
    ((Over.forget X).mapIso ((overEquivPresheafCostructuredArrow X).unitIso.app
      (Over.mk (f ≫ l)))).symm
    ((Over.forget X).mapIso ((overEquivPresheafCostructuredArrow X).unitIso.app
      (Over.mk l))).symm
    (by
      have h := congrArg (Over.forget X).map
        ((overEquivPresheafCostructuredArrow X).unitIso.inv.naturality
          (Over.homMk (U := Over.mk (f ≫ l)) (V := Over.mk l) f))
      simp only [Functor.map_comp] at h
      exact h.symm)

def sliceOverIso {X : Aᵒᵖ ⥤ Type v} {Y : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v}
    {h : (sliceForget X).obj Y ⟶ X} (hh : h = (sliceForgetπ X).app Y) :
    Over.mk h ≅ (overEquivPresheafCostructuredArrow X).inverse.obj Y :=
  Over.isoMk (Iso.refl _) (by subst hh; exact Category.id_comp _)

def sliceHomSliceForgetIso {X : Aᵒᵖ ⥤ Type v}
    {Y Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v} (g : Y ⟶ Z) :
    Arrow.mk (sliceHom ((sliceForget X).map g) ((sliceForgetπ X).app Z)) ≅ Arrow.mk g :=
  Arrow.isoMk
    ((overEquivPresheafCostructuredArrow X).functor.mapIso
        (sliceOverIso (by simp)) ≪≫
      (overEquivPresheafCostructuredArrow X).counitIso.app Y)
    ((overEquivPresheafCostructuredArrow X).functor.mapIso (sliceOverIso rfl) ≪≫
      (overEquivPresheafCostructuredArrow X).counitIso.app Z)
    (by
      have h := (overEquivPresheafCostructuredArrow X).counitIso.hom.naturality g
      have h' : Over.homMk (U := Over.mk ((sliceForget X).map g ≫ (sliceForgetπ X).app Z))
          (V := Over.mk ((sliceForgetπ X).app Z)) ((sliceForget X).map g) ≫
            (sliceOverIso rfl).hom =
          (sliceOverIso (by simp)).hom ≫
            (overEquivPresheafCostructuredArrow X).inverse.map g := by
        ext
        simp [sliceOverIso, sliceForget]
      change (overEquivPresheafCostructuredArrow X).functor.map
            (sliceOverIso (by simp)).hom ≫
          (overEquivPresheafCostructuredArrow X).counitIso.hom.app Y ≫ g =
        (overEquivPresheafCostructuredArrow X).functor.map
            (Over.homMk (U := Over.mk ((sliceForget X).map g ≫ (sliceForgetπ X).app Z))
              (V := Over.mk ((sliceForgetπ X).app Z)) ((sliceForget X).map g)) ≫
          (overEquivPresheafCostructuredArrow X).functor.map (sliceOverIso rfl).hom ≫
          (overEquivPresheafCostructuredArrow X).counitIso.hom.app Z
      rw [← Functor.map_comp_assoc, h', Functor.map_comp_assoc]
      exact congrArg _ h.symm)

instance preservesLimitsOfShape_walkingCospan_sliceForget (X : Aᵒᵖ ⥤ Type v) :
    PreservesLimitsOfShape WalkingCospan (sliceForget X) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((overEquivPresheafCostructuredArrow X).inverse ⋙ Over.forget X))

instance reflectsLimitsOfShape_walkingCospan_sliceForget (X : Aᵒᵖ ⥤ Type v) :
    ReflectsLimitsOfShape WalkingCospan (sliceForget X) :=
  inferInstanceAs (ReflectsLimitsOfShape WalkingCospan
    ((overEquivPresheafCostructuredArrow X).inverse ⋙ Over.forget X))

instance reflectsColimitsOfSize_sliceForget (X : Aᵒᵖ ⥤ Type v) :
    ReflectsColimitsOfSize.{v, v} (sliceForget X) :=
  inferInstanceAs (ReflectsColimitsOfSize.{v, v}
    ((overEquivPresheafCostructuredArrow X).inverse ⋙ Over.forget X))

theorem isPullback_sliceForget_map_iff {X : Aᵒᵖ ⥤ Type v}
    {P Y Z W : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v}
    {fst : P ⟶ Y} {snd : P ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W} :
    IsPullback ((sliceForget X).map fst) ((sliceForget X).map snd) ((sliceForget X).map f)
        ((sliceForget X).map g) ↔ IsPullback fst snd f g :=
  ⟨fun h ↦ h.of_map_of_faithful (sliceForget X), fun h ↦ h.map (sliceForget X)⟩

theorem isPushout_sliceForget_map_iff {X : Aᵒᵖ ⥤ Type v}
    {Z Y₁ Y₂ P : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v}
    {f : Z ⟶ Y₁} {g : Z ⟶ Y₂} {inl : Y₁ ⟶ P} {inr : Y₂ ⟶ P} :
    IsPushout ((sliceForget X).map f) ((sliceForget X).map g) ((sliceForget X).map inl)
        ((sliceForget X).map inr) ↔ IsPushout f g inl inr :=
  ⟨fun h ↦ h.of_map_of_faithful (sliceForget X), fun h ↦ h.map (sliceForget X)⟩

theorem hasLiftingProperty_of_sliceForget {X : Aᵒᵖ ⥤ Type v}
    {Y Z Y' Z' : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v} (g : Y ⟶ Z) (p : Y' ⟶ Z')
    [h : HasLiftingProperty ((sliceForget X).map g) ((sliceForget X).map p)] :
    HasLiftingProperty g p := by
  have : HasLiftingProperty ((overEquivPresheafCostructuredArrow X).inverse.map g).left
      ((overEquivPresheafCostructuredArrow X).inverse.map p).left := h
  have : HasLiftingProperty ((overEquivPresheafCostructuredArrow X).inverse.map g)
      ((overEquivPresheafCostructuredArrow X).inverse.map p) := HasLiftingProperty.over _ _
  have : HasLiftingProperty
      ((overEquivPresheafCostructuredArrow X).functor.map
        ((overEquivPresheafCostructuredArrow X).inverse.map g)) p :=
    ((overEquivPresheafCostructuredArrow X).toAdjunction.hasLiftingProperty_iff _ _).2 this
  exact HasLiftingProperty.of_arrow_iso_left (hip := this)
    (Arrow.isoOfNatIso (overEquivPresheafCostructuredArrow X).counitIso (Arrow.mk g)) p

theorem hasLift_of_sliceHom {X K L : Aᵒᵖ ⥤ Type v}
    {Y' Z' : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v} {i : K ⟶ L} {p : Y' ⟶ Z'}
    {a : K ⟶ (sliceForget X).obj Y'} {b : L ⟶ (sliceForget X).obj Z'}
    (sq : CommSq a i ((sliceForget X).map p) b)
    [h : HasLiftingProperty (sliceHom i (b ≫ (sliceForgetπ X).app Z')) p] : sq.HasLift := by
  have hπ : (sliceForget X).map p ≫ (sliceForgetπ X).app Z' = (sliceForgetπ X).app Y' := by
    simp
  let i' : Over.mk (i ≫ b ≫ (sliceForgetπ X).app Z') ⟶ Over.mk (b ≫ (sliceForgetπ X).app Z') :=
    Over.homMk i
  have : HasLiftingProperty i' ((overEquivPresheafCostructuredArrow X).inverse.map p) :=
    ((overEquivPresheafCostructuredArrow X).toAdjunction.hasLiftingProperty_iff i' p).1 h
  let a' : Over.mk (i ≫ b ≫ (sliceForgetπ X).app Z') ⟶
      (overEquivPresheafCostructuredArrow X).inverse.obj Y' :=
    Over.homMk a (by
      change a ≫ (sliceForgetπ X).app Y' = i ≫ b ≫ (sliceForgetπ X).app Z'
      rw [← sq.w_assoc, hπ])
  let b' : Over.mk (b ≫ (sliceForgetπ X).app Z') ⟶
      (overEquivPresheafCostructuredArrow X).inverse.obj Z' :=
    Over.homMk b rfl
  have sq' : CommSq a' i' ((overEquivPresheafCostructuredArrow X).inverse.map p) b' :=
    ⟨Over.OverMorphism.ext sq.w⟩
  exact ⟨⟨{ l := sq'.lift.left
            fac_left := congrArg CommaMorphism.left sq'.fac_left
            fac_right := congrArg CommaMorphism.left sq'.fac_right }⟩⟩

theorem rlp_inverseImage_sliceForget_of_respectsIso (X : Aᵒᵖ ⥤ Type v)
    (P : MorphismProperty (Aᵒᵖ ⥤ Type v)) [P.RespectsIso] :
    (P.inverseImage (sliceForget X)).rlp = P.rlp.inverseImage (sliceForget X) := by
  ext Y' Z' p
  constructor
  · intro hp K L i hi
    constructor
    intro a b sq
    have : HasLiftingProperty (sliceHom i (b ≫ (sliceForgetπ X).app Z')) p :=
      hp _ ((P.arrow_mk_iso_iff (sliceForgetMapSliceHomIso i _)).2 hi)
    exact hasLift_of_sliceHom sq
  · intro hp Y Z g hg
    have := hp _ hg
    exact hasLiftingProperty_of_sliceForget g p

theorem llp_inverseImage_sliceForget (X : Aᵒᵖ ⥤ Type v)
    (P : MorphismProperty (Aᵒᵖ ⥤ Type v)) [P.IsStableUnderBaseChange] :
    (P.inverseImage (sliceForget X)).llp = P.llp.inverseImage (sliceForget X) := by
  ext Y Z i
  constructor
  · intro hi Y' Z' q hq
    constructor
    intro a b sq
    have hpb : P (pullback.snd q b) := P.of_isPullback (IsPullback.of_hasPullback q b) hq
    let l := (sliceForgetπ X).app Z
    have : HasLiftingProperty i (sliceHom (pullback.snd q b) l) :=
      hi _ ((P.arrow_mk_iso_iff (sliceForgetMapSliceHomIso _ _)).2 hpb)
    let q' : Over.mk (pullback.snd q b ≫ l) ⟶ Over.mk l := Over.homMk (pullback.snd q b)
    have : HasLiftingProperty ((overEquivPresheafCostructuredArrow X).inverse.map i) q' :=
      ((overEquivPresheafCostructuredArrow X).symm.toAdjunction.hasLiftingProperty_iff i q').2
        this
    have hπ : (sliceForget X).map i ≫ l = (sliceForgetπ X).app Y := by simp [l]
    let a' : (overEquivPresheafCostructuredArrow X).inverse.obj Y ⟶
        Over.mk (pullback.snd q b ≫ l) :=
      Over.homMk (pullback.lift a ((sliceForget X).map i) sq.w)
        ((pullback.lift_snd_assoc a ((sliceForget X).map i) sq.w l).trans hπ)
    let b' : (overEquivPresheafCostructuredArrow X).inverse.obj Z ⟶ Over.mk l :=
      Over.homMk (𝟙 _) (Category.id_comp _)
    have sq' : CommSq a' ((overEquivPresheafCostructuredArrow X).inverse.map i) q' b' :=
      ⟨Over.OverMorphism.ext
        ((pullback.lift_snd a ((sliceForget X).map i) sq.w).trans (Category.comp_id _).symm)⟩
    let ℓ : (sliceForget X).obj Z ⟶ pullback q b := sq'.lift.left
    have hl : (sliceForget X).map i ≫ ℓ = pullback.lift a ((sliceForget X).map i) sq.w :=
      congrArg CommaMorphism.left sq'.fac_left
    have hr : ℓ ≫ pullback.snd q b = 𝟙 _ := congrArg CommaMorphism.left sq'.fac_right
    exact ⟨⟨{ l := ℓ ≫ pullback.fst q b
              fac_left := by rw [← Category.assoc, hl, pullback.lift_fst]
              fac_right := by
                rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp] }⟩⟩
  · intro hi Y' Z' p hp
    have := hi _ hp
    exact hasLiftingProperty_of_sliceForget i p

theorem monomorphisms_eq_inverseImage_sliceForget (X : Aᵒᵖ ⥤ Type v) :
    MorphismProperty.monomorphisms ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) =
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).inverseImage (sliceForget X) := by
  ext Y Z g
  exact ((sliceForget X).mono_map_iff_mono g).symm

end Atoms.Homotopical
