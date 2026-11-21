import Atoms.Homotopical.Localizer.AccessibleModel
import Atoms.ForMathlib.CategoryTheory.Limits.VanKampen
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Limits

open CategoryTheory Limits MorphismProperty MonoidalCategory HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v w' v'

variable {A : Type v} [SmallCategory A]

section Lift

variable {K L E B : Aᵒᵖ ⥤ Type (max w v)}

noncomputable def baseChangeLift (c : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) {u : K ⟶ B}
    (hu : c ≫ b = u) : pullback u p ⟶ pullback b p :=
  pullback.lift (pullback.fst u p ≫ c) (pullback.snd u p)
    (by rw [Category.assoc, hu, pullback.condition])

end Lift

noncomputable def baseChangeMap {K L E B : Aᵒᵖ ⥤ Type (max w v)}
    (f : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) :
    pullback (f ≫ b) p ⟶ pullback b p :=
  baseChangeLift f b p rfl

def baseChangeClass (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) {E B : Aᵒᵖ ⥤ Type (max w v)}
    (p : E ⟶ B) :
    MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  fun _ L f ↦ ∀ b : L ⟶ B, V (baseChangeMap f b p)

def fibrantBaseChangeClass (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) :
    MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  fun _ _ f ↦ ∀ {E B : Aᵒᵖ ⥤ Type (max w v)} (q : E ⟶ B),
    (MorphismProperty.monomorphisms _ ⊓ V).rlp q →
      (MorphismProperty.monomorphisms _ ⊓ V).rlp (terminal.from B) → baseChangeClass V q f

def LocallyConstant (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) {E B : Aᵒᵖ ⥤ Type (max w v)}
    (p : E ⟶ B) : Prop :=
  ∀ (a a' : A) (f : a ⟶ a') (b : uliftYoneda.{w}.obj a' ⟶ B),
    V (baseChangeMap (uliftYoneda.{w}.map f) b p)

def WeakFibration (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) {E B : Aᵒᵖ ⥤ Type (max w v)}
    (p : E ⟶ B) :
    Prop :=
  ∀ {K L : Aᵒᵖ ⥤ Type (max w v)} (f : K ⟶ L) (b : L ⟶ B), V f → V (baseChangeMap f b p)

class IsRightProper (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) : Prop where
  weakFibration_of_rlp {E B : Aᵒᵖ ⥤ Type (max w v)} (p : E ⟶ B) :
    (MorphismProperty.monomorphisms _ ⊓ V).rlp p → WeakFibration V p

theorem weakFibration_iff_le_baseChangeClass (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    {E B : Aᵒᵖ ⥤ Type (max w v)} (p : E ⟶ B) : WeakFibration V p ↔ V ≤ baseChangeClass V p :=
  ⟨fun h _ _ f hf b ↦ h f b hf, fun h _ _ f b hf ↦ h f hf b⟩

section Lift

variable {K L E B : Aᵒᵖ ⥤ Type (max w v)}

@[reassoc (attr := simp)]
theorem baseChangeLift_fst (c : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) {u : K ⟶ B}
    (hu : c ≫ b = u) : baseChangeLift c b p hu ≫ pullback.fst b p = pullback.fst u p ≫ c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeLift_snd (c : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) {u : K ⟶ B}
    (hu : c ≫ b = u) : baseChangeLift c b p hu ≫ pullback.snd b p = pullback.snd u p :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMap_fst (f : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) :
    baseChangeMap f b p ≫ pullback.fst b p = pullback.fst (f ≫ b) p ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMap_snd (f : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) :
    baseChangeMap f b p ≫ pullback.snd b p = pullback.snd (f ≫ b) p :=
  pullback.lift_snd _ _ _

theorem isPullback_baseChangeLift (c : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) {u : K ⟶ B}
    (hu : c ≫ b = u) :
    IsPullback (baseChangeLift c b p hu) (pullback.fst u p) (pullback.fst b p) c := by
  subst hu
  refine IsPullback.of_right ?_ (baseChangeLift_fst c b p rfl) (IsPullback.of_hasPullback b p).flip
  rw [baseChangeLift_snd]
  exact (IsPullback.of_hasPullback (c ≫ b) p).flip

theorem isPullback_baseChangeMap (f : K ⟶ L) (b : L ⟶ B) (p : E ⟶ B) :
    IsPullback (baseChangeMap f b p) (pullback.fst (f ≫ b) p) (pullback.fst b p) f :=
  isPullback_baseChangeLift f b p rfl

theorem baseChangeLift_mem_iff (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) (c : K ⟶ L) (b : L ⟶ B)
    (p : E ⟶ B) {u u' : K ⟶ B} (hu : c ≫ b = u) (hu' : c ≫ b = u') :
    V (baseChangeLift c b p hu) ↔ V (baseChangeLift c b p hu') := by
  subst hu
  subst hu'
  exact Iff.rfl

instance mono_baseChangeLift (c : K ⟶ L) [Mono c] (b : L ⟶ B) (p : E ⟶ B) {u : K ⟶ B}
    (hu : c ≫ b = u) : Mono (baseChangeLift c b p hu) :=
  (isPullback_baseChangeLift c b p hu).mono_fst_of_mono

instance mono_baseChangeMap (f : K ⟶ L) [Mono f] (b : L ⟶ B) (p : E ⟶ B) :
    Mono (baseChangeMap f b p) :=
  mono_baseChangeLift f b p rfl

end Lift

section Sorites

variable {E B : Aᵒᵖ ⥤ Type (max w v)}

theorem baseChangeMap_comp_mem_iff (V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) (p : E ⟶ B)
    {X Y Z : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (g : Y ⟶ Z) (b : Z ⟶ B) :
    V (baseChangeMap (f ≫ g) b p) ↔ V (baseChangeMap f (g ≫ b) p ≫ baseChangeMap g b p) := by
  have : baseChangeMap f (g ≫ b) p ≫ baseChangeMap g b p =
      baseChangeLift (f ≫ g) b p (Category.assoc f g b) := by
    apply pullback.hom_ext <;> simp
  rw [this]
  exact baseChangeLift_mem_iff V (f ≫ g) b p rfl _

theorem baseChangeMap_mem_iff_of_iso {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [V.RespectsIso]
    {K L K' L' : Aᵒᵖ ⥤ Type (max w v)} (f : K ⟶ L) (f' : K' ⟶ L') (eK : K ≅ K') (eL : L ≅ L')
    (w : f ≫ eL.hom = eK.hom ≫ f') (b : L ⟶ B) (p : E ⟶ B) :
    V (baseChangeMap f b p) ↔ V (baseChangeMap f' (eL.inv ≫ b) p) := by
  have := (isPullback_baseChangeMap eL.hom (eL.inv ≫ b) p).isIso_fst_of_isIso
  have := (isPullback_baseChangeMap eK.hom (f' ≫ eL.inv ≫ b) p).isIso_fst_of_isIso
  have h : V (baseChangeMap f (eL.hom ≫ eL.inv ≫ b) p) ↔ V (baseChangeMap f' (eL.inv ≫ b) p) := by
    rw [← V.cancel_right_of_respectsIso _ (baseChangeMap eL.hom (eL.inv ≫ b) p),
      ← baseChangeMap_comp_mem_iff V p, w, baseChangeMap_comp_mem_iff V p,
      V.cancel_left_of_respectsIso]
  rwa [eL.hom_inv_id_assoc] at h

theorem locallyConstant_iff_yoneda {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [V.RespectsIso]
    {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B) :
    LocallyConstant V p ↔
      ∀ (a a' : A) (f : a ⟶ a') (b : yoneda.obj a' ⟶ B),
        V (baseChangeMap.{v, v} (yoneda.map f) b p) := by
  let e := uliftYonedaIsoYoneda.{v, v} (C := A)
  refine ⟨fun h a a' f b ↦ ?_, fun h a a' f b ↦ ?_⟩
  · have := (baseChangeMap_mem_iff_of_iso (uliftYoneda.{v}.map f) (yoneda.map f) (e.app a)
      (e.app a') (e.hom.naturality f) ((e.app a').hom ≫ b) p).1 (h a a' f _)
    rwa [Iso.inv_hom_id_assoc] at this
  · exact (baseChangeMap_mem_iff_of_iso (uliftYoneda.{v}.map f) (yoneda.map f) (e.app a)
      (e.app a') (e.hom.naturality f) b p).2 (h a a' f _)

theorem baseChangeClass_comp_iff {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.HasTwoOutOfThreeProperty] {E B : Aᵒᵖ ⥤ Type (max w v)} (p : E ⟶ B)
    {X Y Z : Aᵒᵖ ⥤ Type (max w v)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : baseChangeClass V p f) :
    baseChangeClass V p (f ≫ g) ↔ baseChangeClass V p g :=
  ⟨fun h b ↦ V.of_precomp _ _ (hf (g ≫ b)) ((baseChangeMap_comp_mem_iff V p f g b).1 (h b)),
    fun h b ↦ (baseChangeMap_comp_mem_iff V p f g b).2 (V.comp_mem _ _ (hf (g ≫ b)) (h b))⟩

theorem IsALocalizer.rlp_monomorphisms_le_baseChangeClass
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] (p : E ⟶ B) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp ≤ baseChangeClass V p :=
  fun _ _ _ hf b ↦ hV.rlp_monomorphisms_le _
    ((MorphismProperty.monomorphisms _).rlp.of_isPullback
      (isPullback_baseChangeLift _ b p rfl).flip hf)

theorem IsALocalizer.le_baseChangeClass {V W : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] [hW : IsALocalizer W] {E B : Aᵒᵖ ⥤ Type (max w v)} (p : E ⟶ B)
    (h : MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ W ≤ baseChangeClass V p) :
    W ≤ baseChangeClass V p := by
  intro X Y w hw
  let F := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp w
  have hi : W F.i :=
    W.of_postcomp _ _ (hW.rlp_monomorphisms_le _ F.hp) (by rw [F.fac]; exact hw)
  rw [← F.fac]
  exact (baseChangeClass_comp_iff p _ _ (h _ ⟨F.hi, hi⟩)).2
    (hV.rlp_monomorphisms_le_baseChangeClass p _ F.hp)

theorem baseChangeClass_of_retract {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.IsStableUnderRetracts] (p : E ⟶ B) {X Y X' Y' : Aᵒᵖ ⥤ Type (max w v)} {f : X ⟶ Y}
    {g : X' ⟶ Y'} (R : RetractArrow f g) (hg : baseChangeClass V p g) :
    baseChangeClass V p f := by
  intro b
  have hrr : R.i.right ≫ R.r.right ≫ b = b := by
    rw [← Category.assoc, R.retract_right]
    exact Category.id_comp b
  have hi : R.i.left ≫ g ≫ R.r.right ≫ b = f ≫ b := by
    rw [R.i_w_assoc, hrr]
  have hr : R.r.left ≫ f ≫ b = g ≫ R.r.right ≫ b := by rw [R.r_w_assoc]
  let il : pullback (f ≫ b) p ⟶ pullback (g ≫ R.r.right ≫ b) p :=
    pullback.lift (pullback.fst _ _ ≫ R.i.left) (pullback.snd _ _)
      (by rw [Category.assoc, hi, pullback.condition])
  let ir : pullback b p ⟶ pullback (R.r.right ≫ b) p :=
    pullback.lift (pullback.fst _ _ ≫ R.i.right) (pullback.snd _ _)
      (by rw [Category.assoc, hrr, pullback.condition])
  let rl : pullback (g ≫ R.r.right ≫ b) p ⟶ pullback (f ≫ b) p :=
    pullback.lift (pullback.fst _ _ ≫ R.r.left) (pullback.snd _ _)
      (by rw [Category.assoc, hr, pullback.condition])
  let rr : pullback (R.r.right ≫ b) p ⟶ pullback b p :=
    pullback.lift (pullback.fst _ _ ≫ R.r.right) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  let R' : RetractArrow (baseChangeMap.{w} f b p) (baseChangeMap.{w} g (R.r.right ≫ b) p) :=
    { i := Arrow.homMk il ir (by
        apply pullback.hom_ext <;>
          simp [il, ir, R.i_w, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc])
      r := Arrow.homMk rl rr (by
        apply pullback.hom_ext <;>
          simp [rl, rr, R.r_w, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc])
      retract := by
        ext : 1
        all_goals dsimp; apply pullback.hom_ext <;> simp [il, ir, rl, rr,
          pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc] }
  exact V.of_retract R' (hg _)

theorem baseChangeClass_le_of_retract {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.IsStableUnderRetracts] {X Y Z T : Aᵒᵖ ⥤ Type (max w v)} {p : X ⟶ Y} {q : Z ⟶ T}
    (R : RetractArrow p q) : baseChangeClass V q ≤ baseChangeClass V p := by
  intro K L f hf b
  have hi : ∀ {M : Aᵒᵖ ⥤ Type (max w v)} (m : M ⟶ Y), pullback.snd m p ≫ R.i.left ≫ q =
      pullback.fst m p ≫ m ≫ R.i.right := fun m ↦ by
    rw [R.i_w, ← pullback.condition_assoc]
  have hr : ∀ {M : Aᵒᵖ ⥤ Type (max w v)} (m : M ⟶ Y) (n : M ⟶ T) (hn : m ≫ R.i.right = n),
      pullback.snd n q ≫ R.r.left ≫ p = pullback.fst n q ≫ m := fun m n hn ↦ by
    rw [R.r_w, ← pullback.condition_assoc, ← hn, Category.assoc, R.retract_right,
      Category.comp_id]
  let il : pullback (f ≫ b) p ⟶ pullback (f ≫ b ≫ R.i.right) q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ R.i.left)
      (by simp only [Category.assoc, hi])
  let ir : pullback b p ⟶ pullback (b ≫ R.i.right) q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ R.i.left)
      (by rw [Category.assoc, hi])
  let rl : pullback (f ≫ b ≫ R.i.right) q ⟶ pullback (f ≫ b) p :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ R.r.left)
      (by rw [Category.assoc, hr (f ≫ b) _ (Category.assoc _ _ _)])
  let rr : pullback (b ≫ R.i.right) q ⟶ pullback b p :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ R.r.left)
      (by rw [Category.assoc, hr b _ rfl])
  let R' : RetractArrow (baseChangeMap.{w} f b p) (baseChangeMap.{w} f (b ≫ R.i.right) q) :=
    { i := Arrow.homMk il ir (by
        apply pullback.hom_ext <;>
          simp [il, ir, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc])
      r := Arrow.homMk rl rr (by
        apply pullback.hom_ext <;>
          simp [rl, rr, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc])
      retract := by
        ext : 1
        all_goals dsimp; apply pullback.hom_ext <;> simp [il, ir, rl, rr,
          pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc] }
  exact V.of_retract R' (hf _)

theorem baseChangeClass_le_of_isPullback {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.RespectsIso]
    {E' B' : Aᵒᵖ ⥤ Type (max w v)} {p : E ⟶ B} {q : E' ⟶ B'} {g : E' ⟶ E} {j : B' ⟶ B}
    (h : IsPullback g q p j) : baseChangeClass V p ≤ baseChangeClass V q := by
  intro K L f hf b
  have hb : IsPullback (pullback.fst b q) (pullback.snd b q ≫ g) (b ≫ j) p :=
    ((IsPullback.of_hasPullback b q).flip.paste_horiz h).flip
  exact (mem_iff_of_isPullback V (isPullback_baseChangeMap f (b ≫ j) p)
    (isPullback_baseChangeMap f b q) hb.isoPullback (hb.isoPullback_hom_fst)).2 (hf _)

end Sorites

theorem isRightProper_inverseImage_of_rlp_map {B : Type v'} [SmallCategory B]
    (F : (Aᵒᵖ ⥤ Type (max w v)) ⥤ (Bᵒᵖ ⥤ Type (max w' v')))
    [PreservesLimitsOfShape WalkingCospan F]
    (V : MorphismProperty (Bᵒᵖ ⥤ Type (max w' v'))) [V.RespectsIso] [hP : IsRightProper V]
    (hF : ∀ {E B' : Aᵒᵖ ⥤ Type (max w v)} (q : E ⟶ B'),
      (MorphismProperty.monomorphisms _ ⊓ V.inverseImage F).rlp q →
        (MorphismProperty.monomorphisms _ ⊓ V).rlp (F.map q)) :
    IsRightProper (V.inverseImage F) := by
  refine ⟨fun {E B'} q hq ↦ ?_⟩
  intro K L f b hf
  have hW := hP.weakFibration_of_rlp (F.map q) (hF q hq) (F.map f) (F.map b) hf
  exact (mem_iff_of_isPullback V (isPullback_baseChangeMap (F.map f) (F.map b) (F.map q))
    ((isPullback_baseChangeMap f b q).map F) (PreservesPullback.iso F b q)
    (PreservesPullback.iso_hom_fst F b q)).2 hW

section Saturation

variable {E B : Aᵒᵖ ⥤ Type (max w v)}

theorem IsALocalizer.baseChangeClass_of_isPushout {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [IsALocalizer V] (p : E ⟶ B) {X₀ X₁ X₂ X₃ : Aᵒᵖ ⥤ Type (max w v)} {g : X₀ ⟶ X₂}
    {f : X₀ ⟶ X₁} {f' : X₂ ⟶ X₃} {g' : X₁ ⟶ X₃} (sq : IsPushout g f f' g') [Mono f]
    (hf : baseChangeClass V p f) : baseChangeClass V p f' := by
  intro b
  have hu : g ≫ f' ≫ b = f ≫ g' ≫ b := by rw [reassoc_of% sq.w]
  have hcube := (Adhesive.van_kampen' sq) (baseChangeLift g (f' ≫ b) p hu)
    (baseChangeMap f (g' ≫ b) p) (baseChangeMap f' b p) (baseChangeMap g' b p)
    (pullback.fst _ _) (pullback.fst _ _) (pullback.fst _ _) (pullback.fst _ _)
    (isPullback_baseChangeLift g (f' ≫ b) p hu) (isPullback_baseChangeMap f (g' ≫ b) p)
    (isPullback_baseChangeMap f' b p).toCommSq (isPullback_baseChangeMap g' b p).toCommSq
    ⟨by apply pullback.hom_ext <;> simp [sq.w]⟩
  have hpo := hcube.2 ⟨isPullback_baseChangeMap f' b p, isPullback_baseChangeMap g' b p⟩
  exact (MorphismProperty.of_isPushout (P := MorphismProperty.monomorphisms _ ⊓ V) hpo
    ⟨MorphismProperty.monomorphisms.infer_property _, hf (g' ≫ b)⟩).2

theorem IsALocalizer.baseChangeClass_of_transfiniteComposition
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [IsALocalizer V] (p : E ⟶ B) (J : Type (max w v))
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : Aᵒᵖ ⥤ Type (max w v)}
    {f : X ⟶ Y}
    (t : MorphismProperty.TransfiniteCompositionOfShape
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ baseChangeClass V p) J f) :
    baseChangeClass V p f := by
  intro b
  have hw : ∀ {j k : J} (g : j ⟶ k), t.F.map g ≫ t.incl.app k = t.incl.app j := fun g ↦
    (t.incl.naturality g).trans (by simp)
  have hwb : ∀ {j k : J} (g : j ⟶ k), t.F.map g ≫ t.incl.app k ≫ b = t.incl.app j ≫ b :=
    fun g ↦ by rw [reassoc_of% (hw g)]
  let G : J ⥤ Aᵒᵖ ⥤ Type (max w v) :=
    { obj j := pullback (t.incl.app j ≫ b) p
      map {j k} g := baseChangeLift.{w} (t.F.map g) (t.incl.app k ≫ b) p (hwb g)
      map_id j := by apply pullback.hom_ext <;> simp
      map_comp g g' := by apply pullback.hom_ext <;> simp }
  let α : G ⟶ t.F :=
    { app j := pullback.fst (t.incl.app j ≫ b) p
      naturality j k g := by simp [G] }
  let ι : G ⟶ (Functor.const J).obj (pullback b p) :=
    { app j := baseChangeLift (t.incl.app j) b p rfl
      naturality j k g := by apply pullback.hom_ext <;> simp [G, hw] }
  have h₁ : t.isoBot.hom ≫ f = t.incl.app ⊥ := (Iso.eq_inv_comp _).1 t.fac.symm
  have hbot : t.isoBot.hom ≫ f ≫ b = t.incl.app ⊥ ≫ b := by rw [← Category.assoc, h₁]
  have hbot' : t.isoBot.inv ≫ t.incl.app ⊥ ≫ b = f ≫ b := by
    rw [← Category.assoc, t.fac]
  let e : G.obj ⊥ ≅ pullback (f ≫ b) p :=
    { hom := baseChangeLift t.isoBot.hom (f ≫ b) p hbot
      inv := baseChangeLift t.isoBot.inv (t.incl.app ⊥ ≫ b) p hbot'
      hom_inv_id := by apply pullback.hom_ext <;> simp [G]
      inv_hom_id := by apply pullback.hom_ext <;> simp }
  have hcont : G.IsWellOrderContinuous := ⟨fun m hm ↦
    nonempty_isColimit_of_isPullback (t.F.isColimitOfIsWellOrderContinuous m hm)
      ((Set.principalSegIio m).cocone G) (Functor.whiskerLeft _ α) (α.app m)
      (fun j ↦ isPullback_baseChangeLift _ _ p (hwb _))⟩
  let t' :
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).TransfiniteCompositionOfShape J
      (baseChangeMap f b p) :=
    { F := G
      isoBot := e
      isWellOrderContinuous := hcont
      incl := ι
      isColimit := (nonempty_isColimit_of_isPullback t.isColimit (Cocone.mk _ ι) α
        (pullback.fst b p) (fun j ↦ isPullback_baseChangeLift _ _ p rfl)).some
      fac := by
        apply pullback.hom_ext <;>
          simp [e, ι, baseChangeMap, t.fac]
      map_mem j hj := by
        have : Mono (t.F.map (homOfLE (Order.le_succ j))) := (t.map_mem j hj).1
        change (MorphismProperty.monomorphisms _ ⊓ V) (baseChangeLift _ _ p (hwb _))
        exact ⟨MorphismProperty.monomorphisms.infer_property _,
          (baseChangeLift_mem_iff V _ _ p rfl _).1 ((t.map_mem j hj).2 _)⟩ }
  exact
    ((MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V).transfiniteCompositionsOfShape_le
    J _ ⟨t'⟩).2

theorem IsALocalizer.isSaturated_monomorphisms_inf_baseChangeClass
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsALocalizer V] {E B : Aᵒᵖ ⥤ Type (max w v)}
    (p : E ⟶ B) :
    IsSaturated.{max w v}
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ baseChangeClass V p) where
  isStableUnderCobaseChange := ⟨fun sq hf ↦ by
    have : Mono _ := hf.1
    exact ⟨MorphismProperty.of_isPushout (P := MorphismProperty.monomorphisms _) sq hf.1,
      hV.baseChangeClass_of_isPushout p sq hf.2⟩⟩
  isStableUnderRetracts := ⟨fun R hg ↦
    ⟨(MorphismProperty.monomorphisms _).of_retract R hg.1, baseChangeClass_of_retract p R hg.2⟩⟩
  isStableUnderTransfiniteComposition := ⟨fun J _ _ _ _ ↦ ⟨fun _ _ f ⟨t⟩ ↦
    ⟨(MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).transfiniteCompositionsOfShape_le J f
      ⟨t.ofLE inf_le_left⟩, hV.baseChangeClass_of_transfiniteComposition p J t⟩⟩⟩

end Saturation

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))

theorem weakEquivalences_baseChangeMap_of_deformation_retract
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {K L E B : Aᵒᵖ ⥤ Type (max w v)}
    (i : K ⟶ L) (d : 𝕀.DeformationRetract i)
    (p : E ⟶ B) (hp : 𝕀.naiveFibrations S p) (b : L ⟶ B) :
    𝕀.weakEquivalences S (baseChangeMap i b p) := by
  let P := pullback (i ≫ b) p
  let X := pullback b p
  let π := pullback.fst b p
  let j := baseChangeMap i b p
  let q := pullback.fst (i ≫ b) p
  have hπ : 𝕀.naiveFibrations S π :=
    (𝕀.naiveFibrations S).of_isPullback (IsPullback.of_hasPullback b p).flip hp
  have hsq : IsPullback j q π i := isPullback_baseChangeMap i b p
  have : Mono i := mono_of_mono_fac d.comp_retraction
  have : Mono j := hsq.mono_fst_of_mono
  have natσ : ∀ {M N : Aᵒᵖ ⥤ Type (max w v)} (m : M ⟶ N),
      𝕀.I.map m ≫ (𝕀.contraction).app N = (𝕀.contraction).app M ≫ m :=
    fun m ↦ (𝕀.contraction).naturality m
  have hc : (𝕀.endpoint false).app P ≫ (𝕀.contraction).app P ≫ j = j ≫ 𝟙 X := by
    rw [endpoint_app_contraction_app_assoc, Category.comp_id]
  have sq : CommSq (pushout.desc ((𝕀.contraction).app P ≫ j) (𝟙 X) hc)
      (𝕀.endpointBox false j) π (𝕀.I.map π ≫ d.homotopy) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_endpointBox_assoc, ← Functor.map_comp_assoc, hsq.w,
        Functor.map_comp_assoc, d.map_comp_homotopy, ← Functor.map_comp_assoc, natσ,
        Category.assoc, hsq.w]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_endpointBox_assoc, endpoint_naturality_assoc,
        d.endpoint_false_comp_homotopy, Category.id_comp, Category.comp_id]⟩
  obtain ⟨⟨⟨k, hkl, hkr⟩⟩⟩ :=
    (hπ _ ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem false j this)).sq_hasLift sq
  have hk₀ : (𝕀.endpoint false).app X ≫ k = 𝟙 X :=
    𝕀.endpoint_comp_eq_of_endpointBox_comp_eq false j hkl
  have hkj : 𝕀.I.map j ≫ k = (𝕀.contraction).app P ≫ j :=
    𝕀.map_comp_eq_of_endpointBox_comp_eq false j hkl
  have hkσ : 𝕀.I.map j ≫ k = 𝕀.I.map j ≫ (𝕀.contraction).app X := hkj.trans (natσ j).symm
  let s : X ⟶ P := hsq.lift ((𝕀.endpoint true).app X ≫ k) (π ≫ d.retraction) (by
    rw [Category.assoc, hkr, endpoint_naturality_assoc, d.endpoint_true_comp_homotopy,
      Category.assoc])
  have hs₁ : s ≫ j = (𝕀.endpoint true).app X ≫ k := hsq.lift_fst _ _ _
  have hs₂ : s ≫ q = π ≫ d.retraction := hsq.lift_snd _ _ _
  have hjs : j ≫ s = 𝟙 P := by
    refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hs₁, ← endpoint_naturality_assoc, hkj,
        endpoint_app_contraction_app_assoc, Category.id_comp]
    · rw [Category.assoc, hs₂, reassoc_of% hsq.w, d.comp_retraction, Category.comp_id,
        Category.id_comp]
  exact 𝕀.anodyne_le_weakEquivalences S hS _
    (𝕀.anodyne_of_deformation_retract S hS j ⟨s, k, hjs, hk₀, hs₁.symm, hkσ⟩)

end HomotopicalAlgebra.ExactCylinder
