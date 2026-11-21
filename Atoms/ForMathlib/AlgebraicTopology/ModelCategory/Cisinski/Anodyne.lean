import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Cylinder
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

universe w v u

variable {C : Type u} [Category.{v} C]

theorem exists_section_of_rlp_monomorphisms [HasInitial C] [HasStrictInitialObjects C]
    {X Y : C} (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  have := hp (initial.to Y) (initial.mono_from Y (initial.to Y))
  have sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := ⟨initial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

variable [HasBinaryCoproducts C]

namespace ExactCylinder

variable (𝕀 : ExactCylinder.{w} C)

def ElementaryHomotopy {X Y : C} (f g : X ⟶ Y) : Prop :=
  ∃ h : 𝕀.I.obj X ⟶ Y,
    (𝕀.endpoint false).app X ≫ h = f ∧ (𝕀.endpoint true).app X ≫ h = g

theorem exists_homotopy_of_rlp_monomorphisms {X Y : C} (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) :
    ∃ k : 𝕀.I.obj X ⟶ X, (𝕀.endpoint false).app X ≫ k = 𝟙 X ∧
      (𝕀.endpoint true).app X ≫ k = p ≫ s ∧ k ≫ p = 𝕀.contraction.app X ≫ p := by
  have := hp (𝕀.endpoints X) (MorphismProperty.monomorphisms.infer_property _)
  have sq : CommSq (coprod.desc (𝟙 X) (p ≫ s)) (𝕀.endpoints X) p
      (𝕀.contraction.app X ≫ p) := ⟨by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc_assoc, inl_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc,
        Category.id_comp]
    · rw [coprod.inr_desc_assoc, inr_endpoints_assoc, 𝕀.endpoint_app_contraction_app_assoc,
        Category.assoc, hs, Category.comp_id]⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← inl_endpoints, Category.assoc, sq.fac_left, coprod.inl_desc]
  · rw [← inr_endpoints, Category.assoc, sq.fac_left, coprod.inr_desc]

def Homotopic {X Y : C} (f g : X ⟶ Y) : Prop :=
  Relation.EqvGen (fun f' g' : X ⟶ Y ↦ 𝕀.ElementaryHomotopy f' g') f g

theorem elementaryHomotopy_precomp {X Y Z : C} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (h : 𝕀.ElementaryHomotopy g g') : 𝕀.ElementaryHomotopy (f ≫ g) (f ≫ g') := by
  obtain ⟨k, h₀, h₁⟩ := h
  refine ⟨𝕀.I.map f ≫ k, ?_, ?_⟩
  · rw [← Category.assoc, 𝕀.endpoint_naturality false f, Category.assoc, h₀]
  · rw [← Category.assoc, 𝕀.endpoint_naturality true f, Category.assoc, h₁]

theorem Homotopic.map {X Y X' Y' : C} {f g : X ⟶ Y} (F : (X ⟶ Y) → (X' ⟶ Y'))
    (hF : ∀ ⦃f g : X ⟶ Y⦄, 𝕀.ElementaryHomotopy f g → 𝕀.ElementaryHomotopy (F f) (F g))
    (h : 𝕀.Homotopic f g) : 𝕀.Homotopic (F f) (F g) := by
  induction h with
  | rel _ _ hab => exact Relation.EqvGen.rel _ _ (hF hab)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem homotopic_precomp {X Y Z : C} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (h : 𝕀.Homotopic g g') : 𝕀.Homotopic (f ≫ g) (f ≫ g') :=
  Homotopic.map 𝕀 (f ≫ ·) (fun _ _ ↦ 𝕀.elementaryHomotopy_precomp f) h

def homotopySetoid (X Y : C) : Setoid (X ⟶ Y) :=
  ⟨fun f g ↦ 𝕀.Homotopic f g, Relation.EqvGen.is_equivalence _⟩

def HomotopyClasses (X Y : C) : Type v :=
  Quotient (𝕀.homotopySetoid X Y)

def precompClasses {X Y : C} (f : X ⟶ Y) (Z : C) :
    𝕀.HomotopyClasses Y Z → 𝕀.HomotopyClasses X Z :=
  Quotient.map (sa := 𝕀.homotopySetoid Y Z) (sb := 𝕀.homotopySetoid X Z) (f ≫ ·)
    fun _ _ h ↦ 𝕀.homotopic_precomp f h

theorem precompClasses_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : C) :
    𝕀.precompClasses (f ≫ g) T = 𝕀.precompClasses f T ∘ 𝕀.precompClasses g T := by
  funext c
  induction c using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (Category.assoc f g a)

theorem precompClasses_id (X T : C) : 𝕀.precompClasses (𝟙 X) T = id := by
  funext c
  induction c using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (Category.id_comp a)

theorem elementaryHomotopy_refl {K T : C} (u : K ⟶ T) :
    𝕀.ElementaryHomotopy u u := by
  exact ⟨(𝕀.contraction).app K ≫ u, 𝕀.endpoint_app_contraction_app_assoc false u,
    𝕀.endpoint_app_contraction_app_assoc true u⟩

end ExactCylinder

variable [HasPushouts C]

structure IsAnodyneClass (𝕀 : ExactCylinder.{w} C) (S P : MorphismProperty C) :
    Prop where
  isSaturated : IsSaturated.{w} P
  generators_le : S ≤ P
  endpointBox_mem : ∀ (ε : Bool) {K X : C} (i : K ⟶ X), Mono i →
    P (𝕀.endpointBox ε i)
  bothBox_mem : ∀ {K X : C} (i : K ⟶ X), Mono i → P i → P (𝕀.bothBox i)

namespace ExactCylinder

variable (𝕀 : ExactCylinder.{w} C)

def anodyne (S : MorphismProperty C) : MorphismProperty C :=
  sInf {P | IsAnodyneClass 𝕀 S P}

theorem anodyne_iff (S : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    𝕀.anodyne S f ↔ ∀ P : MorphismProperty C, IsAnodyneClass 𝕀 S P → P f := by
  rw [anodyne, MorphismProperty.sInf_iff]
  simp only [Set.mem_ofPred_eq]

theorem anodyne_le (S P : MorphismProperty C) (h : IsAnodyneClass 𝕀 S P) :
    𝕀.anodyne S ≤ P :=
  fun _ _ f hf ↦ (𝕀.anodyne_iff S f).1 hf P h

instance isSaturated_anodyne (S : MorphismProperty C) :
    IsSaturated.{w} (𝕀.anodyne S) :=
  isSaturated_sInf _ fun _ hP ↦ hP.isSaturated

theorem isAnodyneClass_anodyne (S : MorphismProperty C) :
    IsAnodyneClass 𝕀 S (𝕀.anodyne S) where
  isSaturated := inferInstance
  generators_le _ _ f hf := (𝕀.anodyne_iff S f).2 fun _ hP ↦ hP.generators_le f hf
  endpointBox_mem := fun ε {_ _} i hi ↦
    (𝕀.anodyne_iff S _).2 fun _ hP ↦ hP.endpointBox_mem ε i hi
  bothBox_mem := fun {_ _} i hi hf ↦ (𝕀.anodyne_iff S _).2 fun P hP ↦
    hP.bothBox_mem i hi (𝕀.anodyne_le S P hP i hf)

theorem le_anodyne (S : MorphismProperty C) : S ≤ 𝕀.anodyne S :=
  (𝕀.isAnodyneClass_anodyne S).generators_le

theorem anodyne_mono {S T : MorphismProperty C} (h : S ≤ T) :
    𝕀.anodyne S ≤ 𝕀.anodyne T :=
  𝕀.anodyne_le S _
    { isSaturated := inferInstance
      generators_le := h.trans (𝕀.le_anodyne T)
      endpointBox_mem := (𝕀.isAnodyneClass_anodyne T).endpointBox_mem
      bothBox_mem := (𝕀.isAnodyneClass_anodyne T).bothBox_mem }

theorem anodyne_le_monomorphisms [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [IsSaturated.{w} (MorphismProperty.monomorphisms C)] (S : MorphismProperty C)
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.anodyne S ≤ MorphismProperty.monomorphisms C :=
  𝕀.anodyne_le S _
    { isSaturated := inferInstance
      generators_le := hS
      endpointBox_mem := fun ε {_ _} i hi ↦ 𝕀.mono_endpointBox ε i hi
      bothBox_mem := fun {_ _} i hi _ ↦ 𝕀.mono_bothBox i hi }

variable [HasTerminal C]

def IsFibrant (S : MorphismProperty C) (X : C) : Prop :=
  (𝕀.anodyne S).rlp (terminal.from X)

def weakEquivalences (S : MorphismProperty C) :
    MorphismProperty C :=
  fun _ _ f ↦ ∀ Z : C, 𝕀.IsFibrant S Z → Function.Bijective (𝕀.precompClasses f Z)

theorem weakEquivalences_eq_of_anodyne_eq {S T : MorphismProperty C}
    (h : 𝕀.anodyne S = 𝕀.anodyne T) : 𝕀.weakEquivalences S = 𝕀.weakEquivalences T := by
  unfold weakEquivalences IsFibrant
  rw [h]

abbrev trivialCofibrations (S : MorphismProperty C) :
    MorphismProperty C :=
  MorphismProperty.monomorphisms C ⊓ 𝕀.weakEquivalences S

abbrev naiveFibrations (S : MorphismProperty C) :
    MorphismProperty C :=
  (𝕀.anodyne S).rlp

abbrev fibrations (S : MorphismProperty C) : MorphismProperty C :=
  (𝕀.trivialCofibrations S).rlp

theorem isFibrant_iff_naiveFibrations (S : MorphismProperty C)
    (X : C) : 𝕀.IsFibrant S X ↔ 𝕀.naiveFibrations S (terminal.from X) :=
  Iff.rfl

variable (S : MorphismProperty C)

theorem exists_fac_of_isFibrant {T : C} (hT : 𝕀.IsFibrant S T)
    {K L : C} {j : K ⟶ L} (hj : 𝕀.anodyne S j) (k : K ⟶ T) :
    ∃ l : L ⟶ T, j ≫ l = k := by
  have := hT j hj
  have sq : CommSq k j (terminal.from T) (terminal.from L) :=
    ⟨Subsingleton.elim _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

theorem elementaryHomotopy_of_elementaryHomotopy_of_isFibrant {T : C}
    (hT : 𝕀.IsFibrant S T) {K : C} {u v w : K ⟶ T}
    (huv : 𝕀.ElementaryHomotopy u v) (huw : 𝕀.ElementaryHomotopy u w) :
    𝕀.ElementaryHomotopy v w := by
  obtain ⟨h, h₀, h₁⟩ := huv
  obtain ⟨k, k₀, k₁⟩ := huw
  obtain ⟨ψ, hψl, hψr⟩ := 𝕀.exists_map_coprod_comp K
  have hc : (𝕀.endpoint false).app (K ⨿ K) ≫ ψ ≫ coprod.desc h k =
      𝕀.endpoints K ≫ (𝕀.contraction).app K ≫ u := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc,
        ← Category.assoc (𝕀.I.map _), hψl,
        coprod.inl_desc, h₀, ← Category.assoc, 𝕀.inl_endpoints,
        𝕀.endpoint_app_contraction_app_assoc]
    · rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc,
        ← Category.assoc (𝕀.I.map _), hψr,
        coprod.inr_desc, k₀, ← Category.assoc, 𝕀.inr_endpoints,
        𝕀.endpoint_app_contraction_app_assoc]
  obtain ⟨H, hH⟩ := 𝕀.exists_fac_of_isFibrant S hT
    ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem false (𝕀.endpoints K) inferInstance)
    (pushout.desc (ψ ≫ coprod.desc h k) ((𝕀.contraction).app K ≫ u) hc)
  have hH₁ : 𝕀.I.map (𝕀.endpoints K) ≫ H = ψ ≫ coprod.desc h k :=
    𝕀.map_comp_eq_of_endpointBox_comp_eq false _ hH
  refine ⟨(𝕀.endpoint true).app (𝕀.I.obj K) ≫ H, ?_, ?_⟩
  · have e := (𝕀.inl_endpoints K).symm
    rw [← Category.assoc, ← 𝕀.endpoint_naturality, e, Functor.map_comp, Category.assoc,
      Category.assoc, hH₁, ← Category.assoc (𝕀.I.map _), hψl,
      coprod.inl_desc]
    exact h₁
  · have e := (𝕀.inr_endpoints K).symm
    rw [← Category.assoc, ← 𝕀.endpoint_naturality, e, Functor.map_comp, Category.assoc,
      Category.assoc, hH₁, ← Category.assoc (𝕀.I.map _), hψr,
      coprod.inr_desc]
    exact k₁

theorem elementaryHomotopy_equivalence_of_isFibrant {T : C}
    (hT : 𝕀.IsFibrant S T) (K : C) :
    Equivalence (fun u v : K ⟶ T ↦ 𝕀.ElementaryHomotopy u v) := by
  have symm : ∀ {u v : K ⟶ T}, 𝕀.ElementaryHomotopy u v → 𝕀.ElementaryHomotopy v u :=
    fun h ↦ 𝕀.elementaryHomotopy_of_elementaryHomotopy_of_isFibrant S hT h
      (𝕀.elementaryHomotopy_refl _)
  exact ⟨𝕀.elementaryHomotopy_refl, symm, fun h₁ h₂ ↦
    𝕀.elementaryHomotopy_of_elementaryHomotopy_of_isFibrant S hT (symm h₁) h₂⟩

theorem homotopic_iff_elementaryHomotopy_of_isFibrant {T : C}
    (hT : 𝕀.IsFibrant S T) {K : C} (u v : K ⟶ T) :
    𝕀.Homotopic u v ↔ 𝕀.ElementaryHomotopy u v :=
  ((𝕀.elementaryHomotopy_equivalence_of_isFibrant S hT K).eqvGen_iff)

theorem exists_fac_of_homotopic {T : C} (hT : 𝕀.IsFibrant S T) {A B : C}
    (i : A ⟶ B) [Mono i] (k : A ⟶ T) (l : B ⟶ T)
    (h : 𝕀.Homotopic (i ≫ l) k) : ∃ l' : B ⟶ T, i ≫ l' = k := by
  obtain ⟨H, h₀, h₁⟩ := (𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hT _ _).1 h
  obtain ⟨L, hL⟩ := 𝕀.exists_fac_of_isFibrant S hT
    ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem false i inferInstance)
    (pushout.desc H l h₀)
  refine ⟨(𝕀.endpoint true).app B ≫ L, ?_⟩
  rw [← 𝕀.endpoint_naturality_assoc,
    𝕀.map_comp_eq_of_endpointBox_comp_eq false i hL, h₁]

theorem anodyne_le_weakEquivalences [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [IsSaturated.{w} (MorphismProperty.monomorphisms C)]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.anodyne S ≤ 𝕀.weakEquivalences S := by
  intro K L j hj T hT
  refine ⟨fun c₀ c₁ hc ↦ ?_, fun c ↦ ?_⟩
  · induction c₀ using Quotient.inductionOn with | h l₀ => ?_
    induction c₁ using Quotient.inductionOn with | h l₁ => ?_
    have hr : 𝕀.Homotopic (j ≫ l₀) (j ≫ l₁) := Quotient.exact hc
    obtain ⟨h, h₀, h₁⟩ := (𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hT _ _).1 hr
    have hc' : 𝕀.endpoints K ≫ h = coprod.map j j ≫ coprod.desc l₀ l₁ := by
      refine coprod.hom_ext ?_ ?_
      · rw [← Category.assoc, inl_endpoints, h₀, coprod.inl_map_assoc, coprod.inl_desc]
      · rw [← Category.assoc, inr_endpoints, h₁, coprod.inr_map_assoc, coprod.inr_desc]
    have : Mono j := 𝕀.anodyne_le_monomorphisms S hS j hj
    obtain ⟨H, hH⟩ := 𝕀.exists_fac_of_isFibrant S hT
      ((𝕀.isAnodyneClass_anodyne S).bothBox_mem j inferInstance hj)
      (pushout.desc h (coprod.desc l₀ l₁) hc')
    have hH' : 𝕀.endpoints L ≫ H = coprod.desc l₀ l₁ :=
      𝕀.endpoints_comp_eq_of_bothBox_comp_eq j hH
    refine Quotient.sound (Relation.EqvGen.rel _ _ ⟨H, ?_, ?_⟩)
    · simpa only [← Category.assoc, inl_endpoints, coprod.inl_desc] using
        congrArg (coprod.inl ≫ ·) hH'
    · simpa only [← Category.assoc, inr_endpoints, coprod.inr_desc] using
        congrArg (coprod.inr ≫ ·) hH'
  · induction c using Quotient.inductionOn with | h k => ?_
    obtain ⟨l, hl⟩ := 𝕀.exists_fac_of_isFibrant S hT hj k
    exact ⟨Quotient.mk _ l, congrArg (Quotient.mk _) hl⟩

theorem isomorphisms_le_weakEquivalences :
    MorphismProperty.isomorphisms C ≤ 𝕀.weakEquivalences S := by
  intro X Y f hf T _
  have h₁ := 𝕀.precompClasses_comp f (inv f) T
  have h₂ := 𝕀.precompClasses_comp (inv f) f T
  rw [IsIso.hom_inv_id, precompClasses_id] at h₁
  rw [IsIso.inv_hom_id, precompClasses_id] at h₂
  exact Function.bijective_iff_has_inverse.2
    ⟨𝕀.precompClasses (inv f) T, congrFun h₂.symm, congrFun h₁.symm⟩

instance weakEquivalences_hasTwoOutOfThreeProperty :
    (𝕀.weakEquivalences S).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg T hT := by
    rw [precompClasses_comp]
    exact (hf T hT).comp (hg T hT)
  of_postcomp f g hg hfg T hT := by
    have := hfg T hT
    rw [precompClasses_comp] at this
    exact (Function.Bijective.of_comp_iff _ (hg T hT)).1 this
  of_precomp f g hf hfg T hT := by
    have := hfg T hT
    rw [precompClasses_comp] at this
    exact (Function.Bijective.of_comp_iff' (hf T hT) _).1 this

instance weakEquivalences_isStableUnderRetracts :
    (𝕀.weakEquivalences S).IsStableUnderRetracts where
  of_retract {X Y Z W} {f g} h hg T hT := by
    obtain ⟨hgi, hgs⟩ := hg T hT
    have hl : ∀ a, 𝕀.precompClasses h.i.left T (𝕀.precompClasses h.r.left T a) = a := by
      intro a
      rw [← Function.comp_apply (f := 𝕀.precompClasses h.i.left T), ← precompClasses_comp,
        h.retract_left]
      exact congrFun (𝕀.precompClasses_id X T) a
    have hr : ∀ a, 𝕀.precompClasses h.i.right T (𝕀.precompClasses h.r.right T a) = a := by
      intro a
      rw [← Function.comp_apply (f := 𝕀.precompClasses h.i.right T), ← precompClasses_comp,
        h.retract_right]
      exact congrFun (𝕀.precompClasses_id Y T) a
    have hiw : ∀ b, 𝕀.precompClasses f T (𝕀.precompClasses h.i.right T b) =
        𝕀.precompClasses h.i.left T (𝕀.precompClasses g T b) := by
      intro b
      rw [← Function.comp_apply (f := 𝕀.precompClasses f T), ← precompClasses_comp, ← h.i_w,
        precompClasses_comp, Function.comp_apply]
    have hrw : ∀ a, 𝕀.precompClasses g T (𝕀.precompClasses h.r.right T a) =
        𝕀.precompClasses h.r.left T (𝕀.precompClasses f T a) := by
      intro a
      rw [← Function.comp_apply (f := 𝕀.precompClasses g T), ← precompClasses_comp, ← h.r_w,
        precompClasses_comp, Function.comp_apply]
    refine ⟨fun a a' haa ↦ ?_, fun a ↦ ?_⟩
    · have e := hgi (by rw [hrw, hrw, haa] :
        𝕀.precompClasses g T (𝕀.precompClasses h.r.right T a) =
          𝕀.precompClasses g T (𝕀.precompClasses h.r.right T a'))
      rw [← hr a, ← hr a', e]
    · obtain ⟨b, hb⟩ := hgs (𝕀.precompClasses h.r.left T a)
      exact ⟨𝕀.precompClasses h.i.right T b, by rw [hiw, hb, hl]⟩

end ExactCylinder

end HomotopicalAlgebra
