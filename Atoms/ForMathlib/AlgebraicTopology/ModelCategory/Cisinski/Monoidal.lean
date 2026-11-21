import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.FibrantObject
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Atoms.ForMathlib.CategoryTheory.Monoidal.PushoutProduct

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory

universe v u

namespace HomotopicalAlgebra.ExactCylinder

open CategoryTheory.MonoidalCategory.Arrow

universe w

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryCoproducts C]

structure TensorLeftIso (𝕀 : ExactCylinder.{w} C) (J : C) (e : Bool → (𝟙_ C ⟶ J)) where
  iso : 𝕀.I ≅ tensorLeft J
  endpoint_app_comp_iso_hom_app (ε : Bool) (X : C) :
    (𝕀.endpoint ε).app X ≫ iso.hom.app X = (λ_ X).inv ≫ e ε ▷ X

namespace TensorLeftIso

variable [HasPushouts C] {𝕀 : ExactCylinder.{v} C} {J : C} {e : Bool → (𝟙_ C ⟶ J)}
  (h : 𝕀.TensorLeftIso J e)

noncomputable def endpointBoxArrowIso (ε : Bool) {K X : C} (i : K ⟶ X) :
    Arrow.mk (𝕀.endpointBox ε i) ≅ (Arrow.mk (e ε) □ Arrow.mk i) :=
  NatTrans.leibnizBoxArrowIso (𝕀.endpoint ε) (e ε) (leftUnitorNatIso C).symm h.iso
    (h.endpoint_app_comp_iso_hom_app ε) i

variable [BraidedCategory C] [MonoidalClosed C]

private noncomputable def doubleIsoTensorLeft :
    doubleFunctor ≅ tensorLeft (𝟙_ C ⨿ 𝟙_ C) :=
  NatIso.ofComponents (fun X ↦ coprod.mapIso (λ_ X).symm (λ_ X).symm ≪≫
    PreservesColimitPair.iso (tensorRight X) _ _) fun f ↦ by
      refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodComparison, ← whisker_exchange]

noncomputable def bothBoxArrowIso {K X : C} (i : K ⟶ X) :
    Arrow.mk (𝕀.bothBox i) ≅ (Arrow.mk (coprod.desc (e false) (e true)) □ Arrow.mk i) :=
  NatTrans.leibnizBoxArrowIso 𝕀.endpointsNatTrans (coprod.desc (e false) (e true))
    doubleIsoTensorLeft h.iso (fun X ↦ by
      have hl : coprod.inl ≫ (doubleIsoTensorLeft (C := C)).hom.app X =
          (λ_ X).inv ≫ coprod.inl ▷ X := by
        exact (coprod.inl_map_assoc _ _ _).trans (congrArg _ (coprod.inl_desc _ _))
      have hr : coprod.inr ≫ (doubleIsoTensorLeft (C := C)).hom.app X =
          (λ_ X).inv ≫ coprod.inr ▷ X := by
        exact (coprod.inr_map_assoc _ _ _).trans (congrArg _ (coprod.inr_desc _ _))
      refine coprod.hom_ext ?_ ?_
      · rw [endpointsNatTrans_app, inl_endpoints_assoc, h.endpoint_app_comp_iso_hom_app,
          reassoc_of% hl, ← comp_whiskerRight, coprod.inl_desc]
      · rw [endpointsNatTrans_app, inr_endpoints_assoc, h.endpoint_app_comp_iso_hom_app,
          reassoc_of% hr, ← comp_whiskerRight, coprod.inr_desc]) i

end TensorLeftIso

section Boxes

variable [HasPushouts C] [HasColimitsOfSize.{v, v} C] [BraidedCategory C] [MonoidalClosed C]

omit [HasBinaryCoproducts C] [BraidedCategory C] in
theorem _root_.CategoryTheory.NatTrans.isSaturated_leibnizPreimage_curriedTensor_map
    {X Y : C} (g : X ⟶ Y) (P : MorphismProperty C) [IsSaturated.{v} P] :
    IsSaturated.{v} (NatTrans.leibnizPreimage ((curriedTensor C).map g) P) :=
  have : PreservesColimitsOfSize.{v, v} ((curriedTensor C).obj X) :=
    inferInstanceAs (PreservesColimitsOfSize.{v, v} (tensorLeft X))
  have : PreservesColimitsOfSize.{v, v} ((curriedTensor C).obj Y) :=
    inferInstanceAs (PreservesColimitsOfSize.{v, v} (tensorLeft Y))
  NatTrans.isSaturated_leibnizPreimage _ P

omit [HasBinaryCoproducts C] [HasColimitsOfSize.{v, v} C] [MonoidalClosed C] in
theorem _root_.CategoryTheory.NatTrans.leibnizPreimage_curriedTensor_map_iff (g : Arrow C)
    (P : MorphismProperty C) [P.RespectsIso] {A B : C} (f : A ⟶ B) :
    NatTrans.leibnizPreimage ((curriedTensor C).map g.hom) P f ↔ P (Arrow.mk f □ g).hom :=
  (P.arrow_mk_iso_iff (PushoutProduct.braiding g (Arrow.mk f))).trans Iff.rfl

end Boxes

section TrivialCofibrations

variable [HasPushouts C] [HasTerminal C] [HasPullbacks C] [FinitaryPreExtensive C]
  [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
  [IsLocallyPresentable.{v} C] [HasCellularModel C] [HasInitial C] [InitialMonoClass C]
  (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) [S.IsSmall.{v}]

omit [CartesianMonoidalCategory C] in
theorem trivialCofibrations_bothBox (hS : S ≤ monomorphisms C) {K X : C} (u : K ⟶ X)
    (hu : 𝕀.trivialCofibrations S u) : 𝕀.trivialCofibrations S (𝕀.bothBox u) := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  have : Mono u := hu.1
  have hend (ε : Bool) (Y : C) : 𝕀.weakEquivalences S ((𝕀.endpoint ε).app Y) :=
    𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_endpoint S ε Y)
  have hI : 𝕀.weakEquivalences S (𝕀.I.map u) := by
    have h := (𝕀.weakEquivalences S).comp_mem _ _ hu.2 (hend false X)
    rw [← 𝕀.endpoint_naturality] at h
    exact (𝕀.weakEquivalences S).of_precomp _ _ (hend false K) h
  have hinl : 𝕀.trivialCofibrations S (pushout.inl (𝕀.endpoints K) (coprod.map u u)) :=
    (𝕀.trivialCofibrations S).of_isPushout (IsPushout.of_hasPushout _ _)
      (coprod_map_mem_of_isStableUnderCobaseChange _ hu)
  refine ⟨𝕀.mono_bothBox u inferInstance, (𝕀.weakEquivalences S).of_precomp _ _ hinl.2 ?_⟩
  rw [𝕀.inl_bothBox]
  exact hI

variable [BraidedCategory C] [MonoidalClosed C]

private def boxTrivialCofibrations : MorphismProperty C :=
  ⨅ g : {g : Arrow C // Mono g.hom},
    NatTrans.leibnizPreimage ((curriedTensor C).map g.1.hom) (𝕀.trivialCofibrations S)

omit [HasInitial C] [InitialMonoClass C] [MonoidalClosed C] in
private theorem boxTrivialCofibrations_iff (hS : S ≤ monomorphisms C) {A B : C} (f : A ⟶ B) :
    boxTrivialCofibrations 𝕀 S f ↔
      ∀ g : Arrow C, Mono g.hom → 𝕀.trivialCofibrations S (Arrow.mk f □ g).hom := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  rw [boxTrivialCofibrations, MorphismProperty.iInf_iff]
  exact ⟨fun h g hg ↦ (NatTrans.leibnizPreimage_curriedTensor_map_iff _ _ f).1 (h ⟨g, hg⟩),
    fun h g ↦ (NatTrans.leibnizPreimage_curriedTensor_map_iff _ _ f).2 (h g.1 g.2)⟩

theorem trivialCofibrations_pushoutProduct_of_anodyne (hS : S ≤ monomorphisms C) {J : C}
    {e : Bool → (𝟙_ C ⟶ J)} (h : 𝕀.TensorLeftIso J e) (G : MorphismProperty C)
    (hG : monomorphisms C ≤ saturation.{v} G)
    (hgen : ∀ ⦃A B X Y : C⦄ (s : A ⟶ B) (g : X ⟶ Y), S s → G g →
      𝕀.trivialCofibrations S (Arrow.mk s □ Arrow.mk g).hom)
    {A B K L : C} (a : A ⟶ B) (ha : 𝕀.anodyne S a) (g : K ⟶ L) [Mono g] :
    𝕀.trivialCofibrations S (Arrow.mk a □ Arrow.mk g).hom := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  have hmono (f g : Arrow C) (hf : Mono f.hom) (hg : Mono g.hom) : Mono (f □ g).hom :=
    Arrow.mono_pushoutProduct f.hom g.hom
  have hK : IsAnodyneClass 𝕀 S (boxTrivialCofibrations 𝕀 S) := by
    refine ⟨isSaturated_sInf _ ?_, fun _ _ s hs ↦ ?_, fun ε {_ _} i hi ↦ ?_, fun {_ _} i hi hK ↦ ?_⟩
    · rintro _ ⟨g, rfl⟩
      exact NatTrans.isSaturated_leibnizPreimage_curriedTensor_map g.1.hom _
    · have := NatTrans.isSaturated_leibnizPreimage_curriedTensor_map s (𝕀.trivialCofibrations S)
      refine (boxTrivialCofibrations_iff 𝕀 S hS s).2 fun g hg ↦ ?_
      exact saturation_le _ (NatTrans.leibnizPreimage ((curriedTensor C).map s)
        (𝕀.trivialCofibrations S)) (fun X Y g' hg' ↦ hgen s g' hs hg') g.hom (hG _ hg)
    · refine (boxTrivialCofibrations_iff 𝕀 S hS _).2 fun g hg ↦ ?_
      have := hmono (Arrow.mk i) g hi hg
      refine ((𝕀.trivialCofibrations S).arrow_mk_iso_iff
        ((pushoutProduct.mapIso (h.endpointBoxArrowIso ε i)).app g ≪≫
          PushoutProduct.associator _ _ _ ≪≫
          (h.endpointBoxArrowIso ε (Arrow.mk i □ g).hom).symm)).2 ?_
      exact ⟨𝕀.mono_endpointBox ε _ inferInstance, 𝕀.anodyne_le_weakEquivalences S hS _
        ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε _ inferInstance)⟩
    · refine (boxTrivialCofibrations_iff 𝕀 S hS _).2 fun g hg ↦ ?_
      refine ((𝕀.trivialCofibrations S).arrow_mk_iso_iff
        ((pushoutProduct.mapIso (h.bothBoxArrowIso i)).app g ≪≫
          PushoutProduct.associator _ _ _ ≪≫ (h.bothBoxArrowIso (Arrow.mk i □ g).hom).symm)).2 ?_
      exact 𝕀.trivialCofibrations_bothBox S hS _ ((boxTrivialCofibrations_iff 𝕀 S hS i).1 hK g hg)
  exact (boxTrivialCofibrations_iff 𝕀 S hS a).1 (𝕀.anodyne_le S _ hK a ha) (Arrow.mk g)
    (inferInstance : Mono g)

omit [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C] [HasBinaryProducts C]
  [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] [HasCellularModel C] [HasInitial C]
  [InitialMonoClass C] [S.IsSmall.{v}] [BraidedCategory C] in
private theorem naiveFibrations_ihom_map {K X Y : C} (q : X ⟶ Y) (hq : 𝕀.fibrations S q)
    (h : ∀ ⦃A B : C⦄ (b : A ⟶ B), 𝕀.anodyne S b → 𝕀.trivialCofibrations S (K ◁ b)) :
    𝕀.naiveFibrations S ((ihom K).map q) := fun _ _ b hb ↦
  ((ihom.adjunction K).hasLiftingProperty_iff b q).1 (hq _ (h b hb))

theorem trivialCofibrations_pushoutProduct (hS : S ≤ monomorphisms C) {J : C}
    {e : Bool → (𝟙_ C ⟶ J)} (h : 𝕀.TensorLeftIso J e) (G : MorphismProperty C)
    (hG : monomorphisms C ≤ saturation.{v} G)
    (hgen : ∀ ⦃A B X Y : C⦄ (s : A ⟶ B) (g : X ⟶ Y), S s → G g →
      𝕀.trivialCofibrations S (Arrow.mk s □ Arrow.mk g).hom)
    {A B K L : C} (a : A ⟶ B) (ha : 𝕀.trivialCofibrations S a) (j : K ⟶ L) [Mono j] :
    𝕀.trivialCofibrations S (Arrow.mk a □ Arrow.mk j).hom := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  have : Mono a := ha.1
  have hbox {A' B' K' L' : C} (b : A' ⟶ B') (hb : 𝕀.anodyne S b) (g : K' ⟶ L') [Mono g] :=
    𝕀.trivialCofibrations_pushoutProduct_of_anodyne S hS h G hG hgen b hb g
  have hwl {K' : C} ⦃A' B' : C⦄ (b : A' ⟶ B') (hb : 𝕀.anodyne S b) :
      𝕀.trivialCofibrations S (K' ◁ b) :=
    ((𝕀.trivialCofibrations S).arrow_mk_iso_iff
      (PushoutProduct.braiding _ _ ≪≫ PushoutProduct.isInitialIso' (Arrow.mk b)
        initialIsInitial (W := K'))).1 (hbox b hb (initial.to K'))
  rw [𝕀.trivialCofibrations_eq S hS] at ha ⊢
  refine ⟨Arrow.mono_pushoutProduct _ _, fun X Y p ⟨hp, hY⟩ ↦ ?_⟩
  have hpf : 𝕀.fibrations S p := 𝕀.rlp_trivialCofibrations_of_rlp_anodyne S hS p hp hY
  refine (HasLiftingProperty.iff_of_arrow_iso_left
    (PushoutProduct.braiding (Arrow.mk a) (Arrow.mk j)) p).2 ?_
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j p
  refine (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) j a) sq₁₃).2 (ha.2 _ ⟨?_, ?_⟩)
  · intro _ _ b hb
    refine (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) j b) sq₁₃).1 ?_
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (PushoutProduct.braiding (Arrow.mk b) (Arrow.mk j)) p).1 (hpf _ (hbox b hb j))
  · have hT : IsTerminal ((ihom L).obj (⊤_ C)) := terminalIsTerminal.isTerminalObj (ihom L) _
    have h₁ : 𝕀.naiveFibrations S sq₁₃.snd :=
      (𝕀.naiveFibrations S).of_isPullback sq₁₃.isPullback
        (𝕀.naiveFibrations_ihom_map S p hpf hwl)
    have h₂ : 𝕀.naiveFibrations S ((ihom L).map (terminal.from Y)) :=
      𝕀.naiveFibrations_ihom_map S _ ((𝕀.rlp_trivialCofibrations_terminal_from_iff S hS Y).2 hY)
        hwl
    have h₃ : 𝕀.naiveFibrations S (terminal.from ((ihom L).obj (⊤_ C))) :=
      have := isIso_of_isTerminal hT terminalIsTerminal (terminal.from ((ihom L).obj (⊤_ C)))
      MorphismProperty.of_isIso _ _
    have := (𝕀.naiveFibrations S).comp_mem _ _ h₁ ((𝕀.naiveFibrations S).comp_mem _ _ h₂ h₃)
    rwa [Subsingleton.elim (sq₁₃.snd ≫ (ihom L).map (terminal.from Y) ≫
      terminal.from ((ihom L).obj (⊤_ C))) (terminal.from _)] at this

omit [HasInitial C] [InitialMonoClass C] [MonoidalClosed C] in
theorem trivialCofibrations_pushoutProduct_of_comp (hS : S ≤ monomorphisms C) {A B D K L : C}
    (k : A ⟶ B) (s : B ⟶ D) [Mono s] (g : K ⟶ L) [Mono g]
    (hks : 𝕀.trivialCofibrations S (Arrow.mk (k ≫ s) □ Arrow.mk g).hom)
    (hk : 𝕀.trivialCofibrations S (Arrow.mk k □ Arrow.mk g).hom) :
    𝕀.trivialCofibrations S (Arrow.mk s □ Arrow.mk g).hom := by
  have := 𝕀.isSaturated_trivialCofibrations S hS
  let α := (curriedTensor C).map g
  replace hks : 𝕀.trivialCofibrations S (NatTrans.leibnizBox α (k ≫ s)) :=
    (NatTrans.leibnizPreimage_curriedTensor_map_iff (Arrow.mk g) _ (k ≫ s)).2 hks
  replace hk : 𝕀.trivialCofibrations S (NatTrans.leibnizBox α k) :=
    (NatTrans.leibnizPreimage_curriedTensor_map_iff (Arrow.mk g) _ k).2 hk
  refine (NatTrans.leibnizPreimage_curriedTensor_map_iff (Arrow.mk g)
    (𝕀.trivialCofibrations S) s).1 ?_
  have hpo := NatTrans.isPushout_leibnizSourceMap_of_comp α k (k ≫ s) s (by simp)
  have hc : 𝕀.trivialCofibrations S
      (NatTrans.leibnizSourceMap α (i := k ≫ s) (i' := s) k (𝟙 D) (by simp)) :=
    (𝕀.trivialCofibrations S).of_isPushout hpo hk
  have hfac := NatTrans.leibnizSourceMap_leibnizBox α k (𝟙 D) (i := k ≫ s) (i' := s) (by simp)
  rw [CategoryTheory.Functor.map_id, Category.comp_id (NatTrans.leibnizBox α (k ≫ s))] at hfac
  have hm : Mono (NatTrans.leibnizBox α s) :=
    ((monomorphisms C).arrow_mk_iso_iff (PushoutProduct.braiding (Arrow.mk g) (Arrow.mk s))).2
      (Arrow.mono_pushoutProduct s g)
  exact ⟨hm, (𝕀.weakEquivalences S).of_precomp _ _ hc.2 (hfac ▸ hks.2)⟩

end TrivialCofibrations

end HomotopicalAlgebra.ExactCylinder
