import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FatJoin
import Atoms.Homotopical.Localizer.LeftProper
import Atoms.Homotopical.Simplicial.CartesianInduction
import Atoms.Homotopical.Simplicial.CartesianJoyal
import Atoms.Homotopical.Simplicial.CartesianMonoidal
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  HomotopicalAlgebra MorphismProperty Atoms.Homotopical

universe u

namespace SSet.modelCategoryJoyal

private instance isALocalizer_weakEquivalences :
    IsALocalizer (weakEquivalences SSet.{u}) :=
  joyalInterval.cylinder.isALocalizer_weakEquivalences innerHornInclusions
    innerHornInclusions_le_monomorphisms

theorem weakEquivalence_right_app_of_stdSimplex {Z : SSet.{u}} {Φ Ψ : SSet.{u} ⥤ Under Z}
    [PreservesColimitsOfSize.{u, u} Φ] [PreservesColimitsOfSize.{u, u} Ψ]
    (hΦ : ∀ {X Y : SSet.{u}} (f : X ⟶ Y), Mono f → Mono (Φ.map f).right)
    (hΨ : ∀ {X Y : SSet.{u}} (f : X ⟶ Y), Mono f → Mono (Ψ.map f).right) (α : Φ ⟶ Ψ)
    (h : ∀ n : ℕ, WeakEquivalence (α.app Δ[n]).right) (X : SSet.{u}) :
    WeakEquivalence (α.app X).right := by
  have hP : IsMonoSaturatedClass (fun X : SSet.{u} ↦ weakEquivalences _ (α.app X).right) :=
    { of_isPushout := fun {X₀ X₁ X₂ X₃ f₁ f₂ g₁ g₂} sq hf h₀ h₁ h₂ ↦ by
        have : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink _
        have : PreservesColimitsOfSize.{0, 0} Ψ := preservesColimitsOfSize_shrink _
        have : Mono ((Φ ⋙ Under.forget Z).map f₁) := hΦ f₁ hf
        have : Mono ((Ψ ⋙ Under.forget Z).map f₁) := hΨ f₁ hf
        exact IsALocalizer.of_isPushout_of_mono ((Φ ⋙ Under.forget Z).map_isPushout sq)
          ((Ψ ⋙ Under.forget Z).map_isPushout sq) _ _ _ _
          (congrArg CommaMorphism.right (α.naturality f₁))
          (congrArg CommaMorphism.right (α.naturality f₂))
          (congrArg CommaMorphism.right (α.naturality g₁))
          (congrArg CommaMorphism.right (α.naturality g₂)) h₀ h₁ h₂
      of_isColimit := fun J _ _ F hF {c} hc hP ↦ by
        rcases isEmpty_or_nonempty J with hJ | hJ
        · have hi : IsInitial c.pt := IsInitial.ofUniqueHom
            (fun Y ↦ hc.desc ⟨Y, { app j := isEmptyElim j, naturality j := isEmptyElim j }⟩)
            (fun Y f ↦ hc.hom_ext fun j ↦ isEmptyElim j)
          have : IsIso (α.app c.pt) := isIso_of_isInitial (IsInitial.isInitialObj Φ _ hi)
            (IsInitial.isInitialObj Ψ _ hi) _
          exact (weakEquivalences _).of_isIso ((Under.forget Z).map (α.app c.pt))
        · have : IsConnected J := IsFiltered.isConnected J
          exact IsALocalizer.of_isColimit_asSmall (X := F ⋙ Φ ⋙ Under.forget Z)
            (Y := F ⋙ Ψ ⋙ Under.forget Z) (fun i j h ↦ hΦ _ (hF i j h))
            (fun i j h ↦ hΨ _ (hF i j h)) (Functor.whiskerLeft F (Functor.whiskerRight α _)) hP
            (isColimitOfPreserves (Φ ⋙ Under.forget Z) hc)
            (isColimitOfPreserves (Ψ ⋙ Under.forget Z) hc) _
            (fun j ↦ congrArg CommaMorphism.right (α.naturality (c.ι.app j))) }
  have hr : ∀ {X Y : SSet.{u}} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X →
      weakEquivalences _ (α.app Y).right → weakEquivalences _ (α.app X).right :=
    fun i r hir hY ↦ (weakEquivalences _).of_retract
      { i := Arrow.homMk (Φ.map i).right (Ψ.map i).right
          (congrArg CommaMorphism.right (α.naturality i))
        r := Arrow.homMk (Φ.map r).right (Ψ.map r).right
          (congrArg CommaMorphism.right (α.naturality r))
        retract := by
          ext
          · simp [← Under.comp_right, ← Functor.map_comp, hir]
          · simp [← Under.comp_right, ← Functor.map_comp, hir] } hY
  rw [weakEquivalence_iff]
  exact forall_of_stdSimplex hP hr (fun n ↦ (weakEquivalence_iff _).1 (h n)) X

open MarkedSSet.modelCategoryCartesian in
private theorem weakEquivalence_iff_of_homotopy {A B : SSet.{u}} (H : Δ[1] ⊗ A ⟶ B)
    (hH : ∀ (e : (Δ[1] ⊗ A : SSet.{u}) _⦋1⦌) (v : A _⦋0⦌), e.2 = A.σ 0 v →
      ∃ b, H.app _ e = B.σ 0 b) :
    WeakEquivalence (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 A) ≫ H) ↔
      WeakEquivalence (lift (SSet.const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 A) ≫ H) := by
  let Hm : sharpEdgeProd.obj ((MarkedPresheaf.flat edgeMarking).obj A) ⟶
      (MarkedPresheaf.flat edgeMarking).obj B :=
    edgeHomMk H fun e he ↦ by
      obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ ((mem_marked_sharpEdgeProdObj _ e).1 he)
      obtain ⟨b, hb⟩ := hH e v hv
      exact hb ▸ MarkedSSet.map_σ_mem_marked ((MarkedPresheaf.flat edgeMarking).obj B) b
  have h (ε : Fin 2) : (sharpEdgeEndpoint ε).app _ ≫ Hm =
      (MarkedPresheaf.flat edgeMarking).map
        (lift (SSet.const (stdSimplex.obj₀Equiv.symm ε)) (𝟙 A) ≫ H) :=
    MarkedPresheaf.hom_ext rfl
  rw [← weakEquivalence_flat_map_iff, ← weakEquivalence_flat_map_iff, ← h 0, ← h 1]
  have := weakEquivalence_sharpEdgeEndpoint_app 0 ((MarkedPresheaf.flat edgeMarking).obj A)
  have := weakEquivalence_sharpEdgeEndpoint_app 1 ((MarkedPresheaf.flat edgeMarking).obj A)
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := weakEquivalence_of_precomp ((sharpEdgeEndpoint 0).app _) Hm
    infer_instance
  · have := weakEquivalence_of_precomp ((sharpEdgeEndpoint 1).app _) Hm
    infer_instance

private lemma exists_eq_σ_of_whiskerLeft_fatJoinIncl {X Y : SSet.{u}}
    (H : Δ[1] ⊗ fatJoin X Y ⟶ fatJoin X Y)
    (hH : Δ[1] ◁ fatJoinIncl X Y ≫ H = snd _ _ ≫ fatJoinIncl X Y)
    (e : (Δ[1] ⊗ fatJoin X Y : SSet.{u}) _⦋1⦌) (v : (fatJoin X Y) _⦋0⦌)
    (hv : e.2 = (fatJoin X Y).σ 0 v) : ∃ b, H.app _ e = (fatJoin X Y).σ 0 b := by
  obtain ⟨w, rfl⟩ := exists_fatJoinIncl_app_eq X Y v
  refine ⟨(fatJoinIncl X Y).app _ w, ?_⟩
  let x : (Δ[1] ⊗ (X ⨿ Y) : SSet.{u}) _⦋1⦌ := (e.1, (X ⨿ Y).map (SimplexCategory.σ 0).op w)
  have he : e = (Δ[1] ◁ fatJoinIncl X Y).app _ x :=
    Prod.ext rfl (hv.trans (NatTrans.naturality_apply (fatJoinIncl X Y) _ w).symm)
  have h := ConcreteCategory.congr_hom (congr_app hH (Opposite.op ⦋1⦌)) x
  rw [NatTrans.comp_app, NatTrans.comp_app] at h
  rw [he]
  exact h.trans (NatTrans.naturality_apply (fatJoinIncl X Y) _ w)

private theorem weakEquivalence_fatJoinToJoin_stdSimplex (m n : ℕ) :
    WeakEquivalence (fatJoinToJoin (Δ[m] : SSet.{u}) Δ[n]) := by
  have hπ : WeakEquivalence (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 _) ≫
      fatJoinStdSimplexHomotopyId.{u} m n) := by
    refine (weakEquivalence_iff_of_homotopy _ (exists_eq_σ_of_whiskerLeft_fatJoinIncl _
      (whiskerLeft_fatJoinIncl_fatJoinStdSimplexHomotopyId m n))).2 ?_
    rw [fatJoinStdSimplexHomotopyId_one]
    infer_instance
  rw [← fatJoinStdSimplexHomotopySection_zero] at hπ
  have hs := (weakEquivalence_iff_of_homotopy _ (exists_eq_σ_of_whiskerLeft_fatJoinIncl _
      (whiskerLeft_fatJoinIncl_fatJoinStdSimplexHomotopySection m n))).1 hπ
  rw [fatJoinStdSimplexHomotopySection_one] at hs
  have hsγ : ((stdSimplexJoinIso m n).hom ≫ fatJoinStdSimplexSection m n) ≫
      fatJoinToJoin Δ[m] Δ[n] = 𝟙 _ := by
    rw [Category.assoc, fatJoinStdSimplexSection_fatJoinToJoin, Iso.hom_inv_id]
  let R : RetractArrow (fatJoinToJoin Δ[m] Δ[n] : fatJoin Δ[m] Δ[n] ⟶ _)
      (fatJoinToJoin Δ[m] Δ[n] ≫ (stdSimplexJoinIso m n).hom ≫ fatJoinStdSimplexSection m n) :=
    { i := Arrow.homMk (𝟙 _) ((stdSimplexJoinIso m n).hom ≫ fatJoinStdSimplexSection m n)
        (Category.id_comp _)
      r := Arrow.homMk (𝟙 _) (fatJoinToJoin Δ[m] Δ[n]) ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) hsγ.symm).trans
          (Category.assoc _ _ _).symm)))
      retract := Arrow.hom_ext _ _ (Category.id_comp _) hsγ }
  exact (weakEquivalence_iff _).2 ((weakEquivalences _).of_retract R ((weakEquivalence_iff _).1 hs))

theorem weakEquivalence_fatJoinToJoin (X Y : SSet.{u}) : WeakEquivalence (fatJoinToJoin X Y) := by
  have h₁ (n : ℕ) (X : SSet.{u}) : WeakEquivalence (fatJoinToJoin X Δ[n]) :=
    weakEquivalence_right_app_of_stdSimplex (Φ := fatJoinRightUnder Δ[n])
      (Ψ := joinRightUnder Δ[n]) (fun f _ ↦ mono_fatJoinMap f (𝟙 _))
      (fun f _ ↦ mono_joinMap f (𝟙 _)) (fatJoinToJoinUnder Δ[n])
      (fun m ↦ weakEquivalence_fatJoinToJoin_stdSimplex m n) X
  exact weakEquivalence_right_app_of_stdSimplex (Φ := fatJoinLeftUnder X)
    (Ψ := joinLeftUnder X) (fun f _ ↦ mono_fatJoinMap (𝟙 _) f) (fun f _ ↦ mono_joinMap (𝟙 _) f)
    { app Y := Under.homMk (fatJoinToJoin X Y) (fatJoinInclLeft_fatJoinToJoin X Y)
      naturality _ _ f := Under.UnderMorphism.ext (fatJoinMap_comp_fatJoinToJoin (𝟙 _) f) }
    (fun n ↦ h₁ n X) Y

theorem weakEquivalence_fatJoinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (fatJoinMap f g) := by
  have := weakEquivalence_tensorHom f g
  have := weakEquivalence_whiskerLeft (∂Δ[1] : SSet.{u}) (f ⊗ₘ g)
  have := weakEquivalence_whiskerLeft Δ[1] (f ⊗ₘ g)
  have := weakEquivalence_coprodMap f g
  have (Z : SSet.{u}) : Mono ((∂Δ[1]).ι ▷ Z) := ⟨fun a b h ↦
    CartesianMonoidalCategory.hom_ext _ _
      ((cancel_mono (∂Δ[1]).ι).1 (by simpa using congrArg (· ≫ fst _ _) h))
      (by simpa using congrArg (· ≫ snd _ _) h)⟩
  rw [weakEquivalence_iff]
  exact IsALocalizer.of_isPushout_of_mono (isPushout_fatJoin X Y).flip
    (isPushout_fatJoin X' Y').flip ((∂Δ[1] : SSet.{u}) ◁ (f ⊗ₘ g)) (Δ[1] ◁ (f ⊗ₘ g))
    (coprod.map f g) (fatJoinMap f g) (whisker_exchange _ _).symm
    (fatJoinBoundaryMap_naturality f g) (fatJoinCyl_fatJoinMap f g) (fatJoinIncl_fatJoinMap f g)
    ((weakEquivalence_iff _).1 inferInstance) ((weakEquivalence_iff _).1 inferInstance)
    ((weakEquivalence_iff _).1 inferInstance)

theorem weakEquivalence_joinMap {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (joinMap f g) := by
  have := weakEquivalence_fatJoinMap f g
  have := weakEquivalence_fatJoinToJoin X Y
  have := weakEquivalence_fatJoinToJoin X' Y'
  have : WeakEquivalence (fatJoinToJoin X Y ≫ joinMap f g) := by
    rw [← fatJoinMap_comp_fatJoinToJoin]
    infer_instance
  exact weakEquivalence_of_precomp (fatJoinToJoin X Y) _

theorem isQuillen_joinRightUnderAdjunction (T : SSet.{u}) :
    (joinRightUnderAdjunction T).IsQuillen where
  cofibrations_le _ _ f hf := by
    have : Mono f := hf
    simp only [MorphismProperty.inverseImage_iff, ← cofibration_iff, cofibrations_under_iff]
    rw [cofibration_iff]
    exact mono_joinMap f (𝟙 T)
  trivialCofibrations_le _ _ f hf := by
    have : Mono f := hf.1
    have : WeakEquivalence f := (weakEquivalence_iff f).2 hf.2
    have := weakEquivalence_joinMap f (𝟙 T)
    simp only [MorphismProperty.inverseImage_iff, mem_trivialCofibrations_iff,
      cofibrations_under_iff, weakEquivalences_under_iff]
    exact ⟨(cofibration_iff _).2 (mono_joinMap f (𝟙 T)), this⟩

theorem isQuillen_fatJoinRightUnderAdjunction (T : SSet.{u}) :
    (fatJoinRightUnderAdjunction T).IsQuillen where
  cofibrations_le _ _ f hf := by
    have : Mono f := hf
    simp only [MorphismProperty.inverseImage_iff, ← cofibration_iff, cofibrations_under_iff]
    rw [cofibration_iff]
    exact mono_fatJoinMap f (𝟙 T)
  trivialCofibrations_le _ _ f hf := by
    have : Mono f := hf.1
    have : WeakEquivalence f := (weakEquivalence_iff f).2 hf.2
    have := weakEquivalence_fatJoinMap f (𝟙 T)
    simp only [MorphismProperty.inverseImage_iff, mem_trivialCofibrations_iff,
      cofibrations_under_iff, weakEquivalences_under_iff]
    exact ⟨(cofibration_iff _).2 (mono_fatJoinMap f (𝟙 T)), this⟩

theorem weakEquivalence_sliceToFatSlice {T X : SSet.{u}} [X.Quasicategory] (t : T ⟶ X) :
    WeakEquivalence ((sliceToFatSlice T).app (Under.mk t)) := by
  have : IsFibrant (Under.mk t) :=
    (isFibrant_under_iff _ _).2 ((isFibrant_iff_quasicategory X).2 inferInstance)
  exact (isQuillen_joinRightUnderAdjunction T).weakEquivalence_conjugateEquiv_app
    (isQuillen_fatJoinRightUnderAdjunction T) (fatJoinToJoinUnder T)
    (fun A _ ↦ (weakEquivalences_under_iff _ _).2 (weakEquivalence_fatJoinToJoin A T))
    (Under.mk t)

end SSet.modelCategoryJoyal
