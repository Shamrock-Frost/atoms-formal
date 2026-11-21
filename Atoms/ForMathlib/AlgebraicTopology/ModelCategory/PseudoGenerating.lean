import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

structure IsPseudoGenerating (J : MorphismProperty C) : Prop where
  le_trivialCofibrations : J ≤ trivialCofibrations C
  fibration_iff : ∀ ⦃X Y : C⦄ (p : X ⟶ Y), IsFibrant Y → (Fibration p ↔ J.rlp p)

namespace IsPseudoGenerating

variable {J : MorphismProperty C}

private theorem llp_rlp_le_trivialCofibrations (hJ : IsPseudoGenerating J) :
    J.rlp.llp ≤ trivialCofibrations C := by
  rw [← fibrations_llp]
  exact antitone_llp fun _ _ p hp _ _ j hj =>
    have := (HomotopicalAlgebra.fibration_iff p).2 hp
    have := ((mem_trivialCofibrations_iff j).1 (hJ.le_trivialCofibrations j hj)).1
    have := ((mem_trivialCofibrations_iff j).1 (hJ.le_trivialCofibrations j hj)).2
    inferInstance

theorem llp_rlp (hJ : IsPseudoGenerating J) [J.rlp.llp.HasFactorization J.rlp] {X Y : C}
    (i : X ⟶ Y) [Cofibration i] [WeakEquivalence i] (hY : IsFibrant Y) : J.rlp.llp i := by
  let h := factorizationData J.rlp.llp J.rlp i
  have := (hJ.fibration_iff h.p hY).2 h.hp
  exact J.rlp.llp.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi

omit [ModelCategory C] in
private theorem map_llp_rlp {D : Type*} [Category* D] [ModelCategory D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (hJF : J ≤ (trivialCofibrations D).inverseImage F) {A B : C} (j : A ⟶ B)
    (hj : J.rlp.llp j) : trivialCofibrations D (F.map j) := by
  rw [← fibrations_llp]
  intro _ _ q hq
  refine (adj.hasLiftingProperty_iff j q).2 (hj _ fun _ _ k hk => ?_)
  have := ((mem_trivialCofibrations_iff (F.map k)).1 (hJF k hk)).1
  have := ((mem_trivialCofibrations_iff (F.map k)).1 (hJF k hk)).2
  have := (HomotopicalAlgebra.fibration_iff q).2 hq
  exact (adj.hasLiftingProperty_iff k q).1 inferInstance

theorem map_trivialCofibrations {D : Type*} [Category* D] [ModelCategory D]
    (hJ : IsPseudoGenerating J) [J.rlp.llp.HasFactorization J.rlp]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hc : cofibrations C ≤ (cofibrations D).inverseImage F)
    (hJF : J ≤ (trivialCofibrations D).inverseImage F) :
    trivialCofibrations C ≤ (trivialCofibrations D).inverseImage F := by
  intro X Y i hi
  have := ((mem_trivialCofibrations_iff i).1 hi).1
  have := ((mem_trivialCofibrations_iff i).1 hi).2
  let h := factorizationData J.rlp.llp J.rlp (terminal.from Y)
  have hT : IsFibrant (⊤_ C) := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from (⊤_ C)) (𝟙 _)]
    infer_instance
  have hZ : IsFibrant h.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from h.Z) h.p]
    exact (hJ.fibration_iff h.p hT).2 h.hp
  have := ((mem_trivialCofibrations_iff h.i).1 (hJ.llp_rlp_le_trivialCofibrations _ h.hi)).1
  have := ((mem_trivialCofibrations_iff h.i).1 (hJ.llp_rlp_le_trivialCofibrations _ h.hi)).2
  have hj := map_llp_rlp adj hJF _ h.hi
  have hij := map_llp_rlp adj hJF _ (hJ.llp_rlp (i ≫ h.i) hZ)
  rw [F.map_comp] at hij
  exact ⟨hc i hi.1, (weakEquivalences D).of_postcomp _ _ hj.2 hij.2⟩

section PushoutProduct

variable (T : C ⥤ C ⥤ C)

private theorem map_mem_of_ι_mem (P : MorphismProperty C) [P.RespectsIso]
    [∀ Y, (T.flip.obj Y).IsLeftAdjoint] (X : C) {X₂ Y₂ : C} (g : X₂ ⟶ Y₂)
    (h : P (Functor.PushoutObjObj.ofHasPushout T (initial.to X) g).ι) : P ((T.obj X).map g) := by
  let sq := Functor.PushoutObjObj.ofHasPushout T (initial.to X) g
  have : IsIso ((T.obj (⊥_ C)).map g) :=
    isIso_of_isInitial (IsInitial.isInitialObj (T.flip.obj X₂) _ initialIsInitial)
      (IsInitial.isInitialObj (T.flip.obj Y₂) _ initialIsInitial) _
  have : IsIso sq.inl := sq.isPushout.isIso_inl_of_isIso
  rw [← sq.inl_ι]
  exact (P.cancel_left_of_respectsIso _ _).2 h

private theorem map_app_mem_of_ι_mem (P : MorphismProperty C) [P.RespectsIso]
    [∀ X, (T.obj X).IsLeftAdjoint] (Y : C) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁)
    (h : P (Functor.PushoutObjObj.ofHasPushout T f (initial.to Y)).ι) :
    P ((T.map f).app Y) := by
  let sq := Functor.PushoutObjObj.ofHasPushout T f (initial.to Y)
  have : IsIso ((T.map f).app (⊥_ C)) :=
    isIso_of_isInitial (IsInitial.isInitialObj (T.obj X₁) _ initialIsInitial)
      (IsInitial.isInitialObj (T.obj Y₁) _ initialIsInitial) _
  have : IsIso sq.inr := sq.isPushout.isIso_inr_of_isIso
  rw [← sq.inr_ι]
  exact (P.cancel_left_of_respectsIso _ _).2 h

private theorem weakEquivalence_ι {X₁ Y₁ X₂ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (sq : T.PushoutObjObj f₁ f₂) (hX : trivialCofibrations C ((T.obj X₁).map f₂))
    (hY : trivialCofibrations C ((T.obj Y₁).map f₂)) : WeakEquivalence sq.ι := by
  have hl : trivialCofibrations C sq.inl := MorphismProperty.of_isPushout sq.isPushout hX
  rw [weakEquivalence_iff]
  exact (weakEquivalences C).of_precomp _ _ hl.2 (sq.inl_ι ▸ hY.2)

theorem weakEquivalence_pushoutProduct {J : MorphismProperty C}
    (hJ : IsPseudoGenerating J) [J.rlp.llp.HasFactorization J.rlp]
    [∀ X, (T.obj X).IsLeftAdjoint] [∀ Y, (T.flip.obj Y).IsLeftAdjoint]
    (hcof : ∀ ⦃A B X Y : C⦄ (f : A ⟶ B) (g : X ⟶ Y), cofibrations C f → cofibrations C g →
      cofibrations C (Functor.PushoutObjObj.ofHasPushout T f g).ι)
    (hinit : ∀ X : C, IsCofibrant X)
    (hl : ∀ ⦃A B X Y : C⦄ (f : A ⟶ B) (g : X ⟶ Y), cofibrations C f → J g →
      weakEquivalences C (Functor.PushoutObjObj.ofHasPushout T f g).ι)
    (hr : ∀ ⦃A B X Y : C⦄ (f : A ⟶ B) (g : X ⟶ Y), J f → cofibrations C g →
      weakEquivalences C (Functor.PushoutObjObj.ofHasPushout T f g).ι)
    {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) [Cofibration f] [Cofibration g]
    (h : WeakEquivalence f ∨ WeakEquivalence g) :
    WeakEquivalence (Functor.PushoutObjObj.ofHasPushout T f g).ι := by
  have hi (Z : C) : cofibrations C (initial.to Z) := (cofibration_iff _).1 (hinit Z)
  have hL (Z : C) : trivialCofibrations C ≤ (trivialCofibrations C).inverseImage (T.obj Z) :=
    hJ.map_trivialCofibrations (Adjunction.ofIsLeftAdjoint (T.obj Z))
      (fun _ _ g hg => map_mem_of_ι_mem T _ Z g (hcof _ g (hi Z) hg))
      (fun _ _ g hg => ⟨map_mem_of_ι_mem T _ Z g (hcof _ g (hi Z)
        (hJ.le_trivialCofibrations g hg).1), map_mem_of_ι_mem T _ Z g (hl _ g (hi Z) hg)⟩)
  have hR (Z : C) : trivialCofibrations C ≤ (trivialCofibrations C).inverseImage (T.flip.obj Z) :=
    hJ.map_trivialCofibrations (Adjunction.ofIsLeftAdjoint (T.flip.obj Z))
      (fun _ _ f hf => map_app_mem_of_ι_mem T _ Z f (hcof f _ hf (hi Z)))
      (fun _ _ f hf => ⟨map_app_mem_of_ι_mem T _ Z f (hcof f _
        (hJ.le_trivialCofibrations f hf).1 (hi Z)),
        map_app_mem_of_ι_mem T _ Z f (hr f _ hf (hi Z))⟩)
  rcases h with h | h
  · have hf : trivialCofibrations C f := mem_trivialCofibrations f
    exact weakEquivalence_ι T.flip (Functor.PushoutObjObj.ofHasPushout T f g).flip (hR X f hf)
      (hR Y f hf)
  · have hg : trivialCofibrations C g := mem_trivialCofibrations g
    exact weakEquivalence_ι T _ (hL A g hg) (hL B g hg)

end PushoutProduct

end IsPseudoGenerating

end HomotopicalAlgebra
