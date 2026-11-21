import Atoms.Homotopical.Localizer.BaseChange

open CategoryTheory Limits MorphismProperty MonoidalCategory HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

theorem baseChangeClass_of_comp_of_rlp_terminal {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.HasTwoOutOfThreeProperty] {E B : Aᵒᵖ ⥤ Type (max w v)} (q : E ⟶ B)
    (hB : (MorphismProperty.monomorphisms _ ⊓ V).rlp (terminal.from B))
    {X Y Z : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (i : Y ⟶ Z)
    (hi : (MorphismProperty.monomorphisms _ ⊓ V) i) (hi' : baseChangeClass V q i)
    (hfi : baseChangeClass V q (f ≫ i)) : baseChangeClass V q f := by
  intro u
  have := hB i hi
  have sq : CommSq u i (terminal.from B) (terminal.from Z) := ⟨terminal.hom_ext _ _⟩
  obtain ⟨v, rfl⟩ : ∃ v, i ≫ v = u := ⟨sq.lift, sq.fac_left⟩
  exact V.of_postcomp _ _ (hi' v) ((baseChangeMap_comp_mem_iff V q f i v).1 (hfi v))

private theorem baseChangeClass_of_comp_rlp_monomorphisms_aux {A : Type v} [SmallCategory A]
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer.{v, v} V]
    {E B : Aᵒᵖ ⥤ Type v}
    (q : E ⟶ B) (hq : (MorphismProperty.monomorphisms _ ⊓ V).rlp q) {X Y Z : Aᵒᵖ ⥤ Type v}
    (f : X ⟶ Y) (p : Y ⟶ Z) (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp p)
    (hfp : baseChangeClass V q (f ≫ p)) : baseChangeClass V q f := by
  obtain ⟨S, hS, hmono, hVS⟩ := hV.exists_lawvereCylinder
  let 𝕃 := lawvereCylinder A
  have hLoc : IsALocalizer V := hVS ▸ 𝕃.isALocalizer_weakEquivalences S hmono
  have hqn : (𝕃.anodyne S).rlp q := antitone_rlp (fun _ _ g hg ↦
    ⟨𝕃.anodyne_le_monomorphisms S hmono g hg,
      hVS ▸ 𝕃.anodyne_le_weakEquivalences S hmono g hg⟩) _ hq
  have hsec : ∀ {M N : Aᵒᵖ ⥤ Type v} (π : M ⟶ N)
      (_ : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp π) (σ : N ⟶ M)
      (_ : σ ≫ π = 𝟙 N), baseChangeClass V q σ := by
    intro M N π hπ σ hσ b
    obtain ⟨d, rfl⟩ := 𝕃.exists_deformation_retract_of_rlp_monomorphisms π hπ σ hσ
    rw [← hVS]
    exact 𝕃.weakEquivalences_baseChangeMap_of_deformation_retract S hmono σ d q hqn b
  have hend : ∀ (ε : Bool) (T : Aᵒᵖ ⥤ Type v), baseChangeClass V q ((𝕃.endpoint ε).app T) :=
    fun ε T ↦ hsec _ (rlp_monomorphisms_lawvereCylinder_contraction A T) _
      (𝕃.endpoint_app_contraction_app ε T)
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨H, hH₀, hH₁, -⟩ := 𝕃.exists_homotopy_of_rlp_monomorphisms p hp s hs
  have e₀ : (𝕃.endpoint false).app X ≫ 𝕃.I.map f ≫ H = f := by
    rw [𝕃.endpoint_naturality_assoc, hH₀, Category.comp_id]
  have e₁ : (𝕃.endpoint true).app X ≫ 𝕃.I.map f ≫ H = f ≫ p ≫ s := by
    rw [𝕃.endpoint_naturality_assoc, hH₁]
  have hfps : baseChangeClass V q (f ≫ p ≫ s) := by
    rw [← Category.assoc]
    exact (baseChangeClass_comp_iff q _ _ hfp).2 (hsec p hp s hs)
  have hh : baseChangeClass V q (𝕃.I.map f ≫ H) :=
    (baseChangeClass_comp_iff q _ _ (hend true X)).1 (by rw [e₁]; exact hfps)
  rw [← e₀]
  exact (baseChangeClass_comp_iff q _ _ (hend false X)).2 hh

private theorem baseChangeClass_asSmall_iff {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [V.RespectsIso] {E B X Y : Aᵒᵖ ⥤ Type (max w v)} (q : E ⟶ B) (f : X ⟶ Y) :
    baseChangeClass (V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
        ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor.map q)
        ((AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor.map f) ↔
      baseChangeClass V q f := by
  let F : (Aᵒᵖ ⥤ Type (max w v)) ⥤ ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor
  have hmem : ∀ b : Y ⟶ B,
      (V.inverseImage (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.inverse)
        (baseChangeMap (F.map f) (F.map b) (F.map q)) ↔ V (baseChangeMap f b q) := fun b ↦
    (mem_iff_of_isPullback _ (isPullback_baseChangeMap (F.map f) (F.map b) (F.map q))
      ((isPullback_baseChangeMap f b q).map F) (PreservesPullback.iso F b q)
      (PreservesPullback.iso_hom_fst F b q)).symm.trans
      (MorphismProperty.map_functor_map_inverse_iff
        (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.symm V _)
  refine ⟨fun h b ↦ (hmem b).1 (h (F.map b)), fun h b' ↦ ?_⟩
  obtain ⟨b, rfl⟩ := F.map_surjective b'
  exact (hmem b).2 (h b)

theorem IsAccessibleALocalizer.baseChangeClass_of_comp_rlp_monomorphisms
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V]
    {E B : Aᵒᵖ ⥤ Type (max w v)}
    (q : E ⟶ B) (hq : (MorphismProperty.monomorphisms _ ⊓ V).rlp q) {X Y Z : Aᵒᵖ ⥤ Type (max w v)}
    (f : X ⟶ Y) (p : Y ⟶ Z) (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp p)
    (hfp : baseChangeClass V q (f ≫ p)) : baseChangeClass V q f := by
  have := hV.inverseImage_asSmall
  rw [MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor,
    ← MorphismProperty.inverseImage_inverse_inverseImage_functor
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft V,
    ← MorphismProperty.inverseImage_inf, MorphismProperty.rlp_inverseImage_of_isEquivalence] at hq
  rw [MorphismProperty.monomorphisms_eq_inverseImage_of_isEquivalence
      (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft.functor,
    MorphismProperty.rlp_inverseImage_of_isEquivalence] at hp
  rw [← baseChangeClass_asSmall_iff, Functor.map_comp] at hfp
  rw [← baseChangeClass_asSmall_iff]
  exact baseChangeClass_of_comp_rlp_monomorphisms_aux _ hq _ _ hp hfp

theorem IsAccessibleALocalizer.isALocalizer_fibrantBaseChangeClass
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer V] :
    IsALocalizer.{w, v} (fibrantBaseChangeClass V) := by
  have hLoc := hV.isALocalizer
  have hsat := fun {E B : Aᵒᵖ ⥤ Type (max w v)} (q : E ⟶ B) ↦
    hLoc.isSaturated_monomorphisms_inf_baseChangeClass q
  have hUV : fibrantBaseChangeClass V ≤ V := by
    intro X Y f hf
    have hT : (MorphismProperty.monomorphisms _ ⊓ V).rlp (𝟙 (⊤_ (Aᵒᵖ ⥤ Type (max w v)))) :=
      MorphismProperty.rlp_of_isIso _ _
    have hT' : (MorphismProperty.monomorphisms _ ⊓ V).rlp
        (terminal.from (⊤_ (Aᵒᵖ ⥤ Type (max w v)))) := by
      rw [terminal.hom_ext (terminal.from (⊤_ (Aᵒᵖ ⥤ Type (max w v)))) (𝟙 _)]
      exact hT
    have h := hf (𝟙 _) hT hT' (terminal.from Y)
    have hpb := IsPullback.of_hasPullback (terminal.from Y) (𝟙 (⊤_ (Aᵒᵖ ⥤ Type (max w v))))
    have : IsIso (pullback.fst (terminal.from Y) (𝟙 (⊤_ (Aᵒᵖ ⥤ Type (max w v))))) :=
      hpb.isIso_fst_of_isIso
    exact (mem_iff_of_isPullback V (IsPullback.of_vert_isIso ⟨by simp⟩ :
      IsPullback f (𝟙 X) (𝟙 Y) f) (isPullback_baseChangeMap f _ _)
      (asIso (pullback.fst (terminal.from Y) (𝟙 (⊤_ (Aᵒᵖ ⥤ Type (max w v))))))
      (Category.comp_id _)).1 h
  refine ⟨@HasTwoOutOfThreeProperty.mk _ _ _ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · constructor
    intro X Y Z f g hf hg E B q hq hB
    exact (baseChangeClass_comp_iff q _ _ (hf q hq hB)).2 (hg q hq hB)
  rotate_left
  · constructor
    intro X Y Z f g hf hfg E B q hq hB
    exact (baseChangeClass_comp_iff q f g (hf q hq hB)).1 (hfg q hq hB)
  · intro X Y f hf E B q _ _
    exact hLoc.rlp_monomorphisms_le_baseChangeClass q f hf
  · constructor
    intro _ _ _ _ _ _ _ _ sq hf
    refine ⟨MorphismProperty.of_isPushout (P := MorphismProperty.monomorphisms _) sq hf.1, ?_⟩
    intro E B q hq hB
    have := hsat q
    exact (MorphismProperty.of_isPushout
      (P := MorphismProperty.monomorphisms _ ⊓ baseChangeClass V q) sq ⟨hf.1, hf.2 q hq hB⟩).2
  · constructor
    intro J _ _ _ _
    constructor
    rintro X Y f ⟨t⟩
    refine
      ⟨(MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).transfiniteCompositionsOfShape_le J
      f ⟨t.ofLE inf_le_left⟩, ?_⟩
    intro E B q hq hB
    have := hsat q
    exact (MorphismProperty.transfiniteCompositionsOfShape_le
      (MorphismProperty.monomorphisms _ ⊓ baseChangeClass V q) J f
        ⟨t.ofLE fun _ _ g hg ↦ ⟨hg.1, hg.2 q hq hB⟩⟩).2
  constructor
  intro X Y Z f g hg hfg E B q hq hB
  let F := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp g
  have hi : V F.i :=
    V.of_postcomp _ _ (hLoc.rlp_monomorphisms_le _ F.hp) (by rw [F.fac]; exact hUV g hg)
  have hgq : baseChangeClass V q (F.i ≫ F.p) := by rw [F.fac]; exact hg q hq hB
  have hfgq : baseChangeClass V q ((f ≫ F.i) ≫ F.p) := by
    rw [Category.assoc, F.fac]
    exact hfg q hq hB
  exact baseChangeClass_of_comp_of_rlp_terminal q hB f F.i ⟨F.hi, hi⟩
    (hV.baseChangeClass_of_comp_rlp_monomorphisms q hq F.i F.p F.hp hgq)
    (hV.baseChangeClass_of_comp_rlp_monomorphisms q hq (f ≫ F.i) F.p F.hp hfgq)

theorem IsAccessibleALocalizer.exists_factorization {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer V] {X Y : Aᵒᵖ ⥤ Type (max w v)} (g : X ⟶ Y) :
    ∃ (Z : Aᵒᵖ ⥤ Type (max w v)) (i : X ⟶ Z) (π : Z ⟶ Y),
      (MorphismProperty.monomorphisms _ ⊓ V) i ∧
        (MorphismProperty.monomorphisms _ ⊓ V).rlp π ∧ i ≫ π = g := by
  obtain ⟨J, hJ, hJeq⟩ := hV.exists_trivialCofibrations_eq_saturation
  have := hasFunctorialFactorization_saturation J
  let F := factorizationData (saturation.{max w v} J) J.rlp g
  exact ⟨F.Z, F.i, F.p, by rw [hJeq]; exact F.hi, by rw [hJeq, rlp_saturation]; exact F.hp,
    F.fac⟩

theorem isRightProper_iff_of_generatedALocalizer {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer V] (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hS : generatedALocalizer S = V) :
    IsRightProper V ↔ S ≤ fibrantBaseChangeClass V := by
  have hSV : S ≤ V := hS ▸ le_generatedALocalizer S
  refine ⟨fun hR X Y f hf E B q hq _ b ↦ hR.weakFibration_of_rlp q hq f b (hSV f hf), fun h ↦ ?_⟩
  have hLoc := hV.isALocalizer
  have hVU : V ≤ fibrantBaseChangeClass V := by
    have := hV.isALocalizer_fibrantBaseChangeClass
    have hle := generatedALocalizer_le h
    rwa [hS] at hle
  refine ⟨fun {E B} p hp ↦ ?_⟩
  intro K L f b hf
  obtain ⟨B', j, t, hj, ht, -⟩ := hV.exists_factorization (terminal.from B)
  have hB' : (MorphismProperty.monomorphisms _ ⊓ V).rlp (terminal.from B') := by
    rw [terminal.hom_ext (terminal.from B') t]
    exact ht
  obtain ⟨E', i, p', hi, hp', hip⟩ := hV.exists_factorization (p ≫ j)
  let k : E ⟶ pullback j p' := pullback.lift p i hip.symm
  have hsq : IsPullback (pullback.snd j p') (pullback.fst j p') p' j :=
    (IsPullback.of_hasPullback j p').flip
  have hsnd : V (pullback.snd j p') := by
    have hpb := IsPullback.of_hasPullback (𝟙 B') p'
    have : IsIso (pullback.snd (𝟙 B') p') := hpb.isIso_snd_of_isIso
    refine (mem_iff_of_isPullback V (isPullback_baseChangeMap j (𝟙 B') p') hsq
      (asIso (pullback.snd (𝟙 B') p')).symm ?_).2 (hVU j hj.2 p' hp' hB' (𝟙 B'))
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
  have hki : k ≫ pullback.snd j p' = i := pullback.lift_snd _ _ _
  have : Mono i := hi.1
  have hk : (MorphismProperty.monomorphisms _ ⊓ V) k :=
    ⟨mono_of_mono_fac hki, V.of_postcomp _ _ hsnd (by rw [hki]; exact hi.2)⟩
  have := hp k hk
  have sq : CommSq (𝟙 E) k p (pullback.fst j p') := ⟨by simp [k, pullback.lift_fst]⟩
  let R : RetractArrow p (pullback.fst j p') :=
    { i := Arrow.homMk k (𝟙 B) (by simp [k, pullback.lift_fst])
      r := Arrow.homMk sq.lift (𝟙 B) (by simp)
      retract := by ext <;> simp }
  exact baseChangeClass_le_of_retract R _ (baseChangeClass_le_of_isPullback hsq _
    (hVU f hf p' hp' hB')) b

theorem isRightProper_of_generatedALocalizer_snd {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer V] (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hS : generatedALocalizer S = V) (D : Set (Aᵒᵖ ⥤ Type (max w v)))
    (hSD : ∀ {X Y : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y), S f →
      ∃ L ∈ D, ∃ e : X ≅ L ⊗ Y, f = e.hom ≫ CartesianMonoidalCategory.snd L Y)
    (hD : ∀ L ∈ D, ∀ Z : Aᵒᵖ ⥤ Type (max w v), V (CartesianMonoidalCategory.snd L Z)) :
    IsRightProper V := by
  have hLoc := hV.isALocalizer
  rw [isRightProper_iff_of_generatedALocalizer S hS]
  intro X Y f hf E B q _ _ u
  obtain ⟨L, hL, e, rfl⟩ := hSD f hf
  have h' : IsPullback (CartesianMonoidalCategory.snd L (pullback u q))
      ((L ◁ pullback.fst u q) ≫ e.inv) (pullback.fst u q)
      (e.hom ≫ CartesianMonoidalCategory.snd L Y) :=
    (IsPullback.of_snd_whiskerLeft L (pullback.fst u q)).of_iso (Iso.refl _) (Iso.refl _) e.symm
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact (mem_iff_of_isPullback V (isPullback_baseChangeMap _ u q) h' (Iso.refl _)
    (Category.id_comp _)).1 (hD L hL _)

theorem IsAccessibleALocalizer.mem_pullback_fst_of_weakFibration_of_mem
    {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsAccessibleALocalizer V] [hR : IsRightProper V] {E B : Aᵒᵖ ⥤ Type (max w v)} (p : E ⟶ B)
    (hF : WeakFibration V p) (hp : V p) (K : Aᵒᵖ ⥤ Type (max w v)) (b : K ⟶ B) :
    V (pullback.fst b p) := by
  obtain ⟨Z, i, π, hi, hπ, rfl⟩ := hV.exists_factorization b
  have hbase : V (baseChangeMap p (𝟙 B) π) := hR.weakFibration_of_rlp π hπ p (𝟙 B) hp
  have hfst : V (pullback.fst π p) := by
    refine (mem_iff_of_isPullback V (IsPullback.of_hasPullback π p)
      (isPullback_baseChangeMap p (𝟙 B) π) (asIso (pullback.snd (𝟙 B) π)) ?_).1 hbase
    rw [asIso_hom, ← pullback.condition, Category.comp_id]
  have hcomp := V.comp_mem _ _ (hF i π hi.2) hfst
  rw [baseChangeMap_fst] at hcomp
  exact V.of_postcomp _ _ hi.2 hcomp

end Atoms.Homotopical
