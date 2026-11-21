import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.TrivialFibration
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.AnodyneGenerators

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ExactCylinder

universe w v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]

def naiveFibrationsToFibrant (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty
    C) :
    MorphismProperty C :=
  fun _ Y p ↦ 𝕀.naiveFibrations S p ∧ 𝕀.IsFibrant S Y

variable (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C)

theorem exists_homotopy_inverse_of_weakEquivalences {X Y : C}
    (hX : 𝕀.IsFibrant S X) (hY : 𝕀.IsFibrant S Y) (f : X ⟶ Y) (hf : 𝕀.weakEquivalences S f) :
    ∃ g : Y ⟶ X, 𝕀.Homotopic (f ≫ g) (𝟙 X) ∧ 𝕀.Homotopic (g ≫ f) (𝟙 Y) := by
  obtain ⟨c, hc⟩ := (hf X hX).2 (Quotient.mk _ (𝟙 X))
  induction c using Quotient.inductionOn with | h g => ?_
  refine ⟨g, Quotient.exact hc, ?_⟩
  have hfg : 𝕀.Homotopic (f ≫ g) (𝟙 X) := Quotient.exact hc
  have e : 𝕀.precompClasses f Y (Quotient.mk _ (g ≫ f)) =
      𝕀.precompClasses f Y (Quotient.mk _ (𝟙 Y)) := by
    change Quotient.mk _ (f ≫ g ≫ f) = Quotient.mk _ (f ≫ 𝟙 Y)
    rw [← Category.assoc, Category.comp_id]
    have := congrFun (𝕀.precompClasses_eq_of_homotopic hfg Y) (Quotient.mk _ f)
    rw [precompClasses_id] at this
    exact this
  exact Quotient.exact ((hf Y hY).1 e)

theorem rlp_terminal_from_of_homotopy_retract (P : MorphismProperty C)
    (hP : P ≤ monomorphisms C) {X Y : C} (hY : 𝕀.IsFibrant S Y)
    (hX : P.rlp (terminal.from X)) (r : Y ⟶ X) (s : X ⟶ Y)
    (h : 𝕀.Homotopic (r ≫ s) (𝟙 Y)) : P.rlp (terminal.from Y) := by
  intro A B i hi
  have : Mono i := hP i hi
  have := hX i hi
  refine ⟨fun {k b} sq => ?_⟩
  have sq' : CommSq (k ≫ r) i (terminal.from X) (terminal.from B) :=
    ⟨terminal.hom_ext _ _⟩
  have hk : 𝕀.Homotopic (i ≫ sq'.lift ≫ s) k := by
    rw [← Category.assoc, sq'.fac_left, Category.assoc]
    simpa only [Category.comp_id] using 𝕀.homotopic_precomp k h
  obtain ⟨l, hl⟩ := 𝕀.exists_fac_of_homotopic S hY i k (sq'.lift ≫ s) hk
  exact CommSq.HasLift.mk' ⟨l, hl, terminal.hom_ext _ _⟩

omit [HasTerminal C] in
theorem rlp_monomorphisms_of_rlp_anodyne_of_deformation {X Y : C} (p : X ⟶ Y)
    (hp : 𝕀.naiveFibrations S p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) (k : 𝕀.I.obj X ⟶ X)
    (hk₀ : (𝕀.endpoint false).app X ≫ k = 𝟙 X) (hk₁ : (𝕀.endpoint true).app X ≫ k = p ≫ s)
    (hpk : k ≫ p = (𝕀.contraction).app X ≫ p) :
    (MorphismProperty.monomorphisms C).rlp p := by
  intro K L i hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  have hi' : Mono i := hi
  have hl := hp _ ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem true i hi')
  have hc : (𝕀.endpoint true).app K ≫ 𝕀.I.map a ≫ k = i ≫ b ≫ s := by
    rw [𝕀.endpoint_naturality_assoc, hk₁, ← Category.assoc, sq.w, Category.assoc]
  have sq' : CommSq (pushout.desc (𝕀.I.map a ≫ k) (b ≫ s) hc :
      𝕀.endpointBoxSource true i ⟶ X) (𝕀.endpointBox true i) p
      ((𝕀.contraction).app L ≫ b) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_endpointBox_assoc, 𝕀.map_contraction_app_assoc,
        Category.assoc, hpk, 𝕀.map_contraction_app_assoc, ← sq.w]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_endpointBox_assoc, Category.assoc, hs,
        Category.comp_id, 𝕀.endpoint_app_contraction_app_assoc]⟩
  obtain ⟨⟨⟨H, hHl, hHr⟩⟩⟩ := hl.sq_hasLift sq'
  refine ⟨⟨⟨(𝕀.endpoint false).app L ≫ H, ?_, ?_⟩⟩⟩
  · have h₁ : 𝕀.I.map i ≫ H = 𝕀.I.map a ≫ k := 𝕀.map_comp_eq_of_endpointBox_comp_eq true i hHl
    rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc, h₁,
      𝕀.endpoint_naturality_assoc, hk₀, Category.comp_id]
  · rw [Category.assoc, hHr, 𝕀.endpoint_app_contraction_app_assoc]

theorem isFibrant_of_rlp_anodyne {X Y : C} (p : X ⟶ Y) (hp : 𝕀.naiveFibrations S p)
    (hY : 𝕀.IsFibrant S Y) : 𝕀.IsFibrant S X := by
  unfold IsFibrant
  rw [← terminal.comp_from p]
  exact MorphismProperty.comp_mem _ _ _ hp hY

omit [HasPushouts C] [HasTerminal C] in
theorem cylinder_coprod_hom_ext {X Z : C} {f g : 𝕀.I.obj (X ⨿ X) ⟶ Z}
    (hl : 𝕀.I.map coprod.inl ≫ f = 𝕀.I.map coprod.inl ≫ g)
    (hr : 𝕀.I.map coprod.inr ≫ f = 𝕀.I.map coprod.inr ≫ g) : f = g := by
  rw [← cancel_epi (PreservesColimitPair.iso 𝕀.I X X).hom]
  refine coprod.hom_ext ?_ ?_
  · rw [PreservesColimitPair.iso_hom, coprodComparison, coprod.inl_desc_assoc,
      coprod.inl_desc_assoc]
    exact hl
  · rw [PreservesColimitPair.iso_hom, coprodComparison, coprod.inr_desc_assoc,
      coprod.inr_desc_assoc]
    exact hr

omit [HasTerminal C] in
theorem anodyne_endpoint [HasInitial C] [InitialMonoClass C] (ε : Bool) (Y : C) :
    𝕀.anodyne S ((𝕀.endpoint ε).app Y) :=
  (𝕀.anodyne S).of_retract (𝕀.endpointRetractArrow ε Y)
    ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε (initial.to Y) (initial.mono_from _ _))

theorem weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne [HasInitial C]
    [HasStrictInitialObjects C] {X Y : C}
    (p : X ⟶ Y) (hp : 𝕀.naiveFibrations S p) (hY : 𝕀.IsFibrant S Y) :
    𝕀.weakEquivalences S p ↔ (MorphismProperty.monomorphisms C).rlp p := by
  refine ⟨fun hW ↦ ?_, 𝕀.weakEquivalences_of_rlp_monomorphisms S p⟩
  have hX := 𝕀.isFibrant_of_rlp_anodyne S p hp hY
  obtain ⟨t, hpt, htp⟩ := 𝕀.exists_homotopy_inverse_of_weakEquivalences S hX hY p hW
  obtain ⟨k, hk₀, hk₁⟩ := (𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hY _ _).1
    (Relation.EqvGen.symm _ _ htp)
  have sq : CommSq t ((𝕀.endpoint true).app Y) p k := ⟨hk₁.symm⟩
  obtain ⟨⟨⟨k', hk'₁, hk'p⟩⟩⟩ := (hp _ (𝕀.anodyne_endpoint S true Y)).sq_hasLift sq
  obtain ⟨s, hs, hst⟩ : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y ∧ 𝕀.ElementaryHomotopy s t :=
    ⟨_, by rw [Category.assoc, hk'p, hk₀], k', rfl, hk'₁⟩
  have hps : 𝕀.Homotopic (𝟙 X) (p ≫ s) :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpt)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (𝕀.elementaryHomotopy_precomp p hst)))
  obtain ⟨h, h₀, h₁⟩ := (𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hX _ _).1 hps
  obtain ⟨ψ, hψl, hψr⟩ := 𝕀.exists_map_coprod_comp X
  have hc : (𝕀.endpoint true).app (X ⨿ X) ≫ ψ ≫ coprod.desc h (h ≫ p ≫ s) =
      𝕀.endpoints X ≫ (𝕀.contraction).app X ≫ p ≫ s := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc,
        ← Category.assoc (𝕀.I.map _), hψl, coprod.inl_desc, h₁, ← Category.assoc,
        inl_endpoints, endpoint_app_contraction_app_assoc]
    · rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc,
        ← Category.assoc (𝕀.I.map _), hψr, coprod.inr_desc, ← Category.assoc, h₁,
        Category.assoc, reassoc_of% hs, ← Category.assoc, inr_endpoints,
        endpoint_app_contraction_app_assoc]
  have hbox := (𝕀.isAnodyneClass_anodyne S).endpointBox_mem true (𝕀.endpoints X)
    inferInstance
  have sq₂ : CommSq (pushout.desc (ψ ≫ coprod.desc h (h ≫ p ≫ s))
      ((𝕀.contraction).app X ≫ p ≫ s) hc : 𝕀.endpointBoxSource true (𝕀.endpoints X) ⟶ X)
      (𝕀.endpointBox true (𝕀.endpoints X)) p
      (𝕀.I.map ((𝕀.contraction).app X) ≫ h ≫ p) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_endpointBox_assoc]
      refine 𝕀.cylinder_coprod_hom_ext ?_ ?_
      · rw [Category.assoc, reassoc_of% hψl, coprod.inl_desc_assoc,
          ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, inl_endpoints,
          endpoint_app_contraction_app, 𝕀.I.map_id, Category.id_comp]
      · rw [Category.assoc, reassoc_of% hψr, coprod.inr_desc_assoc,
          ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, inr_endpoints,
          endpoint_app_contraction_app, 𝕀.I.map_id, Category.id_comp]
        simp only [Category.assoc, hs, Category.comp_id]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_endpointBox_assoc,
        𝕀.endpoint_naturality_assoc true (K := 𝕀.I.obj X) (X := X), reassoc_of% h₁]
      simp only [Category.assoc, hs, Category.comp_id]⟩
  obtain ⟨⟨⟨H, hHl, hHr⟩⟩⟩ := (hp _ hbox).sq_hasLift sq₂
  have hH₁ : 𝕀.I.map (𝕀.endpoints X) ≫ H = ψ ≫ coprod.desc h (h ≫ p ≫ s) :=
    𝕀.map_comp_eq_of_endpointBox_comp_eq true _ hHl
  have e₀ : 𝕀.I.map ((𝕀.endpoint false).app X) ≫ H = h := by
    rw [← inl_endpoints, Functor.map_comp_assoc, hH₁, reassoc_of% hψl, coprod.inl_desc]
  have e₁ : 𝕀.I.map ((𝕀.endpoint true).app X) ≫ H = h ≫ p ≫ s := by
    rw [← inr_endpoints, Functor.map_comp_assoc, hH₁, reassoc_of% hψr, coprod.inr_desc]
  refine 𝕀.rlp_monomorphisms_of_rlp_anodyne_of_deformation S p hp s hs
    ((𝕀.endpoint false).app (𝕀.I.obj X) ≫ H) ?_ ?_ ?_
  · rw [← 𝕀.endpoint_naturality_assoc false (K := X) _ H, e₀, h₀]
  · rw [← 𝕀.endpoint_naturality_assoc false (K := X) _ H, e₁, ← Category.assoc, h₀]
    exact Category.id_comp _
  · rw [Category.assoc, hHr, 𝕀.endpoint_naturality_assoc false (K := 𝕀.I.obj X) (X := X),
      reassoc_of% h₀]

theorem anodyne_iff_weakEquivalences_of_isFibrant [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) {K L : C}
    (i : K ⟶ L) (hi : Mono i) (hL : 𝕀.IsFibrant S L) :
    𝕀.anodyne S i ↔ 𝕀.weakEquivalences S i := by
  refine ⟨fun h ↦ 𝕀.anodyne_le_weakEquivalences S hS i h, fun hW ↦ ?_⟩
  have := 𝕀.hasFunctorialFactorization_anodyne S hS
  let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) i
  have hq : 𝕀.weakEquivalences S F.p :=
    MorphismProperty.of_precomp _ F.i F.p (𝕀.anodyne_le_weakEquivalences S hS _ F.hi)
      (by rw [F.fac]; exact hW)
  have htf := (𝕀.weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne S F.p F.hp hL).1 hq
  have : HasLiftingProperty i F.p := htf i hi
  exact (𝕀.anodyne S).of_retract (RetractArrow.ofLeftLiftingProperty F.fac) F.hi

theorem exists_anodyne_isFibrant [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
    [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) (L : C) :
    ∃ (L' : C) (j : L ⟶ L'), 𝕀.anodyne S j ∧ 𝕀.IsFibrant S L' := by
  have := 𝕀.hasFunctorialFactorization_anodyne S hS
  let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) (terminal.from L)
  refine ⟨F.Z, F.i, F.hi, ?_⟩
  unfold IsFibrant
  rw [Subsingleton.elim (terminal.from F.Z) F.p]
  exact F.hp

theorem weakEquivalences_iff_anodyne_comp [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) {K L L' : C}
    (i : K ⟶ L) (hi : Mono i) (j : L ⟶ L') (hj : 𝕀.anodyne S j) (hL' : 𝕀.IsFibrant S L') :
    𝕀.weakEquivalences S i ↔ 𝕀.anodyne S (i ≫ j) := by
  have hjW := 𝕀.anodyne_le_weakEquivalences S hS j hj
  have : Mono j := 𝕀.anodyne_le_monomorphisms S hS j hj
  rw [𝕀.anodyne_iff_weakEquivalences_of_isFibrant S hS (i ≫ j) inferInstance hL']
  exact ⟨fun h ↦ MorphismProperty.comp_mem _ _ _ h hjW,
    fun h ↦ MorphismProperty.of_postcomp _ i j hjW h⟩

theorem trivialCofibrations_eq [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
    [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.trivialCofibrations S =
      MorphismProperty.monomorphisms C ⊓ (𝕀.naiveFibrationsToFibrant S).llp := by
  ext K L i
  obtain ⟨L', j, hj, hL'⟩ := 𝕀.exists_anodyne_isFibrant S hS L
  constructor
  · rintro ⟨hi, hW⟩
    refine ⟨hi, fun X Y p ⟨hp, hY⟩ ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
    have hij := (𝕀.weakEquivalences_iff_anodyne_comp S hS i hi j hj hL').1 hW
    obtain ⟨b', hb'⟩ := 𝕀.exists_fac_of_isFibrant S hY hj b
    have sq' : CommSq a (i ≫ j) p b' := ⟨by rw [Category.assoc, hb']; exact sq.w⟩
    obtain ⟨⟨⟨l, hl, hr⟩⟩⟩ := (hp _ hij).sq_hasLift sq'
    exact ⟨⟨⟨j ≫ l, by rw [← Category.assoc]; exact hl, by rw [Category.assoc, hr, hb']⟩⟩⟩
  · rintro ⟨hi, hllp⟩
    refine ⟨hi, (𝕀.weakEquivalences_iff_anodyne_comp S hS i hi j hj hL').2 ?_⟩
    have := 𝕀.hasFunctorialFactorization_anodyne S hS
    let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) (i ≫ j)
    have : HasLiftingProperty i F.p := hllp F.p ⟨F.hp, hL'⟩
    have : HasLiftingProperty j F.p := F.hp j hj
    exact (𝕀.anodyne S).of_retract (RetractArrow.ofLeftLiftingProperty F.fac) F.hi

theorem isSaturated_trivialCofibrations [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    IsSaturated.{v} (𝕀.trivialCofibrations S) := by
  rw [𝕀.trivialCofibrations_eq S hS]
  infer_instance

theorem rlp_trivialCofibrations_of_rlp_anodyne [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) {X Y : C}
    (p : X ⟶ Y) (hp : 𝕀.naiveFibrations S p) (hY : 𝕀.IsFibrant S Y) :
    𝕀.fibrations S p := by
  rw [fibrations, 𝕀.trivialCofibrations_eq S hS]
  exact fun _ _ i hi ↦ hi.2 p ⟨hp, hY⟩

theorem rlp_trivialCofibrations_terminal_from_iff [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) (X : C) :
    𝕀.fibrations S (terminal.from X) ↔ 𝕀.IsFibrant S X := by
  refine ⟨fun h ↦ antitone_rlp (fun _ _ f hf ↦ ⟨𝕀.anodyne_le_monomorphisms S hS f hf,
    𝕀.anodyne_le_weakEquivalences S hS f hf⟩) _ h, fun h ↦ ?_⟩
  have hT : 𝕀.IsFibrant S (⊤_ C) := by
    unfold IsFibrant
    rw [Subsingleton.elim (terminal.from _) (𝟙 _)]
    exact MorphismProperty.id_mem _ _
  exact 𝕀.rlp_trivialCofibrations_of_rlp_anodyne S hS _ h hT

omit [HasTerminal C] in
theorem llp_rlp_anodyne_of_deformation_retract {K L : C}
    (i : K ⟶ L) (d : 𝕀.DeformationRetract i) : (𝕀.naiveFibrations S).llp i := by
  intro X Y p hp
  refine ⟨fun {u w} sq ↦ ?_⟩
  have : Mono i := mono_of_mono_fac d.comp_retraction
  have hc : (𝕀.endpoint true).app K ≫ (𝕀.contraction).app K ≫ u =
      i ≫ d.retraction ≫ u := by
    rw [endpoint_app_contraction_app_assoc, ← Category.assoc, d.comp_retraction]
    exact (Category.id_comp u).symm
  have sq' : CommSq (pushout.desc ((𝕀.contraction).app K ≫ u) (d.retraction ≫ u) hc :
      𝕀.endpointBoxSource true i ⟶ X) (𝕀.endpointBox true i) p (d.homotopy ≫ w) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_endpointBox_assoc,
        ← Category.assoc (𝕀.I.map i) d.homotopy, d.map_comp_homotopy]
      simp only [Category.assoc]
      rw [map_contraction_app_assoc, sq.w]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_endpointBox_assoc, ← Category.assoc _ d.homotopy,
        d.endpoint_true_comp_homotopy, Category.assoc, Category.assoc, sq.w]⟩
  obtain ⟨⟨⟨H, hHl, hHr⟩⟩⟩ :=
    (hp _ ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem true i this)).sq_hasLift sq'
  have h₁ : 𝕀.I.map i ≫ H = (𝕀.contraction).app K ≫ u :=
    𝕀.map_comp_eq_of_endpointBox_comp_eq true i hHl
  refine ⟨⟨⟨(𝕀.endpoint false).app L ≫ H, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← 𝕀.endpoint_naturality, Category.assoc, h₁,
      endpoint_app_contraction_app_assoc]
  · rw [Category.assoc, hHr, ← Category.assoc, d.endpoint_false_comp_homotopy]
    exact Category.id_comp w

omit [HasTerminal C] in
theorem anodyne_of_deformation_retract [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasBinaryProducts C] [HasColimitsOfSize.{v, v} C]
    [IsLocallyPresentable.{v} C] [HasCellularModel C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) {K L : C}
    (i : K ⟶ L) (d : 𝕀.DeformationRetract i) : 𝕀.anodyne S i := by
  have key := 𝕀.llp_rlp_anodyne_of_deformation_retract S i d
  rw [naiveFibrations, 𝕀.anodyne_eq_llp_rlp S hS, rlp_llp_rlp] at key
  rw [𝕀.anodyne_eq_llp_rlp S hS]
  exact key

theorem exists_deformation_retract_of_anodyne [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [IsSaturated.{v} (monomorphisms C)]
    (hS : S ≤ MorphismProperty.monomorphisms C) {K L : C}
    (i : K ⟶ L) (hi : 𝕀.anodyne S i) (hK : 𝕀.IsFibrant S K) (hL : 𝕀.IsFibrant S L) :
    Nonempty (𝕀.DeformationRetract i) := by
  have : Mono i := 𝕀.anodyne_le_monomorphisms S hS i hi
  obtain ⟨r, hr⟩ := 𝕀.exists_fac_of_isFibrant S hK hi (𝟙 K)
  have hc : 𝕀.endpoints K ≫ 𝕀.I.map i ≫ (𝕀.contraction).app L =
      coprod.map i i ≫ coprod.desc (𝟙 L) (r ≫ i) := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, inl_endpoints, endpoint_naturality_assoc,
        endpoint_app_contraction_app, coprod.inl_map_assoc, coprod.inl_desc]
    · rw [← Category.assoc, inr_endpoints, endpoint_naturality_assoc,
        endpoint_app_contraction_app, coprod.inr_map_assoc, coprod.inr_desc,
        ← Category.assoc, hr]
      exact (Category.comp_id i).trans (Category.id_comp i).symm
  obtain ⟨H, hH⟩ := 𝕀.exists_fac_of_isFibrant S hL
    ((𝕀.isAnodyneClass_anodyne S).bothBox_mem i this hi)
    (pushout.desc (𝕀.I.map i ≫ (𝕀.contraction).app L) (coprod.desc (𝟙 L) (r ≫ i)) hc)
  have hH₁ : 𝕀.I.map i ≫ H = 𝕀.I.map i ≫ (𝕀.contraction).app L :=
    𝕀.map_comp_eq_of_bothBox_comp_eq i hH
  have hH₂ : 𝕀.endpoints L ≫ H = coprod.desc (𝟙 L) (r ≫ i) :=
    𝕀.endpoints_comp_eq_of_bothBox_comp_eq i hH
  refine ⟨⟨r, H, hr, ?_, ?_, hH₁⟩⟩
  · have := congrArg (coprod.inl ≫ ·) hH₂
    simp only [← Category.assoc, inl_endpoints, coprod.inl_desc] at this
    exact this
  · have := congrArg (coprod.inr ≫ ·) hH₂
    simp only [← Category.assoc, inr_endpoints, coprod.inr_desc] at this
    exact this

omit [HasTerminal C] in
theorem exists_deformation_retract_of_rlp_monomorphisms [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] {X Y : C} (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) : ∃ d : 𝕀.DeformationRetract s, d.retraction = p := by
  have : Mono s := mono_of_mono_fac hs
  have hc : 𝕀.endpoints Y ≫ (𝕀.contraction).app Y ≫ s =
      coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s) := by
    refine coprod.hom_ext ?_ ?_
    · rw [𝕀.inl_endpoints_assoc Y, endpoint_app_contraction_app_assoc,
        coprod.inl_map_assoc, coprod.inl_desc, Category.comp_id]
    · rw [𝕀.inr_endpoints_assoc Y, endpoint_app_contraction_app_assoc,
        coprod.inr_map_assoc, coprod.inr_desc, reassoc_of% hs]
  have := hp (𝕀.bothBox s) (𝕀.mono_bothBox s this)
  have sq : CommSq (pushout.desc ((𝕀.contraction).app Y ≫ s) (coprod.desc (𝟙 X) (p ≫ s)) hc :
      𝕀.bothBoxSource s ⟶ X) (𝕀.bothBox s) p ((𝕀.contraction).app X ≫ p) := ⟨by
    refine pushout.hom_ext ?_ ?_
    · rw [pushout.inl_desc_assoc, 𝕀.inl_bothBox_assoc, map_contraction_app_assoc,
        Category.assoc, hs]
    · rw [pushout.inr_desc_assoc, 𝕀.inr_bothBox_assoc]
      refine coprod.hom_ext ?_ ?_
      · rw [coprod.inl_desc_assoc, 𝕀.inl_endpoints_assoc X,
          endpoint_app_contraction_app_assoc, Category.id_comp]
      · rw [coprod.inr_desc_assoc, 𝕀.inr_endpoints_assoc X,
          endpoint_app_contraction_app_assoc, Category.assoc, hs, Category.comp_id]⟩
  obtain ⟨⟨⟨l, hl, -⟩⟩⟩ := this.sq_hasLift sq
  have e₁ : 𝕀.endpoints X ≫ l = coprod.desc (𝟙 X) (p ≫ s) :=
    𝕀.endpoints_comp_eq_of_bothBox_comp_eq s hl
  have e₂ : 𝕀.I.map s ≫ l = (𝕀.contraction).app Y ≫ s := 𝕀.map_comp_eq_of_bothBox_comp_eq s hl
  refine ⟨⟨p, l, hs, ?_, ?_, ?_⟩, rfl⟩
  · rw [← 𝕀.inl_endpoints X, Category.assoc, e₁, coprod.inl_desc]
  · rw [← 𝕀.inr_endpoints X, Category.assoc, e₁, coprod.inr_desc]
  · rw [e₂, 𝕀.map_contraction_app]

end HomotopicalAlgebra.ExactCylinder
