import Atoms.Homotopical.HomotopyColimit.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Whiskering

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A] {I : Type v} [SmallCategory I]

theorem monomorphisms_eq_llp_rlp_monomorphisms :
    MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) =
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.llp := by
  rw [monomorphisms_eq_saturation_cellularGenerators, rlp_saturation.{v},
    saturation_eq_llp_rlp.{v}]

section FreeImages

variable {ι : Type v} {X Y : ι → Aᵒᵖ ⥤ Type v} (f : ∀ t, X t ⟶ Y t)

theorem rlp_ofHoms_evaluationLeftAdjoint_map_iff {F G : I ⥤ Aᵒᵖ ⥤ Type v} (p : F ⟶ G) :
    (MorphismProperty.ofHoms fun q : I × ι ↦
        (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) q.1).map (f q.2)).rlp p ↔
      ∀ i : I, (MorphismProperty.ofHoms f).rlp (p.app i) := by
  constructor
  · rintro hp i _ _ _ ⟨t⟩
    exact ((evaluationAdjunctionRight _ i).hasLiftingProperty_iff _ _).1
      (hp _ (MorphismProperty.ofHoms.mk (i, t)))
  · rintro hp _ _ _ ⟨⟨i, t⟩⟩
    exact ((evaluationAdjunctionRight _ i).hasLiftingProperty_iff _ _).2
      (hp i _ (MorphismProperty.ofHoms.mk t))

theorem llp_rlp_app_of_llp_rlp_ofHoms_evaluationLeftAdjoint_map {F G : I ⥤ Aᵒᵖ ⥤ Type v}
    {k : F ⟶ G}
    (hk : (MorphismProperty.ofHoms fun q : I × ι ↦
        (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) q.1).map (f q.2)).rlp.llp k) (i : I) :
    (MorphismProperty.ofHoms f).rlp.llp (k.app i) := by
  intro _ _ q hq
  refine ((evaluationAdjunctionLeft (Aᵒᵖ ⥤ Type v) i).hasLiftingProperty_iff k q).2
    (hk _ ((rlp_ofHoms_evaluationLeftAdjoint_map_iff f _).2 fun i' ↦ ?_))
  have e : ((evaluationRightAdjoint (Aᵒᵖ ⥤ Type v) i).map q).app i' =
      Limits.Pi.map fun _ : i' ⟶ i ↦ q :=
    Pi.hom_ext _ _ fun g ↦ (Pi.lift_π _ g).trans (Pi.map_π (fun _ : i' ⟶ i ↦ q) g).symm
  rw [e]
  exact MorphismProperty.limMap _ fun _ ↦ hq

end FreeImages

theorem rlp_projectiveGenerators_iff {F G : I ⥤ Aᵒᵖ ⥤ Type v} (p : F ⟶ G) :
    (projectiveGenerators A I).rlp p ↔
      ∀ i : I, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (p.app i) := by
  rw [monomorphisms_eq_saturation_cellularGenerators, rlp_saturation.{v}]
  exact rlp_ofHoms_evaluationLeftAdjoint_map_iff (fun i : CellularIndex A ↦ i.subfunctor.ι) p

theorem mono_app_of_projectiveCofibrations {F G : I ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G}
    (hc : projectiveCofibrations A I c) (i : I) : Mono (c.app i) := by
  have h := llp_rlp_app_of_llp_rlp_ofHoms_evaluationLeftAdjoint_map
    (fun i : CellularIndex A ↦ i.subfunctor.ι) hc i
  rw [show (ofHoms fun i : CellularIndex A ↦ i.subfunctor.ι) = cellularGenerators A from rfl,
    ← saturation_eq_llp_rlp.{v}, ← monomorphisms_eq_saturation_cellularGenerators] at h
  exact h

theorem projectiveCofibrations_initial_to_projectiveReplacement (F : I ⥤ Aᵒᵖ ⥤ Type v) :
    projectiveCofibrations A I (initial.to ((projectiveReplacement A I).obj F)) := by
  have e : initial.to ((projectiveReplacement A I).obj F) =
      (projectiveFactorization A I).i.app ((initialArrow _).obj F) :=
    initial.hom_ext _ _
  rw [e]
  exact (projectiveFactorization A I).hi _

theorem rlp_monomorphisms_projectiveReplacementπ_app (F : I ⥤ Aᵒᵖ ⥤ Type v) (i : I) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp
      (((projectiveReplacementπ A I).app F).app i) :=
  (rlp_projectiveGenerators_iff _).1 ((projectiveFactorization A I).hp ((initialArrow _).obj F)) i

theorem exists_lift_of_projectiveCofibrations {F G H K : I ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G}
    (hc : projectiveCofibrations A I c) {p : H ⟶ K}
    (hp : ∀ i : I, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (p.app i))
    (f : F ⟶ H) (g : G ⟶ K) (w : c ≫ g = f ≫ p) : ∃ l : G ⟶ H, c ≫ l = f ∧ l ≫ p = g := by
  have := hc _ ((rlp_projectiveGenerators_iff p).2 hp)
  have sq : CommSq f c p g := ⟨w.symm⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

theorem projectiveCofibrations_map_of_adjunction {K : Type v} [SmallCategory K]
    {Φ : (I ⥤ Aᵒᵖ ⥤ Type v) ⥤ (K ⥤ Aᵒᵖ ⥤ Type v)} {Ψ : (K ⥤ Aᵒᵖ ⥤ Type v) ⥤ (I ⥤ Aᵒᵖ ⥤ Type v)}
    (adj : Φ ⊣ Ψ)
    (h : ∀ ⦃X Y : K ⥤ Aᵒᵖ ⥤ Type v⦄ (q : X ⟶ Y), (projectiveGenerators A K).rlp q →
      (projectiveGenerators A I).rlp (Ψ.map q))
    {F G : I ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G} (hc : projectiveCofibrations A I c) :
    projectiveCofibrations A K (Φ.map c) :=
  fun _ _ q hq ↦ (adj.hasLiftingProperty_iff c q).2 (hc _ (h q hq))

section Restriction

variable {K : Type v} [SmallCategory K] (u : K ⥤ I) (i : I)

private noncomputable def restrictFreeι (X : Aᵒᵖ ⥤ Type v) (k : K) (h : i ⟶ u.obj k) :
    X ⟶ (u ⋙ (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).obj X).obj k :=
  Sigma.ι (fun _ : i ⟶ u.obj k ↦ X) h

variable {u i}

private theorem restrictFree_hom_ext {X W : Aᵒᵖ ⥤ Type v} {k : K}
    {a b : (u ⋙ (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).obj X).obj k ⟶ W}
    (h : ∀ h' : i ⟶ u.obj k, restrictFreeι u i X k h' ≫ a = restrictFreeι u i X k h' ≫ b) :
    a = b :=
  Sigma.hom_ext (f := fun _ : i ⟶ u.obj k ↦ X) a b h

private theorem restrictFreeι_map (X : Aᵒᵖ ⥤ Type v) {k k' : K} (φ : k ⟶ k') (h : i ⟶ u.obj k) :
    restrictFreeι u i X k h ≫ (u ⋙ (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).obj X).map φ =
      restrictFreeι u i X k' (h ≫ u.map φ) :=
  Sigma.ι_desc _ _

private theorem restrictFreeι_whiskerLeft_map {X Y : Aᵒᵖ ⥤ Type v} (m : X ⟶ Y) (k : K)
    (h : i ⟶ u.obj k) :
    restrictFreeι u i X k h ≫ (Functor.whiskerLeft u
        ((evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).map m)).app k =
      m ≫ restrictFreeι u i Y k h :=
  Sigma.ι_desc _ _

variable (u i)

theorem hasLiftingProperty_whiskerLeft_free_map {M : Type v} (ℓ : M → K)
    (e : ∀ μ, i ⟶ u.obj (ℓ μ))
    (he : ∀ k, Function.Bijective fun p : Σ μ, ℓ μ ⟶ k ↦ e p.1 ≫ u.map p.2)
    {X Y : Aᵒᵖ ⥤ Type v} (m : X ⟶ Y) {H L : K ⥤ Aᵒᵖ ⥤ Type v} (q : H ⟶ L)
    (hq : ∀ k, HasLiftingProperty m (q.app k)) :
    HasLiftingProperty
      (Functor.whiskerLeft u ((evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).map m)) q := by
  constructor
  intro f g sq
  have hl : ∀ μ : M, ∃ l : Y ⟶ H.obj (ℓ μ),
      m ≫ l = restrictFreeι u i X (ℓ μ) (e μ) ≫ f.app _ ∧
        l ≫ q.app _ = restrictFreeι u i Y (ℓ μ) (e μ) ≫ g.app _ := by
    intro μ
    have := hq (ℓ μ)
    have h := congr_app sq.w (ℓ μ)
    simp only [NatTrans.comp_app] at h
    have sq' : CommSq (restrictFreeι u i X (ℓ μ) (e μ) ≫ f.app _) m
        (q.app _) (restrictFreeι u i Y (ℓ μ) (e μ) ≫ g.app _) :=
      ⟨by rw [Category.assoc, h, ← Category.assoc, restrictFreeι_whiskerLeft_map,
        Category.assoc]⟩
    exact ⟨sq'.lift, sq'.fac_left, sq'.fac_right⟩
  choose l hl₁ hl₂ using hl
  let fac : ∀ k, (Σ μ, ℓ μ ⟶ k) ≃ (i ⟶ u.obj k) := fun k ↦ Equiv.ofBijective _ (he k)
  obtain ⟨α, hα⟩ : ∃ α : ∀ k : K,
      (u ⋙ (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) i).obj Y).obj k ⟶ H.obj k,
      ∀ (k : K) (μ : M) (φ : ℓ μ ⟶ k),
        restrictFreeι u i Y k (e μ ≫ u.map φ) ≫ α k = l μ ≫ H.map φ := by
    refine ⟨fun k ↦ Sigma.desc fun h : i ⟶ u.obj k ↦
      l ((fac k).symm h).1 ≫ H.map ((fac k).symm h).2, fun k μ φ ↦ ?_⟩
    refine (Sigma.ι_desc _ _).trans ?_
    have hs : (fac k).symm (e μ ≫ u.map φ) = ⟨μ, φ⟩ := (fac k).symm_apply_apply ⟨μ, φ⟩
    rw [hs]
  refine ⟨⟨{ l := { app := α, naturality := ?_ }, fac_left := ?_, fac_right := ?_ }⟩⟩
  · intro k k' ψ
    refine restrictFree_hom_ext fun h ↦ ?_
    obtain ⟨⟨μ, φ⟩, rfl⟩ := (he k).2 h
    rw [← Category.assoc, restrictFreeι_map, Category.assoc, ← u.map_comp, hα,
      ← Category.assoc, hα, Category.assoc, ← H.map_comp]
  · refine NatTrans.ext (funext fun k ↦ restrictFree_hom_ext fun h ↦ ?_)
    obtain ⟨⟨μ, φ⟩, rfl⟩ := (he k).2 h
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, restrictFreeι_whiskerLeft_map, Category.assoc, hα, ← Category.assoc,
      hl₁, Category.assoc, ← f.naturality, ← Category.assoc, restrictFreeι_map]
  · refine NatTrans.ext (funext fun k ↦ restrictFree_hom_ext fun h ↦ ?_)
    obtain ⟨⟨μ, φ⟩, rfl⟩ := (he k).2 h
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, hα, Category.assoc, q.naturality, ← Category.assoc, hl₂,
      Category.assoc, ← g.naturality, ← Category.assoc, restrictFreeι_map]

end Restriction

theorem projectiveCofibrations_whiskerLeft_of_bijective {K : Type v} [SmallCategory K]
    (u : K ⥤ I) (hu : ∀ i, ∃ (M : Type v) (ℓ : M → K) (e : ∀ μ, i ⟶ u.obj (ℓ μ)),
      ∀ k, Function.Bijective fun p : Σ μ, ℓ μ ⟶ k ↦ e p.1 ≫ u.map p.2)
    {F G : I ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G} (hc : projectiveCofibrations A I c) :
    projectiveCofibrations A K (Functor.whiskerLeft u c) := by
  refine projectiveCofibrations_map_of_adjunction (u.ranAdjunction (Aᵒᵖ ⥤ Type v))
    (fun _ _ q hq ↦ ?_) hc
  rintro _ _ _ ⟨⟨i, idx⟩⟩
  refine (u.ranAdjunction (Aᵒᵖ ⥤ Type v)).hasLiftingProperty_iff _ _ |>.1 ?_
  obtain ⟨M, ℓ, e, he⟩ := hu i
  exact hasLiftingProperty_whiskerLeft_free_map u i ℓ e he _ q fun k ↦
    (rlp_projectiveGenerators_iff q).1 hq k _ (MorphismProperty.monomorphisms.infer_property _)

theorem projectiveCofibrations_whiskerLeft_proj {J : Type v} [SmallCategory J] (u : I ⥤ J)
    (j : J) {F G : I ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G} (hc : projectiveCofibrations A I c) :
    projectiveCofibrations A (CostructuredArrow u j)
      (Functor.whiskerLeft (CostructuredArrow.proj u j) c) := by
  refine projectiveCofibrations_whiskerLeft_of_bijective _ (fun i ↦ ⟨u.obj i ⟶ j,
    CostructuredArrow.mk, fun _ ↦ 𝟙 i, fun k ↦ ⟨?_, fun h ↦ ?_⟩⟩) hc
  · rintro ⟨μ, φ⟩ ⟨μ', φ'⟩ h
    have h' : φ.left = φ'.left :=
      (Category.id_comp _).symm.trans (h.trans (Category.id_comp _))
    have hμ : μ = μ' := by
      have h₁ := CostructuredArrow.w φ
      rw [h'] at h₁
      exact h₁.symm.trans (CostructuredArrow.w φ')
    subst hμ
    obtain rfl : φ = φ' := CostructuredArrow.hom_ext _ _ h'
    rfl
  · exact ⟨⟨u.map h ≫ k.hom, CostructuredArrow.homMk' k h⟩, Category.id_comp _⟩

theorem projectiveCofibrations_whiskerLeft_ι {C : Type v} [SmallCategory C] (P : ObjectProperty C)
    (hP : ∀ ⦃c c' : C⦄, (c ⟶ c') → P c' → P c)
    {F G : C ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G} (hc : projectiveCofibrations A C c) :
    projectiveCofibrations A P.FullSubcategory (Functor.whiskerLeft P.ι c) := by
  refine projectiveCofibrations_whiskerLeft_of_bijective P.ι (fun j ↦ ⟨ULift.{v} (PLift (P j)),
    fun hj ↦ (⟨j, hj.down.down⟩ : P.FullSubcategory), fun _ ↦ 𝟙 j, fun k ↦ ⟨?_, fun h ↦ ?_⟩⟩) hc
  · rintro ⟨⟨⟨hj⟩⟩, φ⟩ ⟨⟨⟨hj'⟩⟩, φ'⟩ h
    obtain rfl : φ = φ' := ObjectProperty.hom_ext _ (by simpa using h)
    rfl
  · exact ⟨⟨⟨⟨hP h k.property⟩⟩, ObjectProperty.homMk h⟩, by simp⟩

theorem projectiveCofibrations_whiskerLeft_map {X Y : Aᵒᵖ ⥤ Type v} (g : Y ⟶ X)
    {F G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G}
    (hc : projectiveCofibrations A _ c) :
    projectiveCofibrations A (CostructuredArrow yoneda Y)
      (Functor.whiskerLeft (CostructuredArrow.map g) c) := by
  refine projectiveCofibrations_whiskerLeft_of_bijective _ (fun i ↦
    ⟨{μ : yoneda.obj i.left ⟶ Y // μ ≫ g = i.hom}, fun μ ↦ CostructuredArrow.mk μ.1,
      fun μ ↦ CostructuredArrow.homMk (𝟙 i.left) (by simp [μ.2]),
      fun k ↦ ⟨?_, fun h ↦ ?_⟩⟩) hc
  · rintro ⟨μ, φ⟩ ⟨μ', φ'⟩ h
    have h' : φ.left = φ'.left := by simpa using congrArg CommaMorphism.left h
    have hμ : μ = μ' := Subtype.ext (by
      have h₁ := CostructuredArrow.w φ
      rw [h'] at h₁
      exact h₁.symm.trans (CostructuredArrow.w φ'))
    subst hμ
    obtain rfl : φ = φ' := CostructuredArrow.hom_ext _ _ h'
    rfl
  · refine ⟨⟨⟨yoneda.map h.left ≫ k.hom, by simpa using CostructuredArrow.w h⟩,
      CostructuredArrow.homMk h.left rfl⟩, CostructuredArrow.hom_ext _ _ (by simp)⟩

theorem projectiveCofibrations_whiskerLeft_of_isRightAdjoint {J : Type v} [SmallCategory J]
    (u : I ⥤ J) [u.IsRightAdjoint] {F G : J ⥤ Aᵒᵖ ⥤ Type v} {c : F ⟶ G}
    (hc : projectiveCofibrations A J c) :
    projectiveCofibrations A I (Functor.whiskerLeft u c) :=
  projectiveCofibrations_map_of_adjunction
    ((Adjunction.ofIsRightAdjoint u).whiskerLeft (C := Aᵒᵖ ⥤ Type v))
    (fun _ _ q hq ↦ (rlp_projectiveGenerators_iff _).2 fun j ↦
      (rlp_projectiveGenerators_iff q).1 hq (u.leftAdjoint.obj j)) hc

theorem projectiveCofibrations_initial_to_of_isInitial {I : Type v} [SmallCategory I]
    {Z Y : I ⥤ Aᵒᵖ ⥤ Type v} (hZ : IsInitial Z) {c : Z ⟶ Y}
    (hc : projectiveCofibrations A I c) : projectiveCofibrations A I (initial.to Y) := by
  have e : initial.to Y = (initialIsInitial.uniqueUpToIso hZ).hom ≫ c := initial.hom_ext _ _
  rw [e]
  unfold projectiveCofibrations at hc ⊢
  exact MorphismProperty.comp_mem _ _ _ (llp_of_isIso _ _) hc

theorem projectiveCofibrations_initial_to_comp {I J : Type v} [SmallCategory I]
    [SmallCategory J] (u : I ⥤ J) {G : J ⥤ Aᵒᵖ ⥤ Type v}
    (hG : projectiveCofibrations A I (Functor.whiskerLeft u (initial.to G))) :
    projectiveCofibrations A I (initial.to (u ⋙ G)) :=
  projectiveCofibrations_initial_to_of_isInitial
    (initialIsInitial.isInitialObj ((Functor.whiskeringLeft I J (Aᵒᵖ ⥤ Type v)).obj u)) hG

theorem projectiveCofibrations_whiskerRight_of_adjunction {A' : Type v} [SmallCategory A']
    {F : (Aᵒᵖ ⥤ Type v) ⥤ (A'ᵒᵖ ⥤ Type v)} {G : (A'ᵒᵖ ⥤ Type v) ⥤ (Aᵒᵖ ⥤ Type v)}
    (adj : F ⊣ G) (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f))
    {K L : I ⥤ Aᵒᵖ ⥤ Type v} {c : K ⟶ L} (hc : projectiveCofibrations A I c) :
    projectiveCofibrations A' I (Functor.whiskerRight c F) := by
  intro _ _ q hq
  refine ((adj.whiskerRight (C := I)).hasLiftingProperty_iff c q).2 (hc _ ?_)
  refine (rlp_projectiveGenerators_iff _).2 fun i _ _ m hm ↦ ?_
  have : Mono m := hm
  exact (adj.hasLiftingProperty_iff m (q.app i)).1
    ((rlp_projectiveGenerators_iff q).1 hq i _ (hF m this))

theorem projectiveCofibrations_initial_to_whiskerRight {A' : Type v} [SmallCategory A']
    {F : (Aᵒᵖ ⥤ Type v) ⥤ (A'ᵒᵖ ⥤ Type v)} {G : (A'ᵒᵖ ⥤ Type v) ⥤ (Aᵒᵖ ⥤ Type v)}
    (adj : F ⊣ G) (hF : ∀ {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y), Mono f → Mono (F.map f))
    {K : I ⥤ Aᵒᵖ ⥤ Type v} (hK : projectiveCofibrations A I (initial.to K)) :
    projectiveCofibrations A' I (initial.to (K ⋙ F)) :=
  haveI : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  projectiveCofibrations_initial_to_of_isInitial
    (Functor.isInitial fun i ↦ (initialIsInitial.isInitialObj
      ((evaluation _ (Aᵒᵖ ⥤ Type v)).obj i)).isInitialObj F)
    (projectiveCofibrations_whiskerRight_of_adjunction adj hF hK)

theorem projectiveCofibrations_initial_to_pointwiseLeftKanExtension {S : Type v}
    [SmallCategory S] (L : I ⥤ S)
    {P : I ⥤ Aᵒᵖ ⥤ Type v} (hP : projectiveCofibrations A I (initial.to P)) :
    projectiveCofibrations A S (initial.to (L.pointwiseLeftKanExtension P)) := by
  let adj := Functor.lanAdjunction (H := Aᵒᵖ ⥤ Type v) L
  have h1 : projectiveCofibrations A S (L.lan.map (initial.to P)) :=
    projectiveCofibrations_map_of_adjunction adj
      (fun _ _ q hq ↦ (rlp_projectiveGenerators_iff _).2 fun i ↦
        (rlp_projectiveGenerators_iff q).1 hq (L.obj i)) hP
  have := adj.leftAdjoint_preservesColimits
  exact projectiveCofibrations_initial_to_of_isInitial (initialIsInitial.isInitialObj L.lan)
    (c := L.lan.map (initial.to P) ≫ (Functor.leftKanExtensionUnique _ (L.lanUnit.app P) _
      (L.pointwiseLeftKanExtensionUnit P)).hom)
    ((projectiveGenerators A S).rlp.llp.comp_mem _ _ h1 (llp_of_isIso _ _))

end Atoms.Homotopical
