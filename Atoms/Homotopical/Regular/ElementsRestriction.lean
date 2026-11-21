import Atoms.ForMathlib.CategoryTheory.Limits.Types.Pushouts
import Atoms.Homotopical.Regular.Presheaf

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

noncomputable def colimitPreMap {Z Y X : Aᵒᵖ ⥤ Type v} (m : Z ⟶ Y) (g : Y ⟶ X) {k : Z ⟶ X}
    (hk : m ≫ g = k) (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v) :
    colimit (CostructuredArrow.map k ⋙ G) ⟶ colimit (CostructuredArrow.map g ⋙ G) :=
  eqToHom (by subst hk; rfl) ≫ colimit.pre (CostructuredArrow.map g ⋙ G) (CostructuredArrow.map m)

@[reassoc]
theorem ι_colimitPreMap {Z Y X : Aᵒᵖ ⥤ Type v} (m : Z ⟶ Y) (g : Y ⟶ X) {k : Z ⟶ X}
    (hk : m ≫ g = k) (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v)
    (c : CostructuredArrow yoneda Z) :
    colimit.ι (CostructuredArrow.map k ⋙ G) c ≫ colimitPreMap m g hk G =
      G.map (CostructuredArrow.homMk (𝟙 c.left) (by simp [← hk])) ≫
        colimit.ι (CostructuredArrow.map g ⋙ G) ((CostructuredArrow.map m).obj c) := by
  subst hk
  change colimit.ι (CostructuredArrow.map m ⋙ CostructuredArrow.map g ⋙ G) c ≫
      (eqToHom rfl ≫ colimit.pre (CostructuredArrow.map g ⋙ G) (CostructuredArrow.map m)) = _
  rw [eqToHom_refl, Category.id_comp, colimit.ι_pre]
  refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
  exact (G.map_id _).symm.trans (congrArg G.map (CostructuredArrow.hom_ext _ _ rfl))

theorem mono_colimitPreMap {Z Y X : Aᵒᵖ ⥤ Type v} (m : Z ⟶ Y) [Mono m] (g : Y ⟶ X) {k : Z ⟶ X}
    (hk : m ≫ g = k) (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v)
    (hG : projectiveCofibrations A (CostructuredArrow yoneda Y)
      (initial.to (CostructuredArrow.map g ⋙ G))) :
    Mono (colimitPreMap m g hk G) := by
  subst hk
  have h : elementsSieve m ≤ ⊤ := fun _ _ ↦ trivial
  have hF : projectiveCofibrations A
      (⊤ : ObjectProperty (CostructuredArrow yoneda Y)).FullSubcategory
      (initial.to ((⊤ : ObjectProperty _).ι ⋙ CostructuredArrow.map g ⋙ G)) :=
    projectiveCofibrations_initial_to_comp _
      (projectiveCofibrations_whiskerLeft_ι ⊤ (fun _ _ _ _ ↦ trivial) hG)
  have := mono_sievePre h (fun _ _ φ ↦ elementsSieve_of_hom m φ) _ hF
  have := (toElementsSieve m).asEquivalence.isRightAdjoint_functor
  have : (⊤ : ObjectProperty (CostructuredArrow yoneda Y)).ι.EssSurj :=
    ⟨fun c ↦ ⟨⟨c, trivial⟩, ⟨Iso.refl _⟩⟩⟩
  have : (⊤ : ObjectProperty (CostructuredArrow yoneda Y)).ι.IsEquivalence := { }
  have := (⊤ : ObjectProperty (CostructuredArrow yoneda Y)).ι.asEquivalence.isRightAdjoint_functor
  have i₁ : IsIso (colimit.pre ((elementsSieve m).ι ⋙ CostructuredArrow.map g ⋙ G)
      (toElementsSieve m)) := inferInstance
  have i₂ : IsIso (colimit.pre (CostructuredArrow.map g ⋙ G)
      (⊤ : ObjectProperty (CostructuredArrow yoneda Y)).ι) := inferInstance
  have e : colimitPreMap m g rfl G =
      colimit.pre ((elementsSieve m).ι ⋙ CostructuredArrow.map g ⋙ G) (toElementsSieve m) ≫
        sievePre h (CostructuredArrow.map g ⋙ G) ≫
          colimit.pre (CostructuredArrow.map g ⋙ G) (⊤ : ObjectProperty _).ι := by
    refine colimit.hom_ext fun c ↦ ?_
    rw [ι_colimitPreMap]
    refine Eq.trans ?_ (colimit.ι_pre_assoc ((elementsSieve m).ι ⋙ CostructuredArrow.map g ⋙ G)
      (toElementsSieve m) c _).symm
    rw [ι_sievePre_assoc, colimit.ι_pre]
    refine (congrArg (· ≫ _) ?_).trans (Category.id_comp _)
    exact (congrArg G.map (CostructuredArrow.hom_ext _ _ rfl)).trans (G.map_id _)
  have hm : Mono (colimit.pre ((elementsSieve m).ι ⋙ CostructuredArrow.map g ⋙ G)
      (toElementsSieve m) ≫ sievePre h (CostructuredArrow.map g ⋙ G) ≫
        colimit.pre (CostructuredArrow.map g ⋙ G) (⊤ : ObjectProperty _).ι) := inferInstance
  rw [e]
  exact hm

section Pushout

def toMapMk {Y X : Aᵒᵖ ⥤ Type v} (g : Y ⟶ X) (c : CostructuredArrow yoneda X)
    (y : yoneda.obj c.left ⟶ Y) (hy : y ≫ g = c.hom) :
    c ⟶ (CostructuredArrow.map g).obj (CostructuredArrow.mk y) :=
  CostructuredArrow.homMk (𝟙 c.left) (by simp [hy])

@[simp]
theorem toMapMk_left {Y X : Aᵒᵖ ⥤ Type v} (g : Y ⟶ X) (c : CostructuredArrow yoneda X)
    (y : yoneda.obj c.left ⟶ Y) (hy : y ≫ g = c.hom) : (toMapMk g c y hy).left = 𝟙 c.left :=
  rfl

@[reassoc]
theorem map_comp_ι_map {Y X : Aᵒᵖ ⥤ Type v} {g : Y ⟶ X}
    (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v) {c : CostructuredArrow yoneda X}
    {d d' : CostructuredArrow yoneda Y} (θ : c ⟶ (CostructuredArrow.map g).obj d)
    (θ' : c ⟶ (CostructuredArrow.map g).obj d') (ψ : d ⟶ d')
    (h : θ ≫ (CostructuredArrow.map g).map ψ = θ') :
    G.map θ ≫ colimit.ι (CostructuredArrow.map g ⋙ G) d =
      G.map θ' ≫ colimit.ι (CostructuredArrow.map g ⋙ G) d' := by
  rw [← h, G.map_comp, Category.assoc]
  exact congrArg (G.map θ ≫ ·) (colimit.w (CostructuredArrow.map g ⋙ G) ψ).symm

private theorem exists_comp_eq_of_apply_eq {Xi X : Aᵒᵖ ⥤ Type v} (gi : Xi ⟶ X) {a : A}
    (z : yoneda.obj a ⟶ X) (x : Xi.obj (Opposite.op a))
    (hx : gi.app (Opposite.op a) x = yonedaEquiv z) : ∃ y : yoneda.obj a ⟶ Xi, y ≫ gi = z :=
  ⟨yonedaEquiv.symm x, yonedaEquiv.injective (by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hx)⟩

private theorem map_comp_eq_of_forall_eq {Xi X : Aᵒᵖ ⥤ Type v} (gi : Xi ⟶ X)
    (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v) {P : Aᵒᵖ ⥤ Type v}
    (t : colimit (CostructuredArrow.map gi ⋙ G) ⟶ P) (φ : ∀ c, G.obj c ⟶ P)
    (hφ : ∀ (c : CostructuredArrow yoneda X) (y : yoneda.obj c.left ⟶ Xi) (hy : y ≫ gi = c.hom),
      φ c = G.map (toMapMk gi c y hy) ≫
        colimit.ι (CostructuredArrow.map gi ⋙ G) (CostructuredArrow.mk y) ≫ t)
    {c c' : CostructuredArrow yoneda X} (ψ : c ⟶ c') (y : yoneda.obj c'.left ⟶ Xi)
    (hy : y ≫ gi = c'.hom) : G.map ψ ≫ φ c' = φ c := by
  have hy' : (yoneda.map ψ.left ≫ y) ≫ gi = c.hom := by
    rw [Category.assoc, hy, CostructuredArrow.w ψ]
  rw [hφ c' y hy, hφ c _ hy', ← G.map_comp_assoc]
  symm
  refine map_comp_ι_map_assoc G _ _ (CostructuredArrow.homMk ψ.left ?_ :
    CostructuredArrow.mk (yoneda.map ψ.left ≫ y) ⟶ CostructuredArrow.mk y) ?_ _
  · simp
  · exact CostructuredArrow.hom_ext _ _ (by simp)

private theorem pre_comp_desc_of_forall_eq {Xi X : Aᵒᵖ ⥤ Type v} (gi : Xi ⟶ X)
    (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v) (cc : Cocone G)
    (t : colimit (CostructuredArrow.map gi ⋙ G) ⟶ cc.pt)
    (hφ : ∀ (c : CostructuredArrow yoneda X) (y : yoneda.obj c.left ⟶ Xi) (hy : y ≫ gi = c.hom),
      cc.ι.app c = G.map (toMapMk gi c y hy) ≫
        colimit.ι (CostructuredArrow.map gi ⋙ G) (CostructuredArrow.mk y) ≫ t) :
    colimit.pre G (CostructuredArrow.map gi) ≫ colimit.desc G cc = t := by
  refine colimit.hom_ext fun d ↦ ?_
  rw [colimit.ι_pre_assoc, colimit.ι_desc]
  refine (hφ _ d.hom rfl).trans ?_
  refine (map_comp_ι_map_assoc G _ (𝟙 _) (CostructuredArrow.homMk (𝟙 d.left) ?_ :
    CostructuredArrow.mk d.hom ⟶ d) ?_ _).trans ?_
  · simp
  · exact CostructuredArrow.hom_ext _ _ (by simp)
  · rw [G.map_id, Category.id_comp]

theorem isPushout_colimitPreMap {X₀ X₁ X₂ X : Aᵒᵖ ⥤ Type v} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂}
    {g₁ : X₁ ⟶ X} {g₂ : X₂ ⟶ X} (h : IsPushout f₁ f₂ g₁ g₂) [Mono f₁] {k : X₀ ⟶ X}
    (hk₁ : f₁ ≫ g₁ = k) (hk₂ : f₂ ≫ g₂ = k) (G : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v) :
    IsPushout (colimitPreMap f₁ g₁ hk₁ G) (colimitPreMap f₂ g₂ hk₂ G)
      (colimit.pre G (CostructuredArrow.map g₁)) (colimit.pre G (CostructuredArrow.map g₂)) := by
  have : Mono g₂ := Adhesive.mono_of_isPushout_of_mono_left h
  have hpb := Adhesive.isPullback_of_isPushout_of_mono_left h
  have hcov : ∀ c : CostructuredArrow yoneda X, (∃ y₁ : yoneda.obj c.left ⟶ X₁, y₁ ≫ g₁ = c.hom) ∨
      ∃ y₂ : yoneda.obj c.left ⟶ X₂, y₂ ≫ g₂ = c.hom := by
    intro c
    exact (Types.eq_or_eq_of_isPushout
        (h.map ((evaluation Aᵒᵖ (Type v)).obj (Opposite.op c.left))) (yonedaEquiv c.hom)).imp
      (fun ⟨x, hx⟩ ↦ exists_comp_eq_of_apply_eq g₁ c.hom x hx)
      (fun ⟨x, hx⟩ ↦ exists_comp_eq_of_apply_eq g₂ c.hom x hx)
  have w : colimitPreMap f₁ g₁ hk₁ G ≫ colimit.pre G (CostructuredArrow.map g₁) =
      colimitPreMap f₂ g₂ hk₂ G ≫ colimit.pre G (CostructuredArrow.map g₂) := by
    refine colimit.hom_ext fun c ↦ ?_
    rw [ι_colimitPreMap_assoc, ι_colimitPreMap_assoc, colimit.ι_pre, colimit.ι_pre, colimit.w,
      colimit.w]
  have e : ∀ (s : PushoutCocone (colimitPreMap f₁ g₁ hk₁ G) (colimitPreMap f₂ g₂ hk₂ G))
      (c : CostructuredArrow yoneda X) (y₁ : yoneda.obj c.left ⟶ X₁) (hy₁ : y₁ ≫ g₁ = c.hom)
      (y₂ : yoneda.obj c.left ⟶ X₂) (hy₂ : y₂ ≫ g₂ = c.hom),
      G.map (toMapMk g₁ c y₁ hy₁) ≫
          colimit.ι (CostructuredArrow.map g₁ ⋙ G) (CostructuredArrow.mk y₁) ≫ s.inl =
        G.map (toMapMk g₂ c y₂ hy₂) ≫
          colimit.ι (CostructuredArrow.map g₂ ⋙ G) (CostructuredArrow.mk y₂) ≫ s.inr := by
    intro s c y₁ hy₁ y₂ hy₂
    obtain ⟨x₀, hx₁, hx₂⟩ : ∃ x₀, x₀ ≫ f₁ = y₁ ∧ x₀ ≫ f₂ = y₂ :=
      ⟨hpb.lift y₁ y₂ (hy₁.trans hy₂.symm), hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
    have hx : x₀ ≫ k = c.hom := by rw [← hk₁, ← Category.assoc, hx₁, hy₁]
    subst hx₁ hx₂
    have hc := congrArg (G.map (toMapMk k c x₀ hx) ≫ ·)
      (colimit.ι (CostructuredArrow.map k ⋙ G) (CostructuredArrow.mk x₀) ≫= s.condition)
    simp only [ι_colimitPreMap_assoc] at hc
    refine Eq.trans ?_ (hc.trans ?_)
    · rw [← G.map_comp_assoc]
      symm
      refine map_comp_ι_map_assoc G _ _ (CostructuredArrow.homMk (𝟙 _) ?_ :
        (CostructuredArrow.map f₁).obj (CostructuredArrow.mk x₀) ⟶
          CostructuredArrow.mk (x₀ ≫ f₁)) ?_ _
      · simp
      · exact CostructuredArrow.hom_ext _ _ (by simp)
    · rw [← G.map_comp_assoc]
      refine map_comp_ι_map_assoc G _ _ (CostructuredArrow.homMk (𝟙 _) ?_ :
        (CostructuredArrow.map f₂).obj (CostructuredArrow.mk x₀) ⟶
          CostructuredArrow.mk (x₀ ≫ f₂)) ?_ _
      · simp
      · exact CostructuredArrow.hom_ext _ _ (by simp)
  have key : ∀ (s : PushoutCocone (colimitPreMap f₁ g₁ hk₁ G) (colimitPreMap f₂ g₂ hk₂ G))
      (c : CostructuredArrow yoneda X), ∃ φ : G.obj c ⟶ s.pt,
      (∀ (y₁ : yoneda.obj c.left ⟶ X₁) (hy₁ : y₁ ≫ g₁ = c.hom), φ = G.map (toMapMk g₁ c y₁ hy₁) ≫
          colimit.ι (CostructuredArrow.map g₁ ⋙ G) (CostructuredArrow.mk y₁) ≫ s.inl) ∧
        ∀ (y₂ : yoneda.obj c.left ⟶ X₂) (hy₂ : y₂ ≫ g₂ = c.hom), φ = G.map (toMapMk g₂ c y₂ hy₂) ≫
          colimit.ι (CostructuredArrow.map g₂ ⋙ G) (CostructuredArrow.mk y₂) ≫ s.inr := by
    intro s c
    by_cases h₂ : ∃ y₂ : yoneda.obj c.left ⟶ X₂, y₂ ≫ g₂ = c.hom
    · obtain ⟨y₂, hy₂⟩ := h₂
      refine ⟨_, fun y₁ hy₁ ↦ (e s c y₁ hy₁ y₂ hy₂).symm, fun y₂' hy₂' ↦ ?_⟩
      obtain rfl : y₂ = y₂' := (cancel_mono g₂).1 (hy₂.trans hy₂'.symm)
      rfl
    · obtain ⟨y₁, hy₁⟩ := (hcov c).resolve_right h₂
      refine ⟨G.map (toMapMk g₁ c y₁ hy₁) ≫
        colimit.ι (CostructuredArrow.map g₁ ⋙ G) (CostructuredArrow.mk y₁) ≫ s.inl,
        fun y₁' hy₁' ↦ ?_, fun y₂ hy₂ ↦ (h₂ ⟨y₂, hy₂⟩).elim⟩
      obtain rfl : y₁ = y₁' :=
        eq_of_isPushout_of_not_exists h (hy₁.trans hy₁'.symm) (by rwa [hy₁])
      rfl
  choose φ hφ₁ hφ₂ using key
  let cc : PushoutCocone (colimitPreMap f₁ g₁ hk₁ G) (colimitPreMap f₂ g₂ hk₂ G) → Cocone G :=
    fun s ↦
    { pt := s.pt
      ι :=
        { app := φ s
          naturality := by
            intro c c' ψ
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            rcases hcov c' with ⟨y, hy⟩ | ⟨y, hy⟩
            · exact map_comp_eq_of_forall_eq g₁ G s.inl (φ s) (hφ₁ s) ψ y hy
            · exact map_comp_eq_of_forall_eq g₂ G s.inr (φ s) (hφ₂ s) ψ y hy } }
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s ↦ colimit.desc G (cc s)) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_))
  · exact pre_comp_desc_of_forall_eq g₁ G (cc s) s.inl (hφ₁ s)
  · exact pre_comp_desc_of_forall_eq g₂ G (cc s) s.inr (hφ₂ s)
  · refine colimit.hom_ext fun c ↦ ?_
    rw [colimit.ι_desc]
    change colimit.ι G c ≫ m = φ s c
    rcases hcov c with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [hφ₁ s c y hy, ← hm₁, colimit.ι_pre_assoc, ← Category.assoc, colimit.w]
    · rw [hφ₂ s c y hy, ← hm₂, colimit.ι_pre_assoc, ← Category.assoc, colimit.w]

end Pushout

end Atoms.Homotopical
