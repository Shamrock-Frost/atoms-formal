import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.SmallObject

universe w v u

variable {C : Type u} [Category.{v} C] [HasTerminal C]

noncomputable def arrowToTerminal : C ⥤ Arrow C where
  obj X := Arrow.mk (terminal.from X)
  map u := Arrow.homMk u (𝟙 _) (by simp)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

section General

variable [HasPushouts C] {ι : Type w} {U V : ι → C} (f : ∀ i, U i ⟶ V i)
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C]

noncomputable def attachStep : C ⥤ C :=
  arrowToTerminal ⋙ SmallObject.functor f ⋙ Arrow.leftFunc

noncomputable def attachStepUnit : 𝟭 C ⟶ attachStep f where
  app X := SmallObject.ιFunctorObj f (terminal.from X)
  naturality _ _ u :=
    (SmallObject.ιFunctorObj_naturality f (Arrow.homMk u (𝟙 _) (by simp))).symm

@[reassoc]
theorem sigmaι_ρFunctorObj_functorMap {X Y : C}
    (τ : Arrow.mk (terminal.from X) ⟶ Arrow.mk (terminal.from Y))
    (c : SmallObject.FunctorObjIndex f (terminal.from X)) :
    Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) c ≫
        SmallObject.ρFunctorObj f (terminal.from X) ≫ SmallObject.functorMap f τ =
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from Y))
          ⟨c.i, c.t ≫ τ.left, c.b, terminal.hom_ext _ _⟩ ≫
        SmallObject.ρFunctorObj f (terminal.from Y) := by
  obtain ⟨i, t, b, w⟩ := c
  change _ ≫ pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc,
    SmallObject.ι_functorMapTgt_assoc f τ i t b w b (terminal.hom_ext _ _) (t ≫ τ.left) rfl]

theorem sigmaι_ρFunctorObj_attachStep_map {X Y : C} (u : X ⟶ Y)
    (c : SmallObject.FunctorObjIndex f (terminal.from X)) :
    Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) c ≫
        SmallObject.ρFunctorObj f (terminal.from X) ≫ (attachStep f).map u =
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from Y))
          ⟨c.i, c.t ≫ u, c.b, terminal.hom_ext _ _⟩ ≫
        SmallObject.ρFunctorObj f (terminal.from Y) :=
  sigmaι_ρFunctorObj_functorMap f (arrowToTerminal.map u) c

theorem sigmaι_ρFunctorObj_attachStep_map_assoc {X Y : C} (u : X ⟶ Y)
    (c : SmallObject.FunctorObjIndex f (terminal.from X)) {Z : C} (h : (attachStep f).obj Y ⟶ Z) :
    Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) c ≫
        SmallObject.ρFunctorObj f (terminal.from X) ≫ (attachStep f).map u ≫ h =
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from Y))
          ⟨c.i, c.t ≫ u, c.b, terminal.hom_ext _ _⟩ ≫
        SmallObject.ρFunctorObj f (terminal.from Y) ≫ h := by
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm.trans ((Category.assoc _ _ _).symm.trans
    ((sigmaι_ρFunctorObj_attachStep_map f u c =≫ h).trans (Category.assoc _ _ _)))

omit [HasPushouts C] in
theorem sigmaι_functorObjTgtFamily_mk_eq {X : C} {i : ι} {t t' : U i ⟶ X}
    (h : t = t') (b : V i ⟶ ⊤_ C) (w : t ≫ terminal.from X = f i ≫ b) :
    Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) ⟨i, t, b, w⟩ =
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X))
        ⟨i, t', b, terminal.hom_ext _ _⟩ := by
  subst h
  rfl

theorem attachStep_obj_hom_ext {X Q : C} {m₁ m₂ : (attachStep f).obj X ⟶ Q}
    (h₁ : (attachStepUnit f).app X ≫ m₁ = (attachStepUnit f).app X ≫ m₂)
    (h₂ : ∀ d : SmallObject.FunctorObjIndex f (terminal.from X),
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) d ≫
          SmallObject.ρFunctorObj f (terminal.from X) ≫ m₁ =
        Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from X)) d ≫
          SmallObject.ρFunctorObj f (terminal.from X) ≫ m₂) :
    m₁ = m₂ :=
  pushout.hom_ext h₁ (Sigma.hom_ext _ _ h₂)

end General

section Saturation

variable [HasPushouts C] [HasCoproducts.{v} C] {ι : Type v} {U V : ι → C}

theorem attachStepUnit_mem_saturation (f : ∀ i, U i ⟶ V i) (X : C) :
    saturation.{v} (MorphismProperty.ofHoms f) ((attachStepUnit f).app X) := by
  have := IsCellularlyClosed.isStableUnderCoproducts.{v}
    (saturation.{v} (MorphismProperty.ofHoms f))
  refine IsCellularlyClosed.isStableUnderCobaseChange.{v}.of_isPushout
    (SmallObject.functorObj_isPushout f (terminal.from X)) ?_
  exact MorphismProperty.colimMap _ fun ⟨x⟩ ↦
    le_saturation.{v} _ _ (MorphismProperty.ofHoms.mk x.i)

theorem exists_extension_attachStep (f : ∀ i, U i ⟶ V i) {i : ι} {X : C}
    (t : U i ⟶ X) : ∃ l : V i ⟶ (attachStep f).obj X, f i ≫ l = t ≫ (attachStepUnit f).app X :=
  let ⟨l, hl, _⟩ := SmallObject.ιFunctorObj_extension f t (terminal.from _)
    ⟨terminal.hom_ext _ _⟩
  ⟨l, hl⟩

end Saturation

section Mono

variable [HasPushouts C] [HasCoproducts.{v} C] {ι : Type v} {U V : ι → C} (f : ∀ i, U i ⟶ V i)

variable {f} in
abbrev NewCell {X Y : C} (u : X ⟶ Y) : Type v :=
  {d : FunctorObjIndex f (terminal.from Y) // ¬ ∃ t : U d.i ⟶ X, t ≫ u = d.t}

open Classical in
noncomputable def newCellDesc {X Y W : C} (u : X ⟶ Y)
    (a : functorObj f (terminal.from X) ⟶ W) (b : ∐ (fun d : NewCell (f := f) u => V d.1.i) ⟶ W)
    (d : FunctorObjIndex f (terminal.from Y)) : V d.i ⟶ W :=
  if h : ∃ t : U d.i ⟶ X, t ≫ u = d.t then
    Sigma.ι (functorObjTgtFamily f (terminal.from X))
      ⟨d.i, h.choose, d.b, terminal.hom_ext _ _⟩ ≫ ρFunctorObj f (terminal.from X) ≫ a
  else Sigma.ι (fun d : NewCell (f := f) u => V d.1.i) ⟨d, h⟩ ≫ b

variable {X Y : C} (u : X ⟶ Y)

noncomputable abbrev terminalArrowHom : Arrow.mk (terminal.from X) ⟶ Arrow.mk (terminal.from Y) :=
  Arrow.homMk u (𝟙 _) (terminal.hom_ext _ _)

theorem ιFunctorObj_functorMap_terminalArrowHom :
    ιFunctorObj f (terminal.from X) ≫ functorMap f (terminalArrowHom u) =
      u ≫ ιFunctorObj f (terminal.from Y) :=
  ιFunctorObj_naturality f (terminalArrowHom u)

noncomputable def oldCellsToAttachStep :
    pushout (ιFunctorObj f (terminal.from X)) u ⟶ functorObj f (terminal.from Y) :=
  pushout.desc (functorMap f (terminalArrowHom u)) (ιFunctorObj f (terminal.from Y))
    (ιFunctorObj_functorMap_terminalArrowHom f u)

theorem newCellDesc_of_eq [Mono u] {W : C} (a : functorObj f (terminal.from X) ⟶ W)
    (b : ∐ (fun d : NewCell (f := f) u => V d.1.i) ⟶ W)
    (c : FunctorObjIndex f (terminal.from X)) :
    newCellDesc f u a b ⟨c.i, c.t ≫ u, c.b, terminal.hom_ext _ _⟩ =
      Sigma.ι (functorObjTgtFamily f (terminal.from X)) c ≫
        ρFunctorObj f (terminal.from X) ≫ a := by
  have h : ∃ t : U c.i ⟶ X, t ≫ u = c.t ≫ u := ⟨c.t, rfl⟩
  rw [newCellDesc, dif_pos h]
  rw [sigmaι_functorObjTgtFamily_mk_eq f ((cancel_mono u).1 h.choose_spec) c.b]

theorem newCellDesc_of_not {W : C} (a : functorObj f (terminal.from X) ⟶ W)
    (b : ∐ (fun d : NewCell (f := f) u => V d.1.i) ⟶ W) (d : NewCell (f := f) u) :
    newCellDesc f u a b d.1 = Sigma.ι (fun d : NewCell (f := f) u => V d.1.i) d ≫ b := by
  rw [newCellDesc, dif_neg d.2]

theorem newCellDesc_cond [Mono u] {W : C} (a : functorObj f (terminal.from X) ⟶ W) (p : Y ⟶ W)
    (b : ∐ (fun d : NewCell (f := f) u => V d.1.i) ⟶ W)
    (ha : ιFunctorObj f (terminal.from X) ≫ a = u ≫ p)
    (hb : ∀ d : NewCell (f := f) u,
      d.1.t ≫ p = f d.1.i ≫ Sigma.ι (fun d : NewCell (f := f) u => V d.1.i) d ≫ b) :
    functorObjTop f (terminal.from Y) ≫ p =
      functorObjLeft f (terminal.from Y) ≫ Sigma.desc (newCellDesc f u a b) := by
  refine Sigma.hom_ext _ _ fun d => ?_
  rw [Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Sigma.ι_desc]
  by_cases h : ∃ t : U d.i ⟶ X, t ≫ u = d.t
  · obtain ⟨i, dt, db, dw⟩ := d
    obtain ⟨t, ht⟩ : ∃ t : U i ⟶ X, t ≫ u = dt := h
    subst ht
    rw [newCellDesc_of_eq f u a b ⟨i, t, db, terminal.hom_ext _ _⟩]
    exact ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) ha.symm)).trans
      (FunctorObjIndex.comm_assoc f _ ⟨i, t, db, terminal.hom_ext _ _⟩ a).symm
  · exact (hb ⟨d, h⟩).trans (by rw [newCellDesc_of_not f u a b ⟨d, h⟩])

theorem isPushout_oldCellsToAttachStep [Mono u] :
    IsPushout (Sigma.desc fun d : NewCell (f := f) u =>
        d.1.t ≫ pushout.inr (ιFunctorObj f (terminal.from X)) u)
      (Limits.Sigma.map fun d : NewCell (f := f) u => f d.1.i) (oldCellsToAttachStep f u)
      (Sigma.desc fun d : NewCell (f := f) u =>
        Sigma.ι (functorObjTgtFamily f (terminal.from Y)) d.1 ≫
          ρFunctorObj f (terminal.from Y)) := by
  refine IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s => pushout.desc (pushout.inr (ιFunctorObj f (terminal.from X)) u ≫ s.inl)
      (Sigma.desc (newCellDesc f u (pushout.inl _ _ ≫ s.inl) s.inr))
      (newCellDesc_cond f u _ _ _ (pushout.condition_assoc s.inl) fun d => by
        have := Sigma.ι _ d ≫= s.condition
        rwa [Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Category.assoc] at this)) ?_ ?_ ?_)
  · refine Sigma.hom_ext _ _ fun d => ?_
    rw [Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Sigma.ι_desc, Category.assoc,
      oldCellsToAttachStep, pushout.inr_desc, FunctorObjIndex.comm]
  · intro s
    refine pushout.hom_ext ?_ ?_
    · rw [oldCellsToAttachStep, pushout.inl_desc_assoc]
      refine pushout.hom_ext ?_ (Sigma.hom_ext _ _ fun c => ?_)
      · rw [← Category.assoc, ιFunctorObj_functorMap_terminalArrowHom, Category.assoc,
          pushout.inl_desc]
        exact (pushout.condition_assoc s.inl).symm
      · have e := sigmaι_ρFunctorObj_functorMap f (terminalArrowHom u) c
        rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (functorMap _ _), e,
          Category.assoc, pushout.inr_desc, Sigma.ι_desc]
        exact newCellDesc_of_eq f u _ _ c
    · rw [oldCellsToAttachStep, pushout.inr_desc_assoc, pushout.inl_desc]
  · intro s
    refine Sigma.hom_ext _ _ fun d => ?_
    rw [Sigma.ι_desc_assoc, Category.assoc, pushout.inr_desc, Sigma.ι_desc, newCellDesc_of_not]
  · intro s m hk hh
    refine pushout.hom_ext ?_ (Sigma.hom_ext _ _ fun d => ?_)
    · rw [pushout.inl_desc, ← hk, oldCellsToAttachStep, pushout.inr_desc_assoc]
    · rw [pushout.inr_desc, Sigma.ι_desc]
      by_cases h : ∃ t : U d.i ⟶ X, t ≫ u = d.t
      · obtain ⟨i, dt, db, dw⟩ := d
        obtain ⟨t, ht⟩ : ∃ t : U i ⟶ X, t ≫ u = dt := h
        subst ht
        rw [newCellDesc_of_eq f u _ _ ⟨i, t, db, terminal.hom_ext _ _⟩, ← hk,
          oldCellsToAttachStep, pushout.inl_desc_assoc]
        exact (sigmaι_ρFunctorObj_functorMap_assoc f (terminalArrowHom u)
          ⟨i, t, db, terminal.hom_ext _ _⟩ m).symm
      · rw [newCellDesc_of_not f u _ _ ⟨d, h⟩, ← hh, Sigma.ι_desc_assoc]
        exact (Category.assoc _ _ _).symm

theorem mono_attachStepUnit [(monomorphisms C).IsStableUnderCobaseChange]
    [(monomorphisms C).IsStableUnderCoproducts.{v}] (hf : ∀ i, Mono (f i)) (X : C) :
    Mono ((attachStepUnit f).app X) :=
  (monomorphisms C).of_isPushout (functorObj_isPushout f (terminal.from X))
    (MorphismProperty.colimMap _ fun ⟨d⟩ => hf d.i)

theorem mono_attachStep_map [(monomorphisms C).IsStableUnderCobaseChange]
    [(monomorphisms C).IsStableUnderCoproducts.{v}] (hf : ∀ i, Mono (f i)) [Mono u] :
    Mono ((attachStep f).map u) := by
  have h₁ : Mono (pushout.inl (ιFunctorObj f (terminal.from X)) u) :=
    (monomorphisms C).of_isPushout (IsPushout.of_hasPushout _ _)
      (inferInstance : Mono u)
  have h₂ : Mono (oldCellsToAttachStep f u) :=
    (monomorphisms C).of_isPushout (isPushout_oldCellsToAttachStep f u)
      (MorphismProperty.colimMap _ fun ⟨d⟩ => hf d.1.i)
  have e : (attachStep f).map u = pushout.inl _ _ ≫ oldCellsToAttachStep f u :=
    (pushout.inl_desc _ _ _).symm
  rw [e]
  exact @mono_comp _ _ _ _ _ _ h₁ _ h₂

end Mono

section Accessibility

variable [HasPushouts C] [HasCoproducts.{v} C] {ι : Type v} {U V : ι → C}
  (f : ∀ i, U i ⟶ V i)

theorem nonempty_isColimit_mapCocone_attachStep (κ : Cardinal.{v}) [Fact κ.IsRegular]
    (hU : ∀ i, IsCardinalPresentable (U i) κ) {J : Type v} [SmallCategory J]
    [IsCardinalFiltered J κ] {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c) :
    Nonempty (IsColimit ((attachStep f).mapCocone c)) := by
  refine ⟨IsColimit.ofExistsUnique fun s ↦ ?_⟩
  have hlift (d : SmallObject.FunctorObjIndex f (terminal.from c.pt)) :
      ∃ (j : J) (t : U d.i ⟶ K.obj j), t ≫ c.ι.app j = d.t := by
    have := hU d.i
    exact IsCardinalPresentable.exists_hom_of_isColimit κ hc d.t
  choose jd td htd using hlift
  obtain ⟨α, hα⟩ : ∃ α : c.pt ⟶ s.pt,
      ∀ j, c.ι.app j ≫ α = (attachStepUnit f).app (K.obj j) ≫ s.ι.app j :=
    ⟨hc.desc (Cocone.mk s.pt
      { app j := (attachStepUnit f).app (K.obj j) ≫ s.ι.app j
        naturality j k φ := by
          dsimp
          rw [Category.comp_id, ← s.w φ]
          exact (attachStepUnit f).naturality_assoc (K.map φ) (s.ι.app k) }), hc.fac _⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ∐ SmallObject.functorObjTgtFamily f (terminal.from c.pt) ⟶ s.pt,
      ∀ d, Sigma.ι _ d ≫ β =
        Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from (K.obj (jd d))))
          ⟨d.i, td d, d.b, terminal.hom_ext _ _⟩ ≫
            SmallObject.ρFunctorObj f (terminal.from (K.obj (jd d))) ≫ s.ι.app (jd d) :=
    ⟨Sigma.desc _, fun d ↦ Sigma.ι_desc _ d⟩
  have hβ (j : J) (d : SmallObject.FunctorObjIndex f (terminal.from (K.obj j))) :
      Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from c.pt))
          ⟨d.i, d.t ≫ c.ι.app j, d.b, terminal.hom_ext _ _⟩ ≫ β =
        Sigma.ι (SmallObject.functorObjTgtFamily f (terminal.from (K.obj j))) d ≫
          SmallObject.ρFunctorObj f (terminal.from (K.obj j)) ≫ s.ι.app j := by
    obtain ⟨i, t, b, w⟩ := d
    rw [hβdef]
    have := hU i
    obtain ⟨k, u, v, huv⟩ := IsCardinalPresentable.exists_eq_of_isColimit κ hc _ t
      (htd ⟨i, t ≫ c.ι.app j, b, terminal.hom_ext _ _⟩)
    rw [← s.w u, ← s.w v]
    simp only [Functor.comp_map]
    have e₁ := sigmaι_ρFunctorObj_attachStep_map_assoc f (K.map u)
      ⟨i, td ⟨i, t ≫ c.ι.app j, b, terminal.hom_ext _ _⟩, b, terminal.hom_ext _ _⟩ (s.ι.app k)
    have e₂ := sigmaι_ρFunctorObj_attachStep_map_assoc f (K.map v) ⟨i, t, b, w⟩ (s.ι.app k)
    exact e₁.trans
      ((sigmaι_functorObjTgtFamily_mk_eq f huv b (terminal.hom_ext _ _) =≫
        (SmallObject.ρFunctorObj f (terminal.from (K.obj k)) ≫ s.ι.app k)).trans e₂.symm)
  have hcond : SmallObject.functorObjTop f (terminal.from c.pt) ≫ α =
      SmallObject.functorObjLeft f (terminal.from c.pt) ≫ β := by
    refine Sigma.hom_ext _ _ fun d ↦ ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, hβdef]
    rw [← htd d, Category.assoc, hα]
    exact (SmallObject.FunctorObjIndex.comm_assoc f (terminal.from (K.obj (jd d)))
      ⟨d.i, td d, d.b, terminal.hom_ext _ _⟩ (s.ι.app (jd d))).symm
  obtain ⟨φ, hφl, hφr⟩ : ∃ φ : (attachStep f).obj c.pt ⟶ s.pt,
      (attachStepUnit f).app c.pt ≫ φ = α ∧
        SmallObject.ρFunctorObj f (terminal.from c.pt) ≫ φ = β :=
    ⟨pushout.desc α β hcond, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩
  refine ⟨φ, fun j ↦ ?_, fun m hm ↦ ?_⟩
  · refine attachStep_obj_hom_ext f ?_ fun d ↦ ?_
    · exact (((attachStepUnit f).naturality_assoc (c.ι.app j)) φ).symm.trans
        ((c.ι.app j ≫= hφl).trans (hα j))
    · exact (sigmaι_ρFunctorObj_attachStep_map_assoc f (c.ι.app j) d φ).trans
        ((Sigma.ι _ _ ≫= hφr).trans (hβ j d))
  · refine attachStep_obj_hom_ext f ?_ fun d ↦ ?_
    · rw [hφl]
      refine hc.hom_ext fun j ↦ ?_
      exact (((attachStepUnit f).naturality_assoc (c.ι.app j)) m).trans
        ((_ ≫= hm j).trans (hα j).symm)
    · have e := sigmaι_functorObjTgtFamily_mk_eq f (htd d).symm d.b d.w
      have e₁ := sigmaι_ρFunctorObj_attachStep_map_assoc f (c.ι.app (jd d))
        ⟨d.i, td d, d.b, terminal.hom_ext _ _⟩ m
      exact (e =≫ _).trans (e₁.symm.trans ((Sigma.ι _ _ ≫= (_ ≫= hm (jd d))).trans
        ((hβ (jd d) _).symm.trans ((e =≫ β).symm.trans (Sigma.ι _ d ≫= hφr).symm))))

theorem preservesColimitsOfShape_attachStep (κ : Cardinal.{v}) [Fact κ.IsRegular]
    (hU : ∀ i, IsCardinalPresentable (U i) κ) (J : Type v) [SmallCategory J]
    [IsCardinalFiltered J κ] : PreservesColimitsOfShape J (attachStep f) :=
  ⟨⟨fun hc ↦ nonempty_isColimit_mapCocone_attachStep f κ hU hc⟩⟩

end Accessibility

end CategoryTheory.SmallObject
