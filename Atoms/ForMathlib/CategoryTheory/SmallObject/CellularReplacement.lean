import Atoms.ForMathlib.CategoryTheory.SmallObject.AttachStep

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.SmallObject

universe v u

section Reindex

variable {C : Type u} [Category.{v} C] [HasTerminal C] {ι' : Type*} {U' V' : ι' → C}
  (f' : ∀ i, U' i ⟶ V' i) {ι : Type v} (e : ι ≃ ι')

def functorObjIndexReindex (X : C)
    (d : SmallObject.FunctorObjIndex (fun i ↦ f' (e i)) (terminal.from X)) :
    SmallObject.FunctorObjIndex f' (terminal.from X) :=
  ⟨e d.i, d.t, d.b, d.w⟩

theorem functorObjIndexReindex_bijective (X : C) :
    Function.Bijective (functorObjIndexReindex f' e X) := by
  constructor
  · rintro ⟨i, t, b, w⟩ ⟨i', t', b', w'⟩ h
    obtain ⟨h₁, h₂, h₃⟩ := SmallObject.FunctorObjIndex.mk.inj h
    obtain rfl := e.injective h₁
    obtain rfl := eq_of_heq h₂
    obtain rfl := eq_of_heq h₃
    rfl
  · rintro ⟨i', t, b, w⟩
    obtain ⟨i, rfl⟩ := e.surjective i'
    exact ⟨⟨i, t, b, w⟩, rfl⟩

noncomputable def functorObjIndexReindexEquiv (X : C) :
    SmallObject.FunctorObjIndex (fun i ↦ f' (e i)) (terminal.from X) ≃
      SmallObject.FunctorObjIndex f' (terminal.from X) :=
  Equiv.ofBijective _ (functorObjIndexReindex_bijective f' e X)

variable [HasPushouts C] [HasCoproducts.{v} C] [∀ {X S : C} (π : X ⟶ S),
    HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex f' π)) C]

noncomputable def functorObjSrcReindex (X : C) :
    ∐ SmallObject.functorObjSrcFamily (fun i ↦ f' (e i)) (terminal.from X) ⟶
      ∐ SmallObject.functorObjSrcFamily f' (terminal.from X) :=
  (Sigma.reindex (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjSrcFamily f' (terminal.from X))).hom

noncomputable def functorObjTgtReindex (X : C) :
    ∐ SmallObject.functorObjTgtFamily (fun i ↦ f' (e i)) (terminal.from X) ⟶
      ∐ SmallObject.functorObjTgtFamily f' (terminal.from X) :=
  (Sigma.reindex (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjTgtFamily f' (terminal.from X))).hom

instance (X : C) : IsIso (functorObjSrcReindex f' e X) :=
  Iso.isIso_hom (Sigma.reindex (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjSrcFamily f' (terminal.from X)))

instance (X : C) : IsIso (functorObjTgtReindex f' e X) :=
  Iso.isIso_hom (Sigma.reindex (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjTgtFamily f' (terminal.from X)))

omit [HasPushouts C] in
@[reassoc]
theorem sigmaι_functorObjSrcReindex (X : C)
    (d : SmallObject.FunctorObjIndex (fun i ↦ f' (e i)) (terminal.from X)) :
    Sigma.ι (SmallObject.functorObjSrcFamily (fun i ↦ f' (e i)) (terminal.from X)) d ≫
        functorObjSrcReindex f' e X =
      Sigma.ι (SmallObject.functorObjSrcFamily f' (terminal.from X))
        (functorObjIndexReindex f' e X d) :=
  Sigma.ι_reindex_hom (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjSrcFamily f' (terminal.from X)) d

omit [HasPushouts C] in
@[reassoc]
theorem sigmaι_functorObjTgtReindex (X : C)
    (d : SmallObject.FunctorObjIndex (fun i ↦ f' (e i)) (terminal.from X)) :
    Sigma.ι (SmallObject.functorObjTgtFamily (fun i ↦ f' (e i)) (terminal.from X)) d ≫
        functorObjTgtReindex f' e X =
      Sigma.ι (SmallObject.functorObjTgtFamily f' (terminal.from X))
        (functorObjIndexReindex f' e X d) :=
  Sigma.ι_reindex_hom (functorObjIndexReindexEquiv f' e X)
    (SmallObject.functorObjTgtFamily f' (terminal.from X)) d

noncomputable def attachStepReindexApp (X : C) :
    SmallObject.functorObj (fun i ↦ f' (e i)) (terminal.from X) ⟶
      SmallObject.functorObj f' (terminal.from X) :=
  pushout.map (SmallObject.functorObjTop (fun i ↦ f' (e i)) (terminal.from X))
    (SmallObject.functorObjLeft (fun i ↦ f' (e i)) (terminal.from X))
    (SmallObject.functorObjTop f' (terminal.from X))
    (SmallObject.functorObjLeft f' (terminal.from X)) (𝟙 X)
    (functorObjTgtReindex f' e X) (functorObjSrcReindex f' e X)
    (Sigma.hom_ext _ _ fun d ↦ by
      rw [Category.comp_id, sigmaι_functorObjSrcReindex_assoc]
      exact (Sigma.ι_desc _ d).trans
        (Sigma.ι_desc (fun x : SmallObject.FunctorObjIndex f' (terminal.from X) ↦ x.t)
          (functorObjIndexReindex f' e X d)).symm)
    (Sigma.hom_ext _ _ fun d ↦ by
      have h₁ : Sigma.ι (SmallObject.functorObjSrcFamily (fun i ↦ f' (e i)) (terminal.from X)) d ≫
          SmallObject.functorObjLeft (fun i ↦ f' (e i)) (terminal.from X) =
            f' (e d.i) ≫
              Sigma.ι (SmallObject.functorObjTgtFamily (fun i ↦ f' (e i)) (terminal.from X)) d :=
        Sigma.ι_map _ d
      have h₂ : Sigma.ι (SmallObject.functorObjSrcFamily f' (terminal.from X))
          (functorObjIndexReindex f' e X d) ≫ SmallObject.functorObjLeft f' (terminal.from X) =
            f' (e d.i) ≫ Sigma.ι (SmallObject.functorObjTgtFamily f' (terminal.from X))
              (functorObjIndexReindex f' e X d) :=
        Sigma.ι_map _ _
      rw [reassoc_of% h₁, sigmaι_functorObjTgtReindex, sigmaι_functorObjSrcReindex_assoc]
      exact h₂.symm)

theorem isIso_attachStepReindexApp (X : C) : IsIso (attachStepReindexApp f' e X) := by
  unfold attachStepReindexApp
  infer_instance

theorem ιFunctorObj_attachStepReindexApp (X : C) :
    SmallObject.ιFunctorObj (fun i ↦ f' (e i)) (terminal.from X) ≫ attachStepReindexApp f' e X =
      SmallObject.ιFunctorObj f' (terminal.from X) := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc, Category.id_comp]

theorem sigmaι_ρFunctorObj_attachStepReindexApp (X : C)
    (d : SmallObject.FunctorObjIndex (fun i ↦ f' (e i)) (terminal.from X)) :
    Sigma.ι (SmallObject.functorObjTgtFamily (fun i ↦ f' (e i)) (terminal.from X)) d ≫
        SmallObject.ρFunctorObj (fun i ↦ f' (e i)) (terminal.from X) ≫
          attachStepReindexApp f' e X =
      Sigma.ι (SmallObject.functorObjTgtFamily f' (terminal.from X))
          (functorObjIndexReindex f' e X d) ≫
        SmallObject.ρFunctorObj f' (terminal.from X) := by
  change _ ≫ pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]
  exact sigmaι_functorObjTgtReindex_assoc f' e X d _

noncomputable def attachStepReindexAppIso (X : C) :
    SmallObject.functorObj (fun i ↦ f' (e i)) (terminal.from X) ≅
      SmallObject.functorObj f' (terminal.from X) :=
  haveI := isIso_attachStepReindexApp f' e X
  asIso (attachStepReindexApp f' e X)

noncomputable def attachStepReindexIso : attachStep (fun i ↦ f' (e i)) ≅ attachStep f' :=
  NatIso.ofComponents
    (fun X ↦ attachStepReindexAppIso f' e X)
    (fun {X Y} u ↦ by
    refine attachStep_obj_hom_ext (fun i ↦ f' (e i)) ?_ fun d ↦ ?_
    · have e₂ := reassoc_of% ιFunctorObj_attachStepReindexApp f' e X
      exact ((attachStepUnit (fun i ↦ f' (e i))).naturality_assoc u _).symm.trans
        ((u ≫= ιFunctorObj_attachStepReindexApp f' e Y).trans
        ((SmallObject.ιFunctorObj_naturality f' (arrowToTerminal.map u)).symm.trans (e₂ _).symm))
    · have e₁ := sigmaι_ρFunctorObj_attachStep_map_assoc (fun i ↦ f' (e i)) u d
        (attachStepReindexApp f' e Y)
      have e₂ := (congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((sigmaι_ρFunctorObj_attachStepReindexApp f' e X d =≫ (attachStep f').map u).trans
            (Category.assoc _ _ _)))
      exact e₁.trans ((sigmaι_ρFunctorObj_attachStepReindexApp f' e Y
        ⟨d.i, d.t ≫ u, d.b, terminal.hom_ext _ _⟩).trans
        ((sigmaι_ρFunctorObj_functorMap f' (arrowToTerminal.map u)
          (functorObjIndexReindex f' e X d)).symm.trans
          e₂.symm)))

end Reindex

variable {C : Type u} [Category.{v} C] [HasTerminal C] (I : MorphismProperty C)
  (κ : Cardinal.{v}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

noncomputable def cellularReplacement : C ⥤ C :=
  arrowToTerminal ⋙ SmallObject.iteration I κ ⋙ Arrow.leftFunc

noncomputable def cellularReplacementUnit : 𝟭 C ⟶ cellularReplacement I κ :=
  Functor.whiskerLeft arrowToTerminal
    (Functor.whiskerRight (SmallObject.ιIteration I κ) Arrow.leftFunc)

theorem llp_rlp_cellularReplacementUnit (X : C) :
    I.rlp.llp ((cellularReplacementUnit I κ).app X) :=
  SmallObject.llp_rlp_ιObj I κ (terminal.from X)

theorem rlp_terminal_from_cellularReplacement (X : C) :
    I.rlp (terminal.from ((cellularReplacement I κ).obj X)) := by
  have h : terminal.from ((cellularReplacement I κ).obj X) =
      SmallObject.πObj I κ (terminal.from X) :=
    terminal.hom_ext _ _
  rw [h]
  exact SmallObject.rlp_πObj I κ _

section Stages

noncomputable def arrowWhiskering :
    (Arrow C ⥤ Arrow C) ⥤ C ⥤ C :=
  (Functor.whiskeringLeft _ _ _).obj arrowToTerminal ⋙
    (Functor.whiskeringRight _ _ _).obj Arrow.leftFunc

instance preservesColimitsOfShape_arrowWhiskering (J : Type v) [SmallCategory J]
    [HasColimitsOfShape J C] : PreservesColimitsOfShape J (arrowWhiskering (C := C)) :=
  inferInstanceAs (PreservesColimitsOfShape J
    ((Functor.whiskeringLeft _ _ _).obj arrowToTerminal ⋙
      (Functor.whiskeringRight _ _ _).obj Arrow.leftFunc))

noncomputable def cellularStage : κ.ord.ToType ⥤ C ⥤ C :=
  SmallObject.iterationFunctor I κ ⋙ arrowWhiskering

noncomputable def cellularStageCocone : Cocone (cellularStage I κ) :=
  haveI := SmallObject.hasIterationOfShape I κ
  arrowWhiskering.mapCocone ((SmallObject.succStruct I κ).iterationCocone κ.ord.ToType)

noncomputable def isColimitCellularStageCocone : IsColimit (cellularStageCocone I κ) :=
  haveI := SmallObject.hasIterationOfShape I κ
  isColimitOfPreserves arrowWhiskering
    ((SmallObject.succStruct I κ).isColimitIterationCocone κ.ord.ToType)

noncomputable def isColimitCellularStageIio (m : κ.ord.ToType) (hm : Order.IsSuccLimit m) :
    IsColimit (arrowWhiskering.mapCocone
      ((Set.principalSegIio m).cocone (SmallObject.iterationFunctor I κ))) :=
  haveI := SmallObject.hasIterationOfShape I κ
  haveI := HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit (C := C) m hm
  isColimitOfPreserves arrowWhiskering
    (Functor.isColimitOfIsWellOrderContinuous
      ((SmallObject.succStruct I κ).iterationFunctor κ.ord.ToType) m hm)

noncomputable def cellularStageObjBotIso : (cellularStage I κ).obj ⊥ ≅ 𝟭 C :=
  haveI := SmallObject.hasIterationOfShape I κ
  arrowWhiskering.mapIso
      ((SmallObject.succStruct I κ).iterationFunctorObjBotIso κ.ord.ToType) ≪≫
    NatIso.ofComponents (fun X ↦ Iso.refl X)
      (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

noncomputable def cellularStageArrowIso (j : κ.ord.ToType) :
    arrowToTerminal ⋙ (SmallObject.iterationFunctor I κ).obj j ≅
      (cellularStage I κ).obj j ⋙ arrowToTerminal :=
  NatIso.ofComponents
    (fun X ↦ Arrow.isoMk (Iso.refl _)
      (SmallObject.iterationFunctorObjObjRightIso I κ (Arrow.mk (terminal.from X)) j)
      (terminal.hom_ext _ _))
    (fun _ ↦ Arrow.hom_ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm)
      (terminal.hom_ext _ _))

def cellIndex : Type v :=
  haveI := SmallObject.isSmall I κ
  Shrink.{v} I.toSet

noncomputable def cellIndexEquiv : cellIndex I κ ≃ I.toSet :=
  haveI := SmallObject.isSmall I κ
  (equivShrink I.toSet).symm

noncomputable def cellularStageObjSuccIso [HasPushouts C] [HasCoproducts.{v} C]
    (j : κ.ord.ToType) :
    (cellularStage I κ).obj (Order.succ j) ≅
      (cellularStage I κ).obj j ⋙ attachStep (fun i ↦ I.homFamily (cellIndexEquiv I κ i)) :=
  haveI := SmallObject.hasIterationOfShape I κ
  haveI := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  haveI := SmallObject.hasColimitsOfShape_discrete I κ
  arrowWhiskering.mapIso
      ((SmallObject.succStruct I κ).iterationFunctorObjSuccIso j (not_isMax j)) ≪≫
    Functor.isoWhiskerRight (cellularStageArrowIso I κ j)
      (SmallObject.functor I.homFamily ⋙ Arrow.leftFunc) ≪≫
    Functor.isoWhiskerLeft ((cellularStage I κ).obj j)
      (attachStepReindexIso I.homFamily (cellIndexEquiv I κ)).symm

end Stages

section Induction

theorem cellularStage_obj_induction [HasPushouts C] [HasCoproducts.{v} C] (P : (C ⥤ C) → Prop)
    (hiso : ∀ {F G : C ⥤ C}, (F ≅ G) → P F → P G)
    (hid : P (𝟭 _))
    (hsucc : ∀ F, P F → P (F ⋙ attachStep (fun i ↦ I.homFamily (cellIndexEquiv I κ i))))
    (hcolim : ∀ {D : Type v} [SmallCategory D] [IsFiltered D]
      {K : D ⥤ C ⥤ C} {c : Cocone K},
        IsColimit c → (∀ d, P (K.obj d)) → P c.pt)
    (j : κ.ord.ToType) : P ((cellularStage I κ).obj j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact hiso (cellularStageObjBotIso I κ).symm hid
  | succ j _ ih => exact hiso (cellularStageObjSuccIso I κ j).symm (hsucc _ ih)
  | isSuccLimit m hm ih =>
    obtain ⟨k, hk⟩ := not_isMin_iff.1 hm.not_isMin
    have : Nonempty (Set.Iio m) := ⟨⟨k, hk⟩⟩
    exact hcolim (isColimitCellularStageIio I κ m hm) fun d ↦ ih d.1 d.2

theorem cellularReplacement_induction [HasPushouts C] [HasCoproducts.{v} C] (P : (C ⥤ C) → Prop)
    (hiso : ∀ {F G : C ⥤ C}, (F ≅ G) → P F → P G)
    (hid : P (𝟭 _))
    (hsucc : ∀ F, P F → P (F ⋙ attachStep (fun i ↦ I.homFamily (cellIndexEquiv I κ i))))
    (hcolim : ∀ {D : Type v} [SmallCategory D] [IsFiltered D]
      {K : D ⥤ C ⥤ C} {c : Cocone K},
        IsColimit c → (∀ d, P (K.obj d)) → P c.pt) :
    P (cellularReplacement I κ) :=
  hcolim (isColimitCellularStageCocone I κ)
    (cellularStage_obj_induction I κ P hiso hid hsucc hcolim)

end Induction

section Monomorphisms

omit [HasTerminal C] in
theorem mono_map_of_isColimit [HasColimitsOfSize.{v, v} C]
    [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}] {D : Type v} [SmallCategory D]
    [IsFiltered D] {K : D ⥤ C ⥤ C} {c : Cocone K} (hc : IsColimit c) {X Y : C} (u : X ⟶ Y)
    (h : ∀ d, Mono ((K.obj d).map u)) : Mono (c.pt.map u) :=
  MorphismProperty.colimitsOfShape_le (W := monomorphisms C) (J := D) _
    (MorphismProperty.colimitsOfShape.mk' (K ⋙ (evaluation C C).obj X)
      (K ⋙ (evaluation C C).obj Y) _ _ (isColimitOfPreserves ((evaluation C C).obj X) hc)
      (isColimitOfPreserves ((evaluation C C).obj Y) hc)
      { app d := (K.obj d).map u
        naturality _ _ φ := ((K.map φ).naturality u).symm }
      (fun d => h d) _ fun d => ((c.ι.app d).naturality u).symm)

theorem mono_cellularReplacement_map [HasPushouts C] [HasCoproducts.{v} C]
    [HasColimitsOfSize.{v, v} C]
    [(monomorphisms C).IsStableUnderCobaseChange] [(monomorphisms C).IsStableUnderCoproducts.{v}]
    [(monomorphisms C).IsStableUnderFilteredColimits.{v, v}]
    (hI : I ≤ MorphismProperty.monomorphisms C)
    {X Y : C} (u : X ⟶ Y) [Mono u] : Mono ((cellularReplacement I κ).map u) := by
  have hg (i : cellIndex I κ) : Mono (I.homFamily (cellIndexEquiv I κ i)) :=
    hI _ (cellIndexEquiv I κ i).2
  refine cellularReplacement_induction I κ
    (fun F ↦ ∀ ⦃X Y : C⦄ (u : X ⟶ Y), Mono u → Mono (F.map u))
    ?_ ?_ ?_ ?_ u inferInstance
  · intro F G e hmono X Y u hu
    have := hmono u hu
    have h : G.map u = e.inv.app X ≫ F.map u ≫ e.hom.app Y := by simp
    rw [h]
    infer_instance
  · exact fun _ _ _ hu ↦ hu
  · intro F hmono X Y u hu
    have := hmono u hu
    exact mono_attachStep_map _ (F.map u) hg
  · intro D _ _ K c hc h X Y u hu
    exact mono_map_of_isColimit hc u fun d ↦ h d u hu

end Monomorphisms

section Accessibility

omit [HasTerminal C] in
theorem preservesColimitsOfShape_of_isColimit [HasColimitsOfSize.{v, v} C]
    {D : Type v} [SmallCategory D]
    {K : D ⥤ C ⥤ C} {c : Cocone K} (hc : IsColimit c)
    (J : Type v) [SmallCategory J] (h : ∀ d, PreservesColimitsOfShape J (K.obj d)) :
    PreservesColimitsOfShape J c.pt := by
  have : PreservesColimitsOfShape J K.flip :=
    preservesColimitsOfShape_of_evaluation _ _ fun d ↦
      preservesColimitsOfShape_of_natIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _)
          fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm :
          K.obj d ≅ K.flip ⋙ (evaluation _ _).obj d)
  exact preservesColimitsOfShape_of_natIso
    ((hc.coconePointUniqueUpToIso (colimit.isColimit K)) ≪≫ colimitIsoFlipCompColim K).symm

theorem isCardinalAccessible_cellularReplacement [HasPushouts C] [HasCoproducts.{v} C]
    [HasColimitsOfSize.{v, v} C]
    (κ' : Cardinal.{v}) [Fact κ'.IsRegular]
    (hU : ∀ ⦃X Y : C⦄ (i : X ⟶ Y), I i → IsCardinalPresentable X κ') :
    (cellularReplacement I κ).IsCardinalAccessible κ' := by
  have hg (i : cellIndex I κ) : IsCardinalPresentable (cellIndexEquiv I κ i).1.left κ' :=
    hU _ (cellIndexEquiv I κ i).2
  refine ⟨fun J _ _ ↦ ?_⟩
  refine cellularReplacement_induction I κ (fun F ↦ PreservesColimitsOfShape J F) ?_ ?_ ?_ ?_
  · intro F G e hF
    exact preservesColimitsOfShape_of_natIso e
  · infer_instance
  · intro F hF
    have := preservesColimitsOfShape_attachStep (fun i ↦ I.homFamily (cellIndexEquiv I κ i)) κ' hg J
    infer_instance
  · intro D _ _ K c hc h
    exact preservesColimitsOfShape_of_isColimit hc J h

end Accessibility

end CategoryTheory.SmallObject
