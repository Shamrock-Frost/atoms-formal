import Atoms.Homotopical.Localizer.LeftProper
import Atoms.Homotopical.Simplicial.RightAnodyne

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace SSet

private noncomputable abbrev coneFunctor : SSet.{u} ⥤ SSet.{u} :=
  joinRightUnder Δ[0] ⋙ Under.forget _

noncomputable def coneEdge (Z : Under (Δ[0] : SSet.{u})) : Δ[1] ⟶ join Z.right Δ[0] :=
  (stdSimplexJoinIso 0 0).inv ≫ joinMap Z.hom (𝟙 Δ[0])

abbrev isoEdge : Δ[1] ⟶ coherentIso.{u} :=
  yonedaEquiv.symm coherentIso.hom.edge

private noncomputable abbrev terminalizationPoint : SSet.{u} :=
  pushout (coneEdge (Under.mk (𝟙 (Δ[0] : SSet.{u})))) isoEdge

private noncomputable def pointInl : join Δ[0] Δ[0] ⟶ terminalizationPoint.{u} :=
  pushout.inl (coneEdge (Under.mk (𝟙 (Δ[0] : SSet.{u})))) isoEdge

private noncomputable abbrev terminalizationRight : Under (Δ[0] : SSet.{u}) ⥤ SSet.{u} where
  obj Z := pushout (joinMap Z.hom (𝟙 Δ[0])) pointInl.{u}
  map {Z Z'} f := pushout.desc (joinMap f.right (𝟙 Δ[0]) ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc, joinMap_comp_joinMap_id, Under.w f, pushout.condition])
  map_id Z := pushout.hom_ext (by
    rw [pushout.inl_desc, Under.id_right, Category.comp_id]
    exact (congrArg (· ≫ _) (coneFunctor.map_id Z.right)).trans (Category.id_comp _))
    (by rw [pushout.inr_desc, Category.comp_id])
  map_comp f g := pushout.hom_ext (by
    rw [pushout.inl_desc, pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc,
      Under.comp_right, ← joinMap_comp_joinMap_id, Category.assoc])
    (by rw [pushout.inr_desc, pushout.inr_desc_assoc, pushout.inr_desc])

private theorem terminalizationRight_eq :
    terminalizationRight.{u} =
      Under.post coneFunctor ⋙ Under.pushout pointInl.{u} ⋙ Under.forget _ :=
  rfl

noncomputable def terminalization : Under (Δ[0] : SSet.{u}) ⥤ Under (Δ[0] : SSet.{u}) :=
  terminalizationRight.{u}.toUnder Δ[0]
    (fun Z ↦ Z.hom ≫ joinInclLeft Z.right Δ[0] ≫ pushout.inl _ _)
    fun {Z Z'} f ↦ by
      have e : (joinInclLeft Z.right Δ[0] ≫ pushout.inl _ _) ≫ terminalizationRight.{u}.map f =
          f.right ≫ joinInclLeft Z'.right Δ[0] ≫ pushout.inl _ _ := by
        rw [Category.assoc]
        exact (congrArg (_ ≫ ·) (pushout.inl_desc _ _ _)).trans
          (joinInclLeft_comp_joinMap_assoc _ _ _)
      exact (congrArg (Z.hom ≫ ·) e).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Under.w f)))

noncomputable def terminalizationInl (Z : Under (Δ[0] : SSet.{u})) :
    join Z.right Δ[0] ⟶ (terminalization.obj Z).right :=
  pushout.inl _ _

noncomputable def terminalizationInr (Z : Under (Δ[0] : SSet.{u})) :
    coherentIso.{u} ⟶ (terminalization.obj Z).right :=
  pushout.inr _ _ ≫ pushout.inr _ _

private theorem coneEdge_eq (Z : Under (Δ[0] : SSet.{u})) :
    coneEdge Z = coneEdge (Under.mk (𝟙 (Δ[0] : SSet.{u}))) ≫ joinMap Z.hom (𝟙 Δ[0]) := by
  refine (congrArg ((stdSimplexJoinIso 0 0).inv ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  exact (congrArg (fun g ↦ joinMap g (𝟙 Δ[0])) (Category.id_comp Z.hom)).symm.trans
    (joinMap_comp_joinMap_id (𝟙 Δ[0]) Z.hom _).symm

theorem isPushout_terminalization (Z : Under (Δ[0] : SSet.{u})) :
    IsPushout (coneEdge Z) (yonedaEquiv.symm coherentIso.hom.edge)
      (terminalizationInl Z) (terminalizationInr Z) := by
  rw [coneEdge_eq]
  exact (IsPushout.of_hasPushout (coneEdge (Under.mk (𝟙 (Δ[0] : SSet.{u})))) isoEdge).paste_horiz
    (IsPushout.of_hasPushout (joinMap Z.hom (𝟙 Δ[0])) pointInl.{u})

@[reassoc]
theorem joinMap_comp_terminalizationInl {Z Z' : Under (Δ[0] : SSet.{u})} (f : Z ⟶ Z') :
    joinMap f.right (𝟙 Δ[0]) ≫ terminalizationInl Z' =
      terminalizationInl Z ≫ (terminalization.map f).right :=
  (pushout.inl_desc _ _ _).symm

@[reassoc (attr := simp)]
theorem terminalizationInr_comp_map {Z Z' : Under (Δ[0] : SSet.{u})} (f : Z ⟶ Z') :
    terminalizationInr Z ≫ (terminalization.map f).right = terminalizationInr Z' :=
  (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (pushout.inr_desc _ _ _))

noncomputable def terminalizationUnit : 𝟭 _ ⟶ terminalization where
  app Z := Under.homMk (joinInclLeft Z.right Δ[0] ≫ terminalizationInl Z) rfl
  naturality {Z Z'} f := by
    refine Under.UnderMorphism.ext ?_
    exact (joinInclLeft_comp_joinMap_assoc _ _ _).symm.trans
      (congrArg (_ ≫ ·) (joinMap_comp_terminalizationInl f))

theorem terminalizationUnit_app_right (Z : Under (Δ[0] : SSet.{u})) :
    (terminalizationUnit.app Z).right = joinInclLeft Z.right Δ[0] ≫ terminalizationInl Z :=
  rfl

private instance preservesColimitsOfShape_terminalizationRight :
    PreservesColimitsOfShape WalkingSpan terminalizationRight.{u} := by
  have h₁ : PreservesColimitsOfShape WalkingSpan (Under.post (X := Δ[0]) coneFunctor) :=
    have : PreservesColimitsOfShape WalkingSpan
        (Under.post (X := Δ[0]) coneFunctor ⋙ Under.forget _) :=
      inferInstanceAs (PreservesColimitsOfShape WalkingSpan (Under.forget _ ⋙ coneFunctor))
    preservesColimitsOfShape_of_reflects_of_preserves _ (Under.forget _)
  have h₂ : PreservesColimitsOfShape WalkingSpan (Under.pushout pointInl.{u}) :=
    have := (Under.mapPushoutAdj pointInl.{u}).leftAdjoint_preservesColimits.{0, 0}
    inferInstance
  rw [terminalizationRight_eq]
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ (Under.post coneFunctor)
    (Under.pushout pointInl.{u} ⋙ Under.forget _) h₁
    (@comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h₂ inferInstance)

instance preservesColimitsOfShape_terminalization :
    PreservesColimitsOfShape WalkingSpan terminalization.{u} :=
  have : PreservesColimitsOfShape WalkingSpan (terminalization ⋙ Under.forget _) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingSpan terminalizationRight.{u})
  preservesColimitsOfShape_of_reflects_of_preserves _ (Under.forget _)

private theorem mono_hom (Z : Under (Δ[0] : SSet.{u})) : Mono Z.hom :=
  stdSimplex.isTerminalObj₀.mono_from _

private theorem mono_coneEdge (Z : Under (Δ[0] : SSet.{u})) : Mono (coneEdge Z) :=
  have := mono_hom Z
  inferInstanceAs (Mono ((stdSimplexJoinIso 0 0).inv ≫ joinMap Z.hom (𝟙 Δ[0])))

@[reassoc]
private theorem coneEdge_comp_joinMap {Z Z' : Under (Δ[0] : SSet.{u})} (f : Z ⟶ Z') :
    coneEdge Z ≫ joinMap f.right (𝟙 Δ[0]) = coneEdge Z' :=
  (Category.assoc _ _ _).trans (congrArg ((stdSimplexJoinIso 0 0).inv ≫ ·)
    ((joinMap_comp_joinMap_id _ _ _).trans (congrArg (fun g ↦ joinMap g (𝟙 Δ[0])) (Under.w f))))

theorem isPushout_terminalization_map {Z Z' : Under (Δ[0] : SSet.{u})} (f : Z ⟶ Z') :
    IsPushout (joinMap f.right (𝟙 Δ[0])) (terminalizationInl Z) (terminalizationInl Z')
      (terminalization.map f).right := by
  refine IsPushout.of_left ?_ (joinMap_comp_terminalizationInl f) (isPushout_terminalization Z)
  rw [coneEdge_comp_joinMap, terminalizationInr_comp_map]
  exact isPushout_terminalization Z'

theorem mono_terminalization_map_right {Z Z' : Under (Δ[0] : SSet.{u})} (f : Z ⟶ Z')
    [Mono f.right] : Mono (terminalization.map f).right :=
  Adhesive.mono_of_isPushout_of_mono_left (isPushout_terminalization_map f)

section Joyal

open modelCategoryJoyal

private theorem isALocalizer_joyal :
    Atoms.Homotopical.IsALocalizer
      (Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions) :=
  Atoms.Homotopical.joyalInterval.{u}.cylinder.isALocalizer_weakEquivalences _
    innerHornInclusions_le_monomorphisms

theorem weakEquivalence_terminalization_map_right {Z Z' : Under (Δ[0] : SSet.{u})}
    (f : Z ⟶ Z') [WeakEquivalence f.right] :
    WeakEquivalence (terminalization.map f).right := by
  have := isALocalizer_joyal
  have := mono_coneEdge Z
  have := mono_coneEdge Z'
  have h₀ : Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions
      (𝟙 (Δ[1] : SSet.{u})) := (weakEquivalence_iff (𝟙 (Δ[1] : SSet.{u}))).1 inferInstance
  have h₁ : Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions
      (joinMap f.right (𝟙 Δ[0])) := (weakEquivalence_iff _).1 (weakEquivalence_joinMap_id _ _)
  have h₂ : Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions
      (𝟙 coherentIso.{u}) := (weakEquivalence_iff (𝟙 coherentIso.{u})).1 inferInstance
  rw [weakEquivalence_iff]
  exact Atoms.Homotopical.IsALocalizer.of_isPushout_of_mono
    (V := Atoms.Homotopical.joyalInterval.{u}.cylinder.weakEquivalences innerHornInclusions)
    (isPushout_terminalization Z)
    (isPushout_terminalization Z') (𝟙 _) (joinMap f.right (𝟙 Δ[0])) (𝟙 _) _
    ((coneEdge_comp_joinMap f).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (joinMap_comp_terminalizationInl f).symm
    ((terminalizationInr_comp_map f).trans (Category.id_comp _).symm) h₀ h₁ h₂

end Joyal

private def vertexZero : (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  stdSimplex.δ 1

private theorem δ_one_comp_stdSimplexJoinIso_inv :
    vertexZero ≫ (stdSimplexJoinIso 0 0).inv = joinInclLeft Δ[0] Δ[0] := by
  rw [Iso.comp_inv_eq, joinInclLeft_comp_stdSimplexJoinIso_hom, vertexZero]
  refine congrArg stdSimplex.map
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ ?_)))
  obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
  exact (AugmentedSimplexCategory.inl'_eval ⦋0⦌ ⦋0⦌ 0).symm

private theorem yonedaEquiv_symm_x₀_eq :
    (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) =
      vertexZero ≫ yonedaEquiv.symm coherentIso.hom.edge := by
  rw [vertexZero, stdSimplex.δ_comp_yonedaEquiv_symm, coherentIso.hom.src_eq]

theorem joinInclLeft_comp_isoEdge :
    joinInclLeft Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom ≫ isoEdge =
      yonedaEquiv.symm coherentIso.x₀ := by
  rw [← δ_one_comp_stdSimplexJoinIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
    yonedaEquiv_symm_x₀_eq]

private theorem hom_comp_joinInclLeft (Z : Under (Δ[0] : SSet.{u})) :
    Z.hom ≫ joinInclLeft Z.right Δ[0] = vertexZero ≫ coneEdge Z :=
  (joinInclLeft_comp_joinMap Z.hom (𝟙 Δ[0])).symm.trans
    ((congrArg (· ≫ joinMap Z.hom (𝟙 Δ[0])) δ_one_comp_stdSimplexJoinIso_inv).symm.trans
      (Category.assoc _ _ _))

theorem terminalization_obj_hom_eq (Z : Under (Δ[0] : SSet.{u})) :
    (terminalization.obj Z).hom =
      yonedaEquiv.symm coherentIso.x₀ ≫ terminalizationInr Z := by
  have h₀ := yonedaEquiv_symm_x₀_eq
  have h₁ := hom_comp_joinInclLeft Z
  calc (terminalization.obj Z).hom
      = (Z.hom ≫ joinInclLeft Z.right Δ[0]) ≫ terminalizationInl Z := (Category.assoc _ _ _).symm
    _ = vertexZero ≫ coneEdge Z ≫ terminalizationInl Z :=
      (congrArg (· ≫ terminalizationInl Z) h₁).trans (Category.assoc _ _ _)
    _ = _ := by rw [(isPushout_terminalization Z).w, h₀, Category.assoc]

private theorem rightAnodyneExtensions_coneEdge (Z : Under (Δ[0] : SSet.{u})) :
    rightAnodyneExtensions (coneEdge Z) :=
  have := mono_hom Z
  rightFibrations.llp.comp_mem _ _ (MorphismProperty.of_isIso _ _)
    (rightAnodyneExtensions_joinMap_id Z.hom)

theorem rightAnodyneExtensions_terminalization_obj_hom (Z : Under (Δ[0] : SSet.{u})) :
    rightAnodyneExtensions (terminalization.obj Z).hom := by
  rw [terminalization_obj_hom_eq]
  exact rightFibrations.llp.comp_mem _ _ (rightAnodyneExtensions_coherentIso_vertex false)
    (MorphismProperty.of_isPushout (P := rightFibrations.llp) (isPushout_terminalization Z).flip
      (rightAnodyneExtensions_coneEdge Z))

theorem rightAnodyneExtensions_comp_of_isPushout {E Y₁ Y₂ P : SSet.{u}} {f₁ : E ⟶ Y₁}
    {f₂ : E ⟶ Y₂} {g₁ : Y₁ ⟶ P} {g₂ : Y₂ ⟶ P} (h : IsPushout f₁ f₂ g₁ g₂) [Mono f₁]
    (t : Δ[0] ⟶ E) (hE : rightAnodyneExtensions t)
    (h₁ : rightAnodyneExtensions (t ≫ f₁)) (h₂ : rightAnodyneExtensions (t ≫ f₂)) :
    rightAnodyneExtensions (t ≫ f₁ ≫ g₁) := by
  rw [h.w, ← Category.assoc]
  exact rightFibrations.llp.comp_mem _ _ h₂ (MorphismProperty.of_isPushout
    (P := rightFibrations.llp) h.flip
    (modelCategoryJoyal.rightAnodyneExtensions_of_comp t f₁ hE h₁))

theorem rightAnodyneExtensions_comp_of_isPushout_point {U V P : SSet.{u}} {a : Δ[0] ⟶ U}
    {s : Δ[0] ⟶ V} {g₁ : U ⟶ P} {g₂ : V ⟶ P} (h : IsPushout a s g₁ g₂)
    (ha : rightAnodyneExtensions a) (t : Δ[0] ⟶ V) (ht : rightAnodyneExtensions t) :
    rightAnodyneExtensions (t ≫ g₂) :=
  rightFibrations.llp.comp_mem _ _ ht
    (MorphismProperty.of_isPushout (P := rightFibrations.llp) h.flip ha)

section Unit

open modelCategoryJoyal

private theorem weakEquivalence_yonedaEquiv_symm_x₀ :
    WeakEquivalence (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) := by
  have hE : weakEquivalences SSet.{u}
      ((Atoms.Homotopical.joyalInterval.{u}.cylinder.endpoint false).app (⊤_ SSet.{u})) :=
    Atoms.Homotopical.joyalInterval.{u}.cylinder.anodyne_le_weakEquivalences _
      innerHornInclusions_le_monomorphisms _
      (Atoms.Homotopical.joyalInterval.{u}.cylinder.anodyne_endpoint _ false _)
  have h : (Atoms.Homotopical.joyalInterval.{u}.cylinder.endpoint false).app (⊤_ SSet.{u}) ≫
      CartesianMonoidalCategory.fst _ _ = Atoms.Homotopical.joyalPoint false :=
    (Atoms.Homotopical.segmentEndpoint_app_fst _ _ _).trans
      ((congrArg (· ≫ _) (Subsingleton.elim _ (𝟙 _))).trans (Category.id_comp _))
  have hI : IsIso (CartesianMonoidalCategory.fst Atoms.Homotopical.joyalInterval.{u}.interval
      (⊤_ SSet.{u})) := Atoms.Homotopical.isIso_fst_terminal _
  have hF : weakEquivalences SSet.{u} (CartesianMonoidalCategory.fst
      Atoms.Homotopical.joyalInterval.{u}.interval (⊤_ SSet.{u})) :=
    (weakEquivalence_iff _).1 inferInstance
  have hP : weakEquivalences SSet.{u} (Atoms.Homotopical.joyalPoint false) :=
    h ▸ (weakEquivalences SSet.{u}).comp_mem _ _ hE hF
  have e : (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) =
      (terminalIsoIsTerminal stdSimplex.isTerminalObj₀).inv ≫
        Atoms.Homotopical.joyalPoint false :=
    (Iso.inv_hom_id_assoc _ _).symm
  rw [e, weakEquivalence_iff]
  exact (weakEquivalences SSet.{u}).comp_mem _ _ ((weakEquivalence_iff _).1 inferInstance) hP

private noncomputable def unitPushoutObjObj (Z : Under (Δ[0] : SSet.{u})) :
    (Functor.curry.obj joinFunctor).PushoutObjObj Z.hom (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
  let B : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  have := isIso_joinInclLeft_of_isEmpty Z.right B
  have := isIso_joinInclLeft_of_isEmpty (Δ[0] : SSet.{u}) B
  let e₀ : Δ[0] ≅ join Δ[0] B := asIso (joinInclLeft _ _)
  let e₁ : Z.right ≅ join Z.right B := asIso (joinInclLeft _ _)
  have hf : Z.hom ≫ e₁.hom = e₀.hom ≫ joinMap Z.hom (𝟙 B) :=
    (joinInclLeft_comp_joinMap Z.hom (𝟙 B)).symm
  have hg : vertexZero ≫ (stdSimplexJoinIso 0 0).symm.hom =
      e₀.hom ≫ joinMap (𝟙 Δ[0]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
    δ_one_comp_stdSimplexJoinIso_inv.trans
      ((joinInclLeft_comp_joinMap (𝟙 Δ[0]) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).trans
        (Category.id_comp _)).symm
  have hl : pushout.inl Z.hom vertexZero ≫ (Iso.refl _).hom =
      e₁.hom ≫ e₁.inv ≫ pushout.inl Z.hom vertexZero :=
    (Category.comp_id _).trans (e₁.hom_inv_id_assoc _).symm
  have hr : pushout.inr Z.hom vertexZero ≫ (Iso.refl _).hom =
      (stdSimplexJoinIso 0 0).symm.hom ≫ (stdSimplexJoinIso 0 0).hom ≫
        pushout.inr Z.hom vertexZero :=
    (Category.comp_id _).trans ((stdSimplexJoinIso 0 0).inv_hom_id_assoc _).symm
  have hι : e₁.inv ≫ joinInclLeft Z.right Δ[0] =
      joinMap (𝟙 Z.right) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
    (Iso.inv_comp_eq e₁).2 ((joinInclLeft_comp_joinMap _ _).trans (Category.id_comp _)).symm
  { pt := pushout Z.hom vertexZero
    inl := e₁.inv ≫ pushout.inl _ _
    inr := (stdSimplexJoinIso 0 0).hom ≫ pushout.inr _ _
    isPushout := (IsPushout.of_hasPushout Z.hom vertexZero).of_iso e₀ e₁
      (stdSimplexJoinIso 0 0).symm (Iso.refl _) hf hg hl hr
    ι := pushout.desc (joinInclLeft Z.right Δ[0]) (coneEdge Z) (hom_comp_joinInclLeft Z)
    inl_ι := (Category.assoc _ _ _).trans
      ((congrArg (e₁.inv ≫ ·) (pushout.inl_desc _ _ _)).trans hι)
    inr_ι := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pushout.inr_desc _ _ _)).trans
      (Iso.hom_inv_id_assoc _ _)) }

private theorem innerAnodyneExtensions_unitPushoutObjObj_ι (Z : Under (Δ[0] : SSet.{u}))
    (hZ : rightAnodyneExtensions Z.hom) : innerAnodyneExtensions (unitPushoutObjObj Z).ι :=
  innerAnodyneExtensions_pushoutObjObjι_join _ hZ

private noncomputable def unitRight (Z : Under (Δ[0] : SSet.{u})) :
    pushout Z.hom (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) ⟶
      (terminalization.obj Z).right :=
  pushout.desc (joinInclLeft Z.right Δ[0] ≫ terminalizationInl Z) (terminalizationInr Z)
    (terminalization_obj_hom_eq Z)

private noncomputable def unitMiddle (Z : Under (Δ[0] : SSet.{u})) :
    (unitPushoutObjObj Z).pt ⟶
      pushout Z.hom (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) :=
  pushout.desc (pushout.inl _ _) (yonedaEquiv.symm coherentIso.hom.edge ≫ pushout.inr _ _) (by
    rw [pushout.condition, yonedaEquiv_symm_x₀_eq, Category.assoc])

private theorem isPushout_unitMiddle (Z : Under (Δ[0] : SSet.{u})) :
    IsPushout (pushout.inr Z.hom vertexZero) (yonedaEquiv.symm coherentIso.hom.edge)
      (unitMiddle Z) (pushout.inr _ _) := by
  refine IsPushout.of_top ?_ (pushout.inr_desc _ _ _)
    (IsPushout.of_hasPushout Z.hom vertexZero)
  have h₄ : pushout.inl Z.hom vertexZero ≫ unitMiddle Z = pushout.inl _ _ :=
    pushout.inl_desc _ _ _
  exact (IsPushout.of_hasPushout Z.hom
    (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u})).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (yonedaEquiv_symm_x₀_eq.trans (Category.id_comp _).symm))
    ((Category.comp_id _).trans (h₄.symm.trans (Category.id_comp _).symm))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem isPushout_unitRight (Z : Under (Δ[0] : SSet.{u})) :
    IsPushout (unitPushoutObjObj Z).ι (unitMiddle Z) (terminalizationInl Z) (unitRight Z) := by
  have h₁ : pushout.inr Z.hom vertexZero ≫ (unitPushoutObjObj Z).ι = coneEdge Z :=
    pushout.inr_desc _ _ _
  have h₂ : pushout.inr Z.hom (yonedaEquiv.symm coherentIso.x₀) ≫ unitRight Z =
      terminalizationInr Z := pushout.inr_desc _ _ _
  have h₃ : pushout.inl Z.hom vertexZero ≫ (unitPushoutObjObj Z).ι =
      joinInclLeft Z.right Δ[0] := pushout.inl_desc _ _ _
  have h₄ : pushout.inl Z.hom vertexZero ≫ unitMiddle Z = pushout.inl _ _ :=
    pushout.inl_desc _ _ _
  have h₅ : pushout.inr Z.hom vertexZero ≫ unitMiddle Z =
      yonedaEquiv.symm coherentIso.hom.edge ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
  have h₆ : pushout.inl Z.hom (yonedaEquiv.symm coherentIso.x₀) ≫ unitRight Z =
      joinInclLeft Z.right Δ[0] ≫ terminalizationInl Z := pushout.inl_desc _ _ _
  refine IsPushout.of_left ?_ ?_ (isPushout_unitMiddle Z)
  · have h := isPushout_terminalization Z
    rw [← h₁, ← h₂] at h
    exact h
  · refine pushout.hom_ext ?_ ?_
    · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ terminalizationInl Z) h₃)).trans
        ((h₆.symm.trans (congrArg (· ≫ unitRight Z) h₄.symm)).trans (Category.assoc _ _ _))
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ terminalizationInl Z) h₁).trans
        ((isPushout_terminalization Z).w.trans (congrArg (_ ≫ ·) h₂.symm)))).trans
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ unitRight Z) h₅.symm)).trans
          (Category.assoc _ _ _))

theorem weakEquivalence_terminalizationUnit_app_right (Z : Under (Δ[0] : SSet.{u}))
    (hZ : rightAnodyneExtensions Z.hom) :
    WeakEquivalence (terminalizationUnit.app Z).right := by
  have := weakEquivalence_yonedaEquiv_symm_x₀
  have : Cofibration (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) :=
    (cofibration_iff _).2 (stdSimplex.isTerminalObj₀.mono_from _)
  have h₁ := (MorphismProperty.of_isPushout (P := trivialCofibrations SSet.{u})
    (IsPushout.of_hasPushout Z.hom (yonedaEquiv.symm coherentIso.x₀))
    (mem_trivialCofibrations _))
  rw [mem_trivialCofibrations_iff] at h₁
  obtain ⟨-, h₁⟩ := h₁
  have h₂ := weakEquivalence_of_innerAnodyneExtensions _
    (MorphismProperty.of_isPushout (P := innerAnodyneExtensions) (isPushout_unitRight Z).flip
      (innerAnodyneExtensions_unitPushoutObjObj_ι Z hZ))
  have h : (terminalizationUnit.app Z).right =
      pushout.inl Z.hom (yonedaEquiv.symm coherentIso.x₀) ≫ unitRight Z :=
    (pushout.inl_desc _ _ _).symm
  rw [h, weakEquivalence_iff]
  exact (weakEquivalences SSet.{u}).comp_mem _ _ ((weakEquivalence_iff _).1 h₁)
    ((weakEquivalence_iff _).1 h₂)

end Unit

end SSet
