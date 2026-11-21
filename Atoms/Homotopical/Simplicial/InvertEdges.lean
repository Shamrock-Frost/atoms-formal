import Atoms.Homotopical.Simplicial.CartesianJoyal
import Atoms.Homotopical.Simplicial.Terminalization

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial

universe u

namespace SSet

section InvertEdges

open Atoms.Homotopical

variable (Z : SSet.{u}) (E : Set (Z _⦋1⦌))

noncomputable def invertEdges : SSet.{u} :=
  pushout (Sigma.desc fun e : E => yonedaEquiv.symm e.1)
    (Limits.Sigma.map fun _ : E =>
      (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u}))

noncomputable def toInvertEdges : Z ⟶ invertEdges Z E :=
  pushout.inl _ _

private noncomputable def invertEdgesInr (e : E) : coherentIso.{u} ⟶ invertEdges Z E :=
  Sigma.ι (fun _ : E => coherentIso.{u}) e ≫ pushout.inr _ _

private theorem yonedaEquiv_symm_comp_toInvertEdges (e : E) :
    yonedaEquiv.symm e.1 ≫ toInvertEdges Z E =
      yonedaEquiv.symm coherentIso.hom.edge ≫ invertEdgesInr Z E e := by
  have hc : (Sigma.desc fun e : E => yonedaEquiv.symm e.1) ≫ toInvertEdges Z E =
      (Limits.Sigma.map fun _ : E =>
        (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})) ≫
        pushout.inr _ _ := pushout.condition
  exact (congrArg (· ≫ toInvertEdges Z E)
    (Sigma.ι_desc (fun e : E => (yonedaEquiv.symm e.1 : Δ[1] ⟶ Z)) e).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (Sigma.ι (fun _ : E => (Δ[1] : SSet.{u})) e ≫ ·) hc).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ pushout.inr _ _) (Sigma.ι_map _ e)).trans (Category.assoc _ _ _)))))

private theorem toInvertEdges_app_eq (e : E) :
    (toInvertEdges Z E).app _ e.1 = (invertEdgesInr Z E e).app _ coherentIso.hom.edge := by
  have h := congrArg yonedaEquiv (yonedaEquiv_symm_comp_toInvertEdges Z E e)
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at h

private def invertEdgesMarking : Set ((invertEdges Z E) _⦋1⦌) :=
  {e | ∃ (i : E) (x : coherentIso.{u} _⦋1⦌), (invertEdgesInr Z E i).app _ x = e}

private noncomputable abbrev invertEdgesMarked : MarkedSSet.{u} :=
  MarkedSSet.ofEdgeSet (invertEdges Z E) (invertEdgesMarking Z E)

private noncomputable def toInvertEdgesMarked :
    MarkedSSet.ofEdgeSet Z E ⟶ invertEdgesMarked Z E :=
  MarkedSSet.ofEdgeSetHom (toInvertEdges Z E) E _ fun e he =>
    ⟨⟨e, he⟩, _, (toInvertEdges_app_eq Z E ⟨e, he⟩).symm⟩

private noncomputable def edgesSharp :
    (∐ fun _ : E => (MarkedPresheaf.sharp edgeMarking).obj Δ[1]) ⟶ MarkedSSet.ofEdgeSet Z E :=
  Sigma.desc fun e => edgeHomMk (yonedaEquiv.symm e.1) fun x _ =>
    yonedaEquiv_symm_app_mem_marked ((MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl e.2)) x

private noncomputable def edgesSharpMap :
    (∐ fun _ : E => (MarkedPresheaf.sharp edgeMarking).obj Δ[1]) ⟶
      ∐ fun _ : E => MarkedSSet.sharpJ :=
  Limits.Sigma.map fun _ => (MarkedPresheaf.sharp edgeMarking).map
    (yonedaEquiv.symm coherentIso.hom.edge)

private noncomputable def invertEdgesMarkedInr :
    (∐ fun _ : E => MarkedSSet.sharpJ) ⟶ invertEdgesMarked Z E :=
  Sigma.desc fun e => edgeHomMk (invertEdgesInr Z E e) fun x _ =>
    (MarkedSSet.mem_marked_ofEdgeSet _ _ _).2 (Or.inl ⟨e, x, rfl⟩)

private theorem edgesSharp_comp_toInvertEdgesMarked :
    edgesSharp Z E ≫ toInvertEdgesMarked Z E =
      edgesSharpMap Z E ≫ invertEdgesMarkedInr Z E := by
  refine Sigma.hom_ext _ _ fun e ↦ ?_
  rw [← Category.assoc, ← Category.assoc, edgesSharp, edgesSharpMap, invertEdgesMarkedInr,
    Sigma.ι_desc, Sigma.ι_map, Category.assoc, Sigma.ι_desc]
  exact MarkedPresheaf.hom_ext (yonedaEquiv_symm_comp_toInvertEdges Z E e)

private def ofEdgeSetForget {X : MarkedSSet.{u}} (u : MarkedSSet.ofEdgeSet Z E ⟶ X) :
    Z ⟶ X.underlying :=
  MarkedPresheaf.forget.map u

private noncomputable def sharpJForget {X : MarkedSSet.{u}} (w : MarkedSSet.sharpJ ⟶ X) :
    coherentIso.{u} ⟶ X.underlying :=
  MarkedPresheaf.forget.map w

private theorem yonedaEquiv_symm_comp_ofEdgeSetForget {X : MarkedSSet.{u}}
    {u : MarkedSSet.ofEdgeSet Z E ⟶ X} {v : (∐ fun _ : E => MarkedSSet.sharpJ) ⟶ X}
    (huv : edgesSharp Z E ≫ u = edgesSharpMap Z E ≫ v) (e : E) :
    yonedaEquiv.symm e.1 ≫ ofEdgeSetForget Z E u =
      yonedaEquiv.symm coherentIso.hom.edge ≫
        sharpJForget (Sigma.ι (fun _ : E => MarkedSSet.sharpJ) e ≫ v) := by
  have h := congrArg (fun φ ↦ MarkedPresheaf.forget.map (Sigma.ι _ e ≫ φ)) huv
  rw [← Category.assoc, ← Category.assoc, edgesSharp, edgesSharpMap, Sigma.ι_desc,
    Sigma.ι_map, Category.assoc] at h
  exact h

private noncomputable def invertEdgesMarkedDescRight {X : MarkedSSet.{u}}
    (u : MarkedSSet.ofEdgeSet Z E ⟶ X) (v : (∐ fun _ : E => MarkedSSet.sharpJ) ⟶ X)
    (huv : edgesSharp Z E ≫ u = edgesSharpMap Z E ≫ v) :
    invertEdges Z E ⟶ X.underlying :=
  pushout.desc (ofEdgeSetForget Z E u)
    (Sigma.desc fun e => sharpJForget (Sigma.ι (fun _ : E => MarkedSSet.sharpJ) e ≫ v)) (by
    refine Sigma.hom_ext _ _ fun e ↦ ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
    exact yonedaEquiv_symm_comp_ofEdgeSetForget Z E huv e)

private noncomputable def invertEdgesMarkedForget {X : MarkedSSet.{u}}
    (m : invertEdgesMarked Z E ⟶ X) : invertEdges Z E ⟶ X.underlying :=
  MarkedPresheaf.forget.map m

private theorem invertEdgesInr_comp_invertEdgesMarkedDescRight {X : MarkedSSet.{u}}
    (u : MarkedSSet.ofEdgeSet Z E ⟶ X) (v : (∐ fun _ : E => MarkedSSet.sharpJ) ⟶ X)
    (huv : edgesSharp Z E ≫ u = edgesSharpMap Z E ≫ v) (i : E) :
    invertEdgesInr Z E i ≫ invertEdgesMarkedDescRight Z E u v huv =
      sharpJForget (Sigma.ι (fun _ : E => MarkedSSet.sharpJ) i ≫ v) :=
  (Category.assoc _ _ _).trans ((congrArg (Sigma.ι (fun _ : E => coherentIso.{u}) i ≫ ·)
    (pushout.inr_desc _ _ _)).trans (Sigma.ι_desc _ i))

private theorem invertEdgesMarkedDescRight_app_mem_marked {X : MarkedSSet.{u}}
    (u : MarkedSSet.ofEdgeSet Z E ⟶ X) (v : (∐ fun _ : E => MarkedSSet.sharpJ) ⟶ X)
    (huv : edgesSharp Z E ≫ u = edgesSharpMap Z E ≫ v) (e : (invertEdges Z E) _⦋1⦌)
    (he : e ∈ (invertEdgesMarked Z E).marked ⦋1⦌) :
    (invertEdgesMarkedDescRight Z E u v huv).app _ e ∈ X.marked ⦋1⦌ := by
  rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ e).1 he with ⟨i, x, rfl⟩ | ⟨x, rfl⟩
  · have h := invertEdgesInr_comp_invertEdgesMarkedDescRight Z E u v huv i
    have hx := MarkedPresheaf.map_mem_marked (Sigma.ι (fun _ : E => MarkedSSet.sharpJ) i ≫ v)
      ((MarkedPresheaf.mem_marked_sharp _ _ _ x).2 rfl)
    exact (ConcreteCategory.congr_hom (congr_app h _) x).symm ▸ hx
  · exact (σ_naturality_apply _ 0 x).symm ▸ X.map_σ_mem_marked _

private theorem isPushout_toInvertEdgesMarked :
    IsPushout (edgesSharp Z E) (edgesSharpMap Z E) (toInvertEdgesMarked Z E)
      (invertEdgesMarkedInr Z E) := by
  refine ⟨⟨edgesSharp_comp_toInvertEdgesMarked Z E⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ edgeHomMk (invertEdgesMarkedDescRight Z E s.inl s.inr s.condition)
      (invertEdgesMarkedDescRight_app_mem_marked Z E s.inl s.inr s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    refine MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans ?_)
    exact pushout.inl_desc _ _ _
  · intro s
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, invertEdgesMarkedInr, Sigma.ι_desc]
    refine MarkedPresheaf.hom_ext ((Functor.map_comp _ _ _).trans ?_)
    exact invertEdgesInr_comp_invertEdgesMarkedDescRight Z E _ _ s.condition i
  · intro s m h₁ h₂
    refine MarkedPresheaf.hom_ext ?_
    have hm : invertEdgesMarkedForget Z E m =
        invertEdgesMarkedDescRight Z E s.inl s.inr s.condition := by
      refine pushout.hom_ext ?_ (Sigma.hom_ext _ _ fun i ↦ ?_)
      · rw [invertEdgesMarkedDescRight, pushout.inl_desc]
        exact (Functor.map_comp _ _ _).symm.trans (congrArg MarkedPresheaf.forget.map h₁)
      · rw [invertEdgesMarkedDescRight, pushout.inr_desc, Sigma.ι_desc]
        have h := congrArg (fun φ ↦ MarkedPresheaf.forget.map
          (Sigma.ι (fun _ : E => MarkedSSet.sharpJ) i ≫ φ)) h₂
        rw [← Category.assoc, invertEdgesMarkedInr, Sigma.ι_desc, Functor.map_comp] at h
        exact (Category.assoc _ _ _).symm.trans h
    exact hm

section Cartesian

open MarkedSSet.modelCategoryCartesian

private theorem trivialCofibrations_sharp_map_hom_edge :
    trivialCofibrations MarkedSSet.{u} ((MarkedPresheaf.sharp edgeMarking).map
      (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})) :=
  ⟨cartesianCylinder.{u}.anodyne_le_monomorphisms _ cartesianGenerators_le_monomorphisms _
    (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.sharpHom),
    cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms _
      (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.sharpHom)⟩

theorem exists_weakEquivalence_ofEdgeSet_invertEdges :
    ∃ (W : MarkedSSet.{u}) (f : MarkedSSet.ofEdgeSet Z E ⟶ W)
      (g : (MarkedPresheaf.flat edgeMarking).obj (invertEdges Z E) ⟶ W),
      WeakEquivalence f ∧ WeakEquivalence g ∧ IsIso (MarkedPresheaf.forget.map g) ∧
        MarkedPresheaf.forget.map f = toInvertEdges Z E ≫ MarkedPresheaf.forget.map g := by
  let g : (MarkedPresheaf.flat edgeMarking).obj (invertEdges Z E) ⟶ invertEdgesMarked Z E :=
    ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm (𝟙 _)
  have hg : IsIso (MarkedPresheaf.forget.map g) := inferInstanceAs (IsIso (𝟙 (invertEdges Z E)))
  refine ⟨invertEdgesMarked Z E, toInvertEdgesMarked Z E, g, ?_, ?_, hg, ?_⟩
  · have h : trivialCofibrations MarkedSSet.{u} (edgesSharpMap Z E) := by
      rw [← fibrations_llp]
      exact MorphismProperty.colimMap (W := (fibrations MarkedSSet.{u}).llp) _ fun _ ↦ by
        rw [fibrations_llp]
        exact trivialCofibrations_sharp_map_hom_edge
    have := (MorphismProperty.of_isPushout (P := trivialCofibrations MarkedSSet.{u})
      (isPushout_toInvertEdgesMarked Z E) h).2
    exact (weakEquivalence_iff _).2 this
  · refine weakEquivalence_of_isIso_forget_map g fun F _ h _ e he ↦ ?_
    rcases (MarkedSSet.mem_marked_ofEdgeSet _ _ e).1 he with ⟨i, x, rfl⟩ | ⟨x, rfl⟩
    · exact SSet.coherentIso.nonempty_invStruct_app (invertEdgesInr Z E i ≫ h) x
    · exact ⟨(Edge.InvStruct.invStructId (h.app _ x)).ofEq (σ_naturality_apply h 0 x).symm⟩
  · exact (Category.comp_id _).symm

end Cartesian

end InvertEdges

section Localization

private noncomputable def coneLeibnizPushoutObjObj {A B : SSet.{u}} (i : A ⟶ B) :
    (Functor.curry.obj joinFunctor).PushoutObjObj i (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
  let D : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  have := isIso_joinInclLeft_of_isEmpty A D
  have := isIso_joinInclLeft_of_isEmpty B D
  let e₁ : A ≅ join A D := asIso (joinInclLeft _ _)
  let e₂ : B ≅ join B D := asIso (joinInclLeft _ _)
  have hf : i ≫ e₂.hom = e₁.hom ≫ joinMap i (𝟙 D) := (joinInclLeft_comp_joinMap i (𝟙 D)).symm
  have hg : joinInclLeft A Δ[0] ≫ (Iso.refl _).hom =
      e₁.hom ≫ joinMap (𝟙 A) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
    (Category.comp_id _).trans ((joinInclLeft_comp_joinMap (𝟙 A)
      (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι).trans (Category.id_comp _)).symm
  have hl : pushout.inr (joinInclLeft A Δ[0]) i ≫ (Iso.refl _).hom =
      e₂.hom ≫ e₂.inv ≫ pushout.inr (joinInclLeft A Δ[0]) i :=
    (Category.comp_id _).trans (e₂.hom_inv_id_assoc _).symm
  have hr : pushout.inl (joinInclLeft A Δ[0]) i ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ pushout.inl (joinInclLeft A Δ[0]) i :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have hι : e₂.inv ≫ joinInclLeft B Δ[0] =
      joinMap (𝟙 B) (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι :=
    (Iso.inv_comp_eq e₂).2 ((joinInclLeft_comp_joinMap _ _).trans (Category.id_comp _)).symm
  { pt := pushout (joinInclLeft A Δ[0]) i
    inl := e₂.inv ≫ pushout.inr _ _
    inr := pushout.inl _ _
    isPushout := (IsPushout.of_hasPushout (joinInclLeft A Δ[0]) i).flip.of_iso e₁ e₂
      (Iso.refl _) (Iso.refl _) hf hg hl hr
    ι := pushout.desc (joinMap i (𝟙 Δ[0])) (joinInclLeft B Δ[0])
      (joinInclLeft_comp_joinMap i (𝟙 Δ[0]))
    inl_ι := (Category.assoc _ _ _).trans
      ((congrArg (e₂.inv ≫ ·) (pushout.inr_desc _ _ _)).trans hι)
    inr_ι := pushout.inl_desc _ _ _ }

private theorem innerAnodyneExtensions_coneLeibnizPushoutObjObj_ι {A B : SSet.{u}} (i : A ⟶ B)
    (hi : rightAnodyneExtensions i) : innerAnodyneExtensions (coneLeibnizPushoutObjObj i).ι :=
  innerAnodyneExtensions_pushoutObjObjι_join _ hi

private theorem joinInclRight_comp_stdSimplexJoinIso_hom_eq :
    joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom = stdSimplex.δ 0 := by
  rw [joinInclRight_comp_stdSimplexJoinIso_hom]
  refine congrArg stdSimplex.map
    (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ ?_)))
  obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
  exact AugmentedSimplexCategory.inr'_eval ⦋0⦌ ⦋0⦌ 0

private theorem rightAnodyneExtensions_isoEdge :
    rightAnodyneExtensions (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u}) := by
  have := coherentIso.mono_hom_edge.{u}
  have h₁ : rightAnodyneExtensions (joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom) :=
    rightFibrations.llp.comp_mem _ _ (rightAnodyneExtensions_joinInclRight _)
      (MorphismProperty.of_isIso _ _)
  have h₂ : (joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso 0 0).hom) ≫
      (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u}) =
        yonedaEquiv.symm (cond true coherentIso.x₁ coherentIso.x₀) := by
    rw [joinInclRight_comp_stdSimplexJoinIso_hom_eq, stdSimplex.δ_comp_yonedaEquiv_symm,
      coherentIso.hom.tgt_eq]
    rfl
  refine modelCategoryJoyal.rightAnodyneExtensions_of_comp _ _ h₁ ?_
  rw [h₂]
  exact rightAnodyneExtensions_coherentIso_vertex true

variable (Z : Under (Δ[0] : SSet.{u})) (E : Set (Z.right _⦋1⦌))

private noncomputable abbrev invertEdgesUnder : Under (Δ[0] : SSet.{u}) :=
  Under.mk (Z.hom ≫ toInvertEdges Z.right E)

private noncomputable abbrev toInvertEdgesUnder : Z ⟶ invertEdgesUnder Z E :=
  Under.homMk (toInvertEdges Z.right E) rfl

private noncomputable abbrev edgesDesc : (∐ fun _ : E => (Δ[1] : SSet.{u})) ⟶ Z.right :=
  Sigma.desc fun e : E => yonedaEquiv.symm e.1

private noncomputable abbrev edgesMap :
    (∐ fun _ : E => (Δ[1] : SSet.{u})) ⟶ ∐ fun _ : E => coherentIso.{u} :=
  Limits.Sigma.map fun _ : E => (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})

private theorem isPushout_terminalization_invertEdges :
    IsPushout (joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z)
      (joinMap (edgesMap Z E) (𝟙 Δ[0])) (terminalization.map (toInvertEdgesUnder Z E)).right
      (joinMap (pushout.inr (edgesDesc Z E) (edgesMap Z E)) (𝟙 Δ[0]) ≫
        terminalizationInl (invertEdgesUnder Z E)) :=
  ((IsPushout.of_hasPushout (edgesDesc Z E) (edgesMap Z E)).map
      (joinRightUnder (Δ[0] : SSet.{u}) ⋙ Under.forget _)).paste_horiz
    (isPushout_terminalization_map (toInvertEdgesUnder Z E)).flip

private noncomputable abbrev localizationLeibniz : SSet.{u} :=
  pushout (joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z)
    (pushout.inl (joinInclLeft _ Δ[0]) (edgesMap Z E))

private noncomputable def localizationLeibnizDesc :
    localizationLeibniz Z E ⟶ (terminalization.obj (invertEdgesUnder Z E)).right :=
  pushout.desc (terminalization.map (toInvertEdgesUnder Z E)).right
    ((coneLeibnizPushoutObjObj (edgesMap Z E)).ι ≫
      joinMap (pushout.inr (edgesDesc Z E) (edgesMap Z E)) (𝟙 Δ[0]) ≫
        terminalizationInl (invertEdgesUnder Z E)) (by
    have h : pushout.inl (joinInclLeft _ Δ[0]) (edgesMap Z E) ≫
        (coneLeibnizPushoutObjObj (edgesMap Z E)).ι = joinMap (edgesMap Z E) (𝟙 Δ[0]) :=
      pushout.inl_desc _ _ _
    exact (isPushout_terminalization_invertEdges Z E).w.trans
      ((congrArg (· ≫ _) h.symm).trans (Category.assoc _ _ _)))

private theorem isPushout_localizationLeibnizDesc :
    IsPushout (pushout.inr (joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z)
        (pushout.inl (joinInclLeft _ Δ[0]) (edgesMap Z E)))
      (coneLeibnizPushoutObjObj (edgesMap Z E)).ι (localizationLeibnizDesc Z E)
      (joinMap (pushout.inr (edgesDesc Z E) (edgesMap Z E)) (𝟙 Δ[0]) ≫
        terminalizationInl (invertEdgesUnder Z E)) := by
  have h₁ : pushout.inl (joinInclLeft _ Δ[0]) (edgesMap Z E) ≫
      (coneLeibnizPushoutObjObj (edgesMap Z E)).ι = joinMap (edgesMap Z E) (𝟙 Δ[0]) :=
    pushout.inl_desc _ _ _
  have h₂ : pushout.inl _ _ ≫ localizationLeibnizDesc Z E =
      (terminalization.map (toInvertEdgesUnder Z E)).right := pushout.inl_desc _ _ _
  have h := isPushout_terminalization_invertEdges Z E
  rw [← h₁, ← h₂] at h
  exact h.of_top (pushout.inr_desc _ _ _) (IsPushout.of_hasPushout _ _)

private theorem innerAnodyneExtensions_localizationLeibnizDesc :
    innerAnodyneExtensions (localizationLeibnizDesc Z E) :=
  MorphismProperty.of_isPushout (P := innerAnodyneExtensions)
    (isPushout_localizationLeibnizDesc Z E) (innerAnodyneExtensions_coneLeibnizPushoutObjObj_ι _
      (MorphismProperty.colimMap (W := rightFibrations.llp) _
        fun _ ↦ rightAnodyneExtensions_isoEdge))

private theorem mono_terminalizationUnit_app_right : Mono (terminalizationUnit.app Z).right :=
  have := coherentIso.mono_hom_edge.{u}
  have := Adhesive.mono_of_isPushout_of_mono_right (isPushout_terminalization Z)
  inferInstanceAs (Mono (joinInclLeft Z.right Δ[0] ≫ terminalizationInl Z))

private noncomputable def edgesEquiv :
    E ≃ ((terminalizationUnit.app Z).right.app _ '' E) :=
  Equiv.ofBijective (fun e ↦ ⟨_, e.1, e.2, rfl⟩)
    ⟨fun _ _ h ↦ Subtype.ext (((mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_terminalizationUnit_app_right Z) _)) (congrArg Subtype.val h)),
      fun ⟨_, e, he, h⟩ ↦ ⟨⟨e, he⟩, Subtype.ext h⟩⟩

private theorem isPushout_invertEdges_terminalization :
    IsPushout (joinInclLeft _ Δ[0] ≫ joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z)
      (edgesMap Z E) (toInvertEdges _ ((terminalizationUnit.app Z).right.app _ '' E))
      ((Sigma.reindex (edgesEquiv Z E) (fun _ ↦ coherentIso.{u})).hom ≫ pushout.inr _ _) := by
  let eA : (∐ fun _ : E => (Δ[1] : SSet.{u})) ≅ _ :=
    Sigma.reindex (edgesEquiv Z E) (fun _ ↦ (Δ[1] : SSet.{u}))
  let eB : (∐ fun _ : E => coherentIso.{u}) ≅ _ :=
    Sigma.reindex (edgesEquiv Z E) (fun _ ↦ coherentIso.{u})
  have hf : eA.hom ≫ (Sigma.desc fun e : ((terminalizationUnit.app Z).right.app _ '' E) =>
      (yonedaEquiv.symm e.1 : Δ[1] ⟶ _)) =
        joinInclLeft _ Δ[0] ≫ joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z := by
    refine Sigma.hom_ext _ _ fun e ↦ (Sigma.ι_reindex_hom_assoc (edgesEquiv Z E)
      (fun _ ↦ (Δ[1] : SSet.{u})) e _).trans ?_
    rw [Sigma.ι_desc, joinInclLeft_comp_joinMap_assoc, Sigma.ι_desc_assoc, ← Category.assoc,
      yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]
    rfl
  have hg : eA.hom ≫ (Limits.Sigma.map fun _ :
      ((terminalizationUnit.app Z).right.app _ '' E) =>
        (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})) =
      edgesMap Z E ≫ eB.hom := by
    refine Sigma.hom_ext _ _ fun e ↦ (Sigma.ι_reindex_hom_assoc (edgesEquiv Z E)
      (fun _ ↦ (Δ[1] : SSet.{u})) e _).trans ?_
    rw [Sigma.ι_map, Sigma.ι_map_assoc]
    exact congrArg (_ ≫ ·) (Sigma.ι_reindex_hom (edgesEquiv Z E) (fun _ ↦ coherentIso.{u}) e).symm
  exact (IsPushout.of_hasPushout _ _).of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    ((Category.comp_id _).trans ((Iso.eq_inv_comp _).2 hf))
    ((Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 hg).trans (Category.assoc _ _ _).symm))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (eB.inv_hom_id_assoc _).symm)

theorem exists_innerAnodyneExtensions_invertEdges_terminalization :
    ∃ φ : invertEdges (terminalization.obj Z).right
          ((terminalizationUnit.app Z).right.app _ '' E) ⟶
        (terminalization.obj (Under.mk (Z.hom ≫ toInvertEdges Z.right E))).right,
      toInvertEdges _ _ ≫ φ =
          (terminalization.map (Under.homMk (toInvertEdges Z.right E) rfl :
            Z ⟶ Under.mk (Z.hom ≫ toInvertEdges Z.right E))).right ∧
        innerAnodyneExtensions φ := by
  let e := (isPushout_invertEdges_terminalization Z E).isoIsPushout _ _
    ((IsPushout.of_hasPushout _ _).paste_horiz (IsPushout.of_hasPushout
      (joinMap (edgesDesc Z E) (𝟙 Δ[0]) ≫ terminalizationInl Z)
      (pushout.inl (joinInclLeft _ Δ[0]) (edgesMap Z E))))
  refine ⟨e.hom ≫ localizationLeibnizDesc Z E, ?_, ?_⟩
  · rw [IsPushout.inl_isoIsPushout_hom_assoc]
    exact pushout.inl_desc _ _ _
  · exact innerFibrations.llp.comp_mem _ _ (MorphismProperty.of_isIso _ _)
      (innerAnodyneExtensions_localizationLeibnizDesc Z E)

end Localization

end SSet
