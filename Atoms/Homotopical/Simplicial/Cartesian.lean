import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Atoms.Homotopical.Cylinder.ModelStructure
import Atoms.Homotopical.Marked.Cellular
import Atoms.Homotopical.Simplicial.Joyal
import Atoms.Homotopical.Simplicial.Marked

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial
open MonoidalCategory

universe u w

namespace Atoms.Homotopical

section Invertible

open SSet

theorem coherentIso_vertex_eq (v : coherentIso.{u} _⦋0⦌) :
    ∃ b : Bool, v = cond b coherentIso.x₁ coherentIso.x₀ := by
  refine ⟨coherentIso.simplexEquiv v 0, coherentIso.simplexEquiv.injective (funext fun i => ?_)⟩
  obtain rfl := Fin.fin_one_eq_zero i
  cases coherentIso.simplexEquiv v 0 <;> rfl

private theorem exists_coherentIso_edge (ε : Bool) :
    ∃ k : coherentIso.{u} _⦋1⦌, coherentIso.δ 1 k = cond ε coherentIso.x₁ coherentIso.x₀ ∧
      coherentIso.δ 0 k = cond (!ε) coherentIso.x₁ coherentIso.x₀ := by
  cases ε
  · exact ⟨coherentIso.hom.edge, coherentIso.hom.src_eq, coherentIso.hom.tgt_eq⟩
  · exact ⟨coherentIso.inv.edge, coherentIso.inv.src_eq, coherentIso.inv.tgt_eq⟩

theorem nonempty_invStruct_app_prod_σ {Z C : SSet.{u}}
    (f : coherentIso.{u} ⊗ C ⟶ Z) (j : coherentIso.{u} _⦋1⦌) (c : C _⦋0⦌) :
    Nonempty (Edge.mk'
      (f.app _ ((j, C.σ 0 c) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋1⦌))).InvStruct := by
  let g : coherentIso.{u} ⟶ coherentIso.{u} ⊗ C := CartesianMonoidalCategory.lift (𝟙 _)
    (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm c)
  refine nonempty_invStruct_congr ?_ (coherentIso.nonempty_invStruct_app (g ≫ f) j)
  refine congrArg (f.app _) (Prod.ext rfl ?_)
  change C.map (stdSimplex.objEquiv ((stdSimplex.isTerminalObj₀.from _).app _ j)).op c =
    C.map (SimplexCategory.σ 0).op c
  exact congrArg (fun g : ⦋1⦌ ⟶ ⦋0⦌ => C.map g.op c)
    (SimplexCategory.Hom.ext_one_left _ _ (Subsingleton.elim (α := Fin 1) _ _)
      (Subsingleton.elim (α := Fin 1) _ _))

theorem nonempty_invStruct_app_prod {Z C : SSet.{u}} [Z.Quasicategory]
    (f : coherentIso.{u} ⊗ C ⟶ Z) (ε : Bool) (b : C _⦋1⦌)
    (hb : Nonempty (Edge.mk' (f.app _ ((coherentIso.σ 0 (cond ε coherentIso.x₁ coherentIso.x₀),
      b) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋1⦌))).InvStruct)
    (j : coherentIso.{u} _⦋1⦌) :
    Nonempty (Edge.mk' (f.app _ ((j, b) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋1⦌))).InvStruct := by
  let P : coherentIso.{u} _⦋1⦌ → C _⦋1⦌ → Prop := fun j b =>
    Nonempty (Edge.mk' (f.app _ ((j, b) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋1⦌))).InvStruct
  have hδ (i : Fin 3) (x : coherentIso.{u} _⦋2⦌) (y : C _⦋2⦌) :
      Z.δ i (f.app _ ((x, y) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋2⦌)) =
        f.app _ ((coherentIso.δ i x, C.δ i y) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋1⦌) :=
    (δ_naturality_apply f i _).symm
  have F₁ (j : coherentIso.{u} _⦋1⦌) (b : C _⦋1⦌) (h₂ : P (coherentIso.σ 0 (coherentIso.δ 1 j)) b)
      (h₀ : P j (C.σ 0 (C.δ 0 b))) : P j b := by
    have := nonempty_invStruct_δ_one
      (f.app _ ((coherentIso.σ 0 j, C.σ 1 b) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋2⦌))
    rw [hδ, hδ, hδ] at this
    refine nonempty_invStruct_congr ?_ (this (nonempty_invStruct_congr ?_ h₂)
      (nonempty_invStruct_congr ?_ h₀))
    · exact congrArg (f.app _) (Prod.ext (δ_comp_σ_succ_apply (i := 0) j)
        (δ_comp_σ_self_apply (i := 1) b))
    · exact congrArg (f.app _) (Prod.ext (δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) j).symm
        (δ_comp_σ_succ_apply (i := 1) b).symm)
    · exact congrArg (f.app _) (Prod.ext (δ_comp_σ_self_apply (i := 0) j).symm
        (δ_comp_σ_of_le_apply (i := 0) (j := 0) (by decide) b).symm)
  have F₂ (j : coherentIso.{u} _⦋1⦌) (b : C _⦋1⦌) (h₂ : P j (C.σ 0 (C.δ 1 b))) (h₁ : P j b) :
      P (coherentIso.σ 0 (coherentIso.δ 0 j)) b := by
    have := nonempty_invStruct_δ_zero
      (f.app _ ((coherentIso.σ 1 j, C.σ 0 b) : (coherentIso.{u} ⊗ C : SSet.{u}) _⦋2⦌))
    rw [hδ, hδ, hδ] at this
    refine nonempty_invStruct_congr ?_ (this (nonempty_invStruct_congr ?_ h₂)
      (nonempty_invStruct_congr ?_ h₁))
    · exact congrArg (f.app _) (Prod.ext
        (δ_comp_σ_of_le_apply (i := 0) (j := 0) (by decide) j) (δ_comp_σ_self_apply (i := 0) b))
    · exact congrArg (f.app _) (Prod.ext (δ_comp_σ_succ_apply (i := 1) j).symm
        (δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) b).symm)
    · exact congrArg (f.app _) (Prod.ext (δ_comp_σ_self_apply (i := 1) j).symm
        (δ_comp_σ_succ_apply (i := 0) b).symm)
  have hv (v : coherentIso.{u} _⦋0⦌) : P (coherentIso.σ 0 v) b := by
    obtain ⟨b', rfl⟩ := coherentIso_vertex_eq v
    by_cases hb' : b' = ε
    · exact hb' ▸ hb
    obtain rfl : b' = !ε := by cases b' <;> cases ε <;> first | rfl | exact absurd rfl hb'
    obtain ⟨k, hk₁, hk₀⟩ := exists_coherentIso_edge ε
    have hkb : P k b := F₁ k b (hk₁ ▸ hb) (nonempty_invStruct_app_prod_σ f k _)
    exact hk₀ ▸ F₂ k b (nonempty_invStruct_app_prod_σ f k _) hkb
  exact F₁ j b (hv _) (nonempty_invStruct_app_prod_σ f j _)

private theorem hasLift_coherentIso_hom {P Q : SSet.{u}} [P.Quasicategory] [Q.Quasicategory]
    (π : P ⟶ Q) [Isofibration π] {u : Δ[1] ⟶ P} {v : coherentIso.{u} ⟶ Q}
    (sq : CommSq u (yonedaEquiv.symm coherentIso.hom.edge) π v)
    (hu : Nonempty (Edge.mk' (yonedaEquiv u)).InvStruct) : sq.HasLift := by
  have := coherentIso.mono_hom_edge.{u}
  have hlift : HasLiftingProperty (yonedaEquiv.symm coherentIso.hom.edge :
      Δ[1] ⟶ coherentIso.{u}) (coreMap π) :=
    hasLiftingProperty_of_range_ι _ _ (coherentIso.hasLiftingProperty_ι_of_horn_zero false 1 _
      coherentIso.mem_range_hom_iff _ (hasLiftingProperty_horn_zero_coreMap π))
  have he : yonedaEquiv u ∈ P.core.obj _ := mem_core_of_isIso _ fun i hi => by
    obtain rfl : i = 1 := by
      fin_cases i
      · exact absurd hi (lt_irrefl _)
      · rfl
    rw [show SimplexCategory.mkOfLe (0 : Fin 2) 1 (Fin.zero_le _) = 𝟙 _ from
      SimplexCategory.Hom.ext_one_left _ _ rfl rfl, op_id, CategoryTheory.Functor.map_id_apply]
    exact hu.some.isIso_homMk
  have hu' : Subcomplex.range u ≤ P.core := by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
    exact he
  have sq' : CommSq (Subcomplex.lift u hu') (yonedaEquiv.symm coherentIso.hom.edge) (coreMap π)
      (Subcomplex.lift v (range_le_core v fun e => coherentIso.nonempty_invStruct_app (𝟙 _) e)) :=
    ⟨by rw [← cancel_mono Q.core.ι, Category.assoc, coreMap_ι, Subcomplex.lift_ι_assoc, sq.w,
      Category.assoc, Subcomplex.lift_ι]⟩
  obtain ⟨l⟩ := (hlift.sq_hasLift sq').exists_lift
  refine ⟨⟨⟨l.l ≫ P.core.ι, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, l.fac_left, Subcomplex.lift_ι]
  · rw [Category.assoc, ← coreMap_ι, ← Category.assoc, l.fac_right, Subcomplex.lift_ι]

private theorem quasicategory_of_isTerminal {T : SSet.{u}} (hT : IsTerminal T) :
    T.Quasicategory := by
  have : IsIso (terminal.from T) := isIso_of_isTerminal hT terminalIsTerminal _
  rw [quasicategory_iff_innerFibration]
  exact ⟨MorphismProperty.rlp_of_isIso _ _⟩

private theorem isofibration_of_isTerminal {E T : SSet.{u}} [E.Quasicategory] (q : E ⟶ T)
    (hT : IsTerminal T) : Isofibration q where
  mem := fun _ _ f hf => ⟨fun {a b} sq => by
    have := mem_innerFibrations (terminal.from E) f hf
    have sq' : CommSq a f (terminal.from E) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
    exact ⟨⟨⟨sq'.lift, sq'.fac_left, hT.hom_ext _ _⟩⟩⟩⟩
  exists_lift x₀ _ _ _ :=
    ⟨x₀, Edge.id x₀, ⟨Edge.InvStruct.invStructId x₀⟩,
      SSet.yonedaEquiv.symm.injective (hT.hom_ext _ _)⟩

private theorem hasLiftingProperty_pre_vertex (E : SSet.{u}) [E.Quasicategory] {K L : SSet.{u}}
    (m : K ⟶ L) [Mono m] :
    HasLiftingProperty m ((MonoidalClosed.pre (yonedaEquiv.symm coherentIso.x₀ :
      Δ[0] ⟶ coherentIso.{u})).app E) := by
  have := quasicategory_of_isTerminal (terminalIsTerminal (C := SSet.{u}))
  let v : Δ[0] ⟶ coherentIso.{u} := yonedaEquiv.symm coherentIso.x₀
  let p := terminal.from E
  have h : HasLiftingProperty v
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom m p).π :=
    hasLiftingProperty_coherentIso_vertex_pullbackObjObjπ false p m _
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) m v
  rw [← MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂,
    HasLiftingProperty.iff_of_arrow_iso_left
      (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
        Arrow.isoMk (Iso.refl _) (β_ _ _))] at h
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom v p
  rw [MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃] at h
  have ht (A : SSet.{u}) : IsTerminal ((ihom A).obj (⊤_ SSet.{u})) :=
    terminalIsTerminal.isTerminalObj (ihom A) _
  have : IsIso ((MonoidalClosed.internalHom.map v.op).app (⊤_ SSet.{u})) :=
    isIso_of_isTerminal (ht _) (ht _) _
  have hf : IsIso sq₁₃.fst := sq₁₃.isPullback.isIso_fst_of_isIso
  exact HasLiftingProperty.of_arrow_iso_right m
    (Arrow.isoMk (Iso.refl _) (@asIso _ _ _ _ sq₁₃.fst hf)
      ((Category.id_comp _).trans sq₁₃.π_fst.symm) :
      Arrow.mk sq₁₃.π ≅ Arrow.mk ((MonoidalClosed.pre v).app E))

private theorem nonempty_invStruct_of_pre_vertex (E : SSet.{u}) [E.Quasicategory]
    (e : ((ihom coherentIso.{u}).obj E) _⦋1⦌)
    (he : Nonempty (Edge.mk' ((MonoidalClosed.pre (yonedaEquiv.symm coherentIso.x₀ :
      Δ[0] ⟶ coherentIso.{u})).app E |>.app _ e)).InvStruct) :
    Nonempty (Edge.mk' e).InvStruct := by
  have hr : rightFibrations ((MonoidalClosed.pre (yonedaEquiv.symm coherentIso.x₀ :
      Δ[0] ⟶ coherentIso.{u})).app E) := by
    rintro _ _ _ ⟨i, -⟩
    exact hasLiftingProperty_pre_vertex E _
  exact nonempty_invStruct_of_rightFibrations hr (Edge.mk' e) ⟨he.some.ofEq rfl⟩

private def quasicategoryIsofibrations : MorphismProperty SSet.{u} :=
  fun X Y p => X.Quasicategory ∧ Y.Quasicategory ∧ Isofibration p

private theorem yonedaEquiv_symm_x₀_eq :
    (yonedaEquiv.symm coherentIso.x₀ : Δ[0] ⟶ coherentIso.{u}) =
      ((terminalIsoIsTerminal stdSimplex.isTerminalObj₀.{u}).inv ≫ coprod.inl) ≫
        joyalInterval.{u}.boundary := by
  change _ = _ ≫ coprod.desc (joyalPoint.{u} false) (joyalPoint.{u} true)
  rw [Category.assoc, coprod.inl_desc, joyalPoint, Iso.inv_hom_id_assoc]
  rfl

private theorem llp_bothBox_hom_edge : quasicategoryIsofibrations.llp
    (joyalInterval.{u}.cylinder.bothBox (SSet.yonedaEquiv.symm coherentIso.hom.edge :
      Δ[1] ⟶ coherentIso.{u})) := by
  rintro E B p ⟨_, _, _⟩
  let sq₁₃ :=
    Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom joyalInterval.{u}.boundary p
  refine (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
    (joyalInterval.{u}.bothBoxPushoutObjObj _) sq₁₃).2 ⟨fun {u w} sq => ?_⟩
  have := quasicategory_pullbackObjObj_pt p _ sq₁₃
  have := isofibration_pullbackObjObjπ p joyalInterval.{u}.boundary sq₁₃
  have hJ : ((ihom coherentIso.{u}).obj E).Quasicategory := inferInstance
  have : SSet.Quasicategory
      ((MonoidalClosed.internalHom.obj (op joyalInterval.{u}.interval)).obj E) := hJ
  refine hasLift_coherentIso_hom sq₁₃.π sq (nonempty_invStruct_of_pre_vertex E _ ?_)
  let ι₀ : Δ[0] ⟶ (⊤_ SSet.{u}) ⨿ (⊤_ SSet.{u}) :=
    (terminalIsoIsTerminal stdSimplex.isTerminalObj₀).inv ≫ coprod.inl
  let G : coherentIso.{u} ⟶ (ihom Δ[0]).obj E := w ≫ sq₁₃.fst ≫ (MonoidalClosed.pre ι₀).app E
  have key : u ≫ (MonoidalClosed.pre (SSet.yonedaEquiv.symm coherentIso.x₀ :
      Δ[0] ⟶ coherentIso.{u})).app E = SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ G := by
    have e₁ : (MonoidalClosed.pre (SSet.yonedaEquiv.symm coherentIso.x₀ :
        Δ[0] ⟶ coherentIso.{u})).app E =
        (MonoidalClosed.internalHom.map joyalInterval.{u}.boundary.op).app E ≫
          (MonoidalClosed.pre ι₀).app E := by
      rw [yonedaEquiv_symm_x₀_eq]
      exact congrArg (fun t => t.app E) (MonoidalClosed.pre_map ι₀ joyalInterval.{u}.boundary)
    calc _ = u ≫ (MonoidalClosed.internalHom.map joyalInterval.{u}.boundary.op).app E ≫
          (MonoidalClosed.pre ι₀).app E := congrArg (u ≫ ·) e₁
      _ = (u ≫ sq₁₃.π) ≫ sq₁₃.fst ≫ (MonoidalClosed.pre ι₀).app E :=
        (congrArg (u ≫ ·) (sq₁₃.π_fst_assoc _).symm).trans (Category.assoc _ _ _).symm
      _ = _ := by rw [sq.w, Category.assoc]
  refine nonempty_invStruct_congr ?_ (coherentIso.nonempty_invStruct_app G coherentIso.hom.edge)
  have h₁ : SSet.yonedaEquiv (SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ G) =
      G.app _ coherentIso.hom.edge :=
    (SSet.yonedaEquiv_comp _ G).trans (congrArg _ (Equiv.apply_symm_apply _ _))
  exact h₁.symm.trans ((congrArg SSet.yonedaEquiv key).symm.trans (SSet.yonedaEquiv_comp _ _))

end Invertible

private theorem mem_marked_of_edges {X Y : MarkedSSet.{u}} (f : X.underlying ⟶ Y.underlying)
    (hf : ∀ e ∈ X.marked ⦋1⦌, f.app _ e ∈ Y.marked ⦋1⦌) (a : SimplexCategory)
    (x : X.underlying.obj (op a)) (hx : x ∈ X.marked a) : f.app (op a) x ∈ Y.marked a := by
  obtain ⟨n⟩ := a
  obtain rfl : n = 1 := X.len_eq_one_of_mem_marked hx
  exact hf x hx

noncomputable def edgeHomMk {X Y : MarkedSSet.{u}} (f : X.underlying ⟶ Y.underlying)
    (hf : ∀ e ∈ X.marked ⦋1⦌, f.app _ e ∈ Y.marked ⦋1⦌) : X ⟶ Y :=
  MarkedPresheaf.homMk f (mem_marked_of_edges f hf)

noncomputable abbrev MarkedSSet.sharpJ : MarkedSSet.{u} :=
  (MarkedPresheaf.sharp edgeMarking).obj SSet.coherentIso.{u}

private noncomputable def toSharpTerminal (X : MarkedSSet.{u}) :
    X ⟶ (MarkedPresheaf.sharp edgeMarking).obj (⊤_ SSet.{u}) :=
  (MarkedPresheaf.isTerminalSharpTerminal edgeMarking).from X

private noncomputable def sharpPoint (ε : Bool) :
    (MarkedPresheaf.sharp edgeMarking).obj (⊤_ SSet.{u}) ⟶ MarkedSSet.sharpJ :=
  (MarkedPresheaf.sharp edgeMarking).map (joyalPoint.{u} ε)

noncomputable def cartesianEndpoint (ε : Bool) :
    𝟭 MarkedSSet.{u} ⟶ prod.functor.obj MarkedSSet.sharpJ where
  app X := (prod.lift (toSharpTerminal X ≫ sharpPoint ε) (𝟙 X) : X ⟶ MarkedSSet.sharpJ ⨯ X)
  naturality X Y f := by
    change f ≫ prod.lift (toSharpTerminal Y ≫ sharpPoint ε) (𝟙 Y) =
      prod.lift (toSharpTerminal X ≫ sharpPoint ε) (𝟙 X) ≫ prod.map (𝟙 _) f
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.assoc, prod.map_fst, Category.comp_id,
        prod.lift_fst, ← Category.assoc]
      congr 1
      exact (MarkedPresheaf.isTerminalSharpTerminal edgeMarking).hom_ext _ _
    · rw [Category.assoc, prod.lift_snd, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
        Category.comp_id, Category.id_comp]

noncomputable def cartesianContraction : prod.functor.obj MarkedSSet.sharpJ ⟶ 𝟭 MarkedSSet.{u} where
  app _ := prod.snd
  naturality _ _ _ := prod.map_snd _ _

private noncomputable def forgetProdIso (X : MarkedSSet.{u}) :
    MarkedPresheaf.forget.obj (MarkedSSet.sharpJ ⨯ X) ≅
      MarkedPresheaf.forget.obj MarkedSSet.sharpJ ⊗ MarkedPresheaf.forget.obj X where
  hom := CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
    (MarkedPresheaf.forget.map prod.snd)
  inv := prod.lift (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _) ≫
    (PreservesLimitPair.iso MarkedPresheaf.forget MarkedSSet.sharpJ X).inv
  hom_inv_id := by
    rw [← cancel_mono (PreservesLimitPair.iso MarkedPresheaf.forget MarkedSSet.sharpJ X).hom,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp,
      PreservesLimitPair.iso_hom]
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, CartesianMonoidalCategory.lift_fst, prodComparison_fst]
    · rw [Category.assoc, prod.lift_snd, CartesianMonoidalCategory.lift_snd, prodComparison_snd]
  inv_hom_id := by
    have h₁ : ((PreservesLimitPair.iso MarkedPresheaf.forget MarkedSSet.sharpJ X).inv ≫
        CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
          (MarkedPresheaf.forget.map prod.snd)) ≫ CartesianMonoidalCategory.fst _ _ = prod.fst := by
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst, ← prodComparison_fst,
        ← PreservesLimitPair.iso_hom, Iso.inv_hom_id_assoc]
    have h₂ : ((PreservesLimitPair.iso MarkedPresheaf.forget MarkedSSet.sharpJ X).inv ≫
        CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
          (MarkedPresheaf.forget.map prod.snd)) ≫ CartesianMonoidalCategory.snd _ _ = prod.snd := by
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← prodComparison_snd,
        ← PreservesLimitPair.iso_hom, Iso.inv_hom_id_assoc]
    rw [Category.assoc]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₁, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, h₂, prod.lift_snd, Category.id_comp]

private theorem forget_map_cartesianEndpoint_app (ε : Bool) (X : MarkedSSet.{u}) :
    MarkedPresheaf.forget.map ((cartesianEndpoint ε).app X) ≫ (forgetProdIso X).hom =
      (joyalInterval.{u}.cylinder.endpoint ε).app (MarkedPresheaf.forget.obj X) := by
  change MarkedPresheaf.forget.map (prod.lift (toSharpTerminal X ≫ sharpPoint ε) (𝟙 X)) ≫
      CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
        (MarkedPresheaf.forget.map prod.snd) =
    CartesianMonoidalCategory.lift (terminal.from _ ≫ joyalPoint.{u} ε) (𝟙 _)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.lift_fst, ← Functor.map_comp, prod.lift_fst,
      Functor.map_comp]
    refine Eq.trans ?_ (CartesianMonoidalCategory.lift_fst _ _).symm
    exact congrArg (· ≫ joyalPoint.{u} ε) (terminal.hom_ext _ _)
  · rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← Functor.map_comp, prod.lift_snd,
      CategoryTheory.Functor.map_id]
    exact (CartesianMonoidalCategory.lift_snd _ _).symm

private theorem mono_cartesianEndpoints (X : MarkedSSet.{u}) :
    Mono (coprod.desc ((cartesianEndpoint false).app X) ((cartesianEndpoint true).app X)) := by
  let F := MarkedPresheaf.forget (D := edgeMarking)
  rw [MarkedPresheaf.mono_iff]
  have h : coprodComparison F X X ≫
      F.map (coprod.desc ((cartesianEndpoint false).app X) ((cartesianEndpoint true).app X)) =
    joyalInterval.{u}.cylinder.endpoints (F.obj X) ≫ (forgetProdIso X).inv := by
    refine (Iso.eq_comp_inv _).2 ?_
    apply coprod.hom_ext
    · simp only [coprodComparison, Category.assoc, coprod.inl_desc_assoc, ← F.map_comp_assoc,
        coprod.inl_desc, ExactCylinder.inl_endpoints]
      exact forget_map_cartesianEndpoint_app false X
    · simp only [coprodComparison, Category.assoc, coprod.inr_desc_assoc, ← F.map_comp_assoc,
        coprod.inr_desc, ExactCylinder.inr_endpoints]
      exact forget_map_cartesianEndpoint_app true X
  have : F.map (coprod.desc ((cartesianEndpoint false).app X) ((cartesianEndpoint true).app X)) =
      inv (coprodComparison F X X) ≫ joyalInterval.{u}.cylinder.endpoints (F.obj X) ≫
        (forgetProdIso X).inv := by
    exact (IsIso.eq_inv_comp _).2 h
  have hm : Mono (joyalInterval.{u}.cylinder.endpoints (F.obj X)) := inferInstance
  have hi : Mono (forgetProdIso X).inv := inferInstance
  rw [this]
  exact @mono_comp _ _ _ _ _ _ (inferInstance : Mono (inv (coprodComparison F X X))) _
    (@mono_comp _ _ _ _ _ _ hm _ hi)

noncomputable def cartesianCylinder : ExactCylinder.{u} MarkedSSet.{u} where
  I := prod.functor.obj MarkedSSet.sharpJ
  endpoint := cartesianEndpoint
  contraction := cartesianContraction
  endpoint_contraction ε := by
    ext X : 2
    exact prod.lift_snd _ _
  mono_endpoints := mono_cartesianEndpoints
  preservesMonomorphisms := ⟨fun f _ => inferInstanceAs (Mono (prod.map (𝟙 _) f))⟩
  preservesColimits := (Adjunction.ofIsLeftAdjoint _).leftAdjoint_preservesColimits

noncomputable def cartesianCylinderForgetIso :
    cartesianCylinder.{u}.I ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.forget ⋙ joyalInterval.{u}.cylinder.I :=
  NatIso.ofComponents forgetProdIso fun {X Y} f => by
    have key : MarkedPresheaf.forget.map (prod.map (𝟙 MarkedSSet.sharpJ) f) ≫
        (forgetProdIso Y).hom =
      (forgetProdIso X).hom ≫ (_ ◁ MarkedPresheaf.forget.map f) := by
      dsimp only [forgetProdIso]
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst,
          CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst,
          ← Functor.map_comp, prod.map_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd,
          CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd_assoc,
          ← Functor.map_comp, ← Functor.map_comp, prod.map_snd]
    exact key

theorem whiskerRight_endpoint_forget_comp_cartesianCylinderForgetIso_hom (ε : Bool) :
    Functor.whiskerRight (cartesianCylinder.{u}.endpoint ε) MarkedPresheaf.forget ≫
        cartesianCylinderForgetIso.hom =
      Functor.whiskerLeft MarkedPresheaf.forget (joyalInterval.{u}.cylinder.endpoint ε) := by
  ext X : 2
  exact forget_map_cartesianEndpoint_app ε X

theorem cartesianCylinderForgetIso_hom_comp_whiskerLeft_contraction :
    cartesianCylinderForgetIso.hom ≫
        Functor.whiskerLeft MarkedPresheaf.forget joyalInterval.{u}.cylinder.contraction =
      Functor.whiskerRight cartesianCylinder.{u}.contraction MarkedPresheaf.forget := by
  ext X : 2
  exact CartesianMonoidalCategory.lift_snd _ _

inductive cartesianGenerators : MorphismProperty MarkedSSet.{u}
  | innerHorn {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
      cartesianGenerators ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, i].ι)
  | flatSharp :
      cartesianGenerators ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
        ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u}))
  | sharpHom :
      cartesianGenerators ((MarkedPresheaf.sharp edgeMarking).map
        (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge))

private abbrev GeneratorIndex : Type :=
  (Σ n : ℕ, {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)}) ⊕ Bool

private noncomputable def generatorArrow : GeneratorIndex → Arrow MarkedSSet.{u}
  | .inl ⟨n, p⟩ => Arrow.mk ((MarkedPresheaf.flat edgeMarking).map Λ[n + 2, p.1].ι)
  | .inr false => Arrow.mk ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
      ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u}))
  | .inr true => Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map
      (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge))

private theorem cartesianGenerators_eq_ofHoms :
    cartesianGenerators = MorphismProperty.ofHoms fun i => (generatorArrow i).hom := by
  ext X Y f
  constructor
  · rintro (⟨i, h0, hn⟩ | _ | _)
    · exact MorphismProperty.ofHoms.mk (f := fun i => (generatorArrow i).hom)
        (Sum.inl ⟨_, i, h0, hn⟩ : GeneratorIndex)
    · exact MorphismProperty.ofHoms.mk (f := fun i => (generatorArrow i).hom)
        (Sum.inr false : GeneratorIndex)
    · exact MorphismProperty.ofHoms.mk (f := fun i => (generatorArrow i).hom)
        (Sum.inr true : GeneratorIndex)
  · rintro ⟨(⟨n, i, h0, hn⟩ | _ | _)⟩
    · exact cartesianGenerators.innerHorn i h0 hn
    · exact cartesianGenerators.flatSharp
    · exact cartesianGenerators.sharpHom

instance isSmall_cartesianGenerators : cartesianGenerators.{u}.IsSmall.{w} := by
  rw [cartesianGenerators_eq_ofHoms]
  exact MorphismProperty.isSmall_ofHoms _

theorem cartesianGenerators_le_monomorphisms :
    cartesianGenerators ≤ monomorphisms MarkedSSet.{u} := by
  rintro _ _ _ (⟨i, h0, hn⟩ | _ | _)
  · exact (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono Λ[_ + 2, i].ι))
  · exact (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 SSet.coherentIso.{u})))
  · have := SSet.coherentIso.mono_hom_edge.{u}
    exact (MarkedPresheaf.mono_iff _).2
      (inferInstanceAs (Mono (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge :
        Δ[1] ⟶ SSet.coherentIso.{u})))

section Lifting

open SSet

private theorem joyalAnodyne_le_llp :
    joyalInterval.{u}.cylinder.anodyne innerHornInclusions ≤ quasicategoryIsofibrations.llp := by
  rintro A B f hf X Y p ⟨hX, hY, hp⟩
  let := SSet.modelCategoryJoyal.joyalModelCategory.{u}
  have h := (SSet.modelCategoryJoyal.fibration_iff_isofibration p).2 hp
  rw [HomotopicalAlgebra.fibration_iff] at h
  exact h f ⟨joyalInterval.{u}.cylinder.anodyne_le_monomorphisms _
    innerHornInclusions_le_monomorphisms f hf,
    joyalInterval.{u}.cylinder.anodyne_le_weakEquivalences _
      innerHornInclusions_le_monomorphisms f hf⟩

private theorem llp_joyalBothBox {A B : SSet.{u}} (h : A ⟶ B)
    (hh : quasicategoryIsofibrations.llp h) :
    quasicategoryIsofibrations.llp (joyalInterval.{u}.cylinder.bothBox h) := by
  rintro E B' p ⟨_, _, _⟩
  let sq₁₃ :=
    Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom joyalInterval.{u}.boundary p
  refine (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
    (joyalInterval.{u}.bothBoxPushoutObjObj h) sq₁₃).2
      (hh _ ⟨?_, quasicategory_pullbackObjObj_pt p _ sq₁₃, isofibration_pullbackObjObjπ p _ sq₁₃⟩)
  exact (inferInstance : ((ihom SSet.coherentIso.{u}).obj E).Quasicategory)

private def naturalIsofibrations : MorphismProperty MarkedSSet.{u} := fun X Y p =>
  SSet.Quasicategory X.underlying ∧
    (∀ e : X.underlying _⦋1⦌, e ∈ X.marked ⦋1⦌ ↔ Nonempty (Edge.mk' e).InvStruct) ∧
      SSet.Quasicategory Y.underlying ∧ Isofibration (MarkedPresheaf.forget.map p)

private theorem hasLiftingProperty_of_forget {A B X Y : MarkedSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (h : ∀ (u : A ⟶ X) (v : B ⟶ Y), u ≫ p = i ≫ v →
      ∃ l : MarkedPresheaf.forget.obj B ⟶ MarkedPresheaf.forget.obj X,
        MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map u ∧
          l ≫ MarkedPresheaf.forget.map p = MarkedPresheaf.forget.map v ∧
            ∀ e ∈ B.marked ⦋1⦌, l.app _ e ∈ X.marked ⦋1⦌) :
    HasLiftingProperty i p := by
  refine ⟨fun {u v} sq => ?_⟩
  obtain ⟨l, h₁, h₂, h₃⟩ := h u v sq.w
  exact ⟨⟨⟨edgeHomMk l h₃, MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₁),
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₂)⟩⟩⟩

private theorem llp_naturalIsofibrations_of_forget {A B : MarkedSSet.{u}} (g : A ⟶ B)
    (hg : quasicategoryIsofibrations.llp (MarkedPresheaf.forget.map g))
    (hm : ∀ (Z : SSet.{u}) (_ : Z.Quasicategory) (l : MarkedPresheaf.forget.obj B ⟶ Z),
      (∀ e ∈ A.marked ⦋1⦌,
        Nonempty (Edge.mk' (l.app _ ((MarkedPresheaf.forget.map g).app _ e))).InvStruct) →
      ∀ e ∈ B.marked ⦋1⦌, Nonempty (Edge.mk' (l.app _ e)).InvStruct) :
    naturalIsofibrations.llp g := by
  rintro X Y p ⟨hX, hXn, hY, hp⟩
  refine hasLiftingProperty_of_forget g p fun u v w => ?_
  have sq : CommSq (MarkedPresheaf.forget.map u) (MarkedPresheaf.forget.map g)
      (MarkedPresheaf.forget.map p) (MarkedPresheaf.forget.map v) :=
    ⟨by rw [← Functor.map_comp, w, Functor.map_comp]⟩
  obtain ⟨l⟩ := ((hg _ ⟨hX, hY, hp⟩).sq_hasLift sq).exists_lift
  refine ⟨l.l, l.fac_left, l.fac_right, fun e he => (hXn _).2 (hm _ hX l.l (fun e' he' => ?_) e he)⟩
  exact nonempty_invStruct_congr (ConcreteCategory.congr_hom (congr_app l.fac_left _) e').symm
    ((hXn _).1 (MarkedPresheaf.map_mem_marked u he'))

private theorem joyalEndpoint_app_apply (ε : Bool) (K : SSet.{u}) (b : K _⦋1⦌) :
    ((joyalInterval.{u}.cylinder.endpoint ε).app K).app _ b =
      ((coherentIso.σ 0 (cond ε coherentIso.x₁ coherentIso.x₀), b) :
        (coherentIso.{u} ⊗ K : SSet.{u}) _⦋1⦌) := by
  refine Prod.ext ?_ rfl
  change coherentIso.map (stdSimplex.objEquiv.{u} _).op _ =
    coherentIso.map (SimplexCategory.σ 0).op _
  exact congrArg
    (fun g : ⦋1⦌ ⟶ ⦋0⦌ => coherentIso.map g.op (cond ε coherentIso.x₁ coherentIso.x₀))
    (SimplexCategory.Hom.ext_one_left _ _ (Subsingleton.elim (α := Fin 1) _ _)
      (Subsingleton.elim (α := Fin 1) _ _))

private theorem nonempty_invStruct_of_mem_marked_cylinder {X : MarkedSSet.{u}} {Z : SSet.{u}}
    [Z.Quasicategory] (ε : Bool)
    (l : MarkedPresheaf.forget.obj (cartesianCylinder.{u}.I.obj X) ⟶ Z)
    (hl : ∀ b ∈ X.marked ⦋1⦌, Nonempty (Edge.mk' (l.app _
      ((MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint ε).app X)).app _ b))).InvStruct)
    (e : (MarkedPresheaf.forget.obj (cartesianCylinder.{u}.I.obj X)) _⦋1⦌)
    (he : e ∈ (cartesianCylinder.{u}.I.obj X).marked ⦋1⦌) :
    Nonempty (Edge.mk' (l.app _ e)).InvStruct := by
  let f : coherentIso.{u} ⊗ MarkedPresheaf.forget.obj X ⟶ Z := (forgetProdIso X).inv ≫ l
  have hf (x : (MarkedPresheaf.forget.obj (cartesianCylinder.{u}.I.obj X)) _⦋1⦌) :
      f.app _ ((forgetProdIso X).hom.app _ x) = l.app _ x :=
    congrArg (l.app _) (ConcreteCategory.congr_hom (congr_app (forgetProdIso X).hom_inv_id _) x)
  have hb : (MarkedPresheaf.forget.map prod.snd).app _ e ∈ X.marked ⦋1⦌ :=
    MarkedPresheaf.map_mem_marked (prod.snd : MarkedSSet.sharpJ ⨯ X ⟶ X) he
  have hε := hl _ hb
  rw [← hf] at hε
  have key := (ConcreteCategory.congr_hom (congr_app (forget_map_cartesianEndpoint_app ε X) _)
    ((MarkedPresheaf.forget.map prod.snd).app _ e)).trans (joyalEndpoint_app_apply ε _ _)
  have hε' := nonempty_invStruct_congr (congrArg (f.app _) key) hε
  exact nonempty_invStruct_congr (hf e)
    (nonempty_invStruct_app_prod f ε _ hε' ((MarkedPresheaf.forget.map prod.fst).app _ e))

private theorem isPushout_forget_map_endpointBoxSource (ε : Bool) {K Y : MarkedSSet.{u}}
    (i : K ⟶ Y) :
    IsPushout ((joyalInterval.{u}.cylinder.endpoint ε).app (MarkedPresheaf.forget.obj K))
      (MarkedPresheaf.forget.map i)
      (cartesianCylinderForgetIso.inv.app K ≫
        MarkedPresheaf.forget.map (pushout.inl ((cartesianCylinder.{u}.endpoint ε).app K) i))
      (MarkedPresheaf.forget.map (pushout.inr ((cartesianCylinder.{u}.endpoint ε).app K) i)) := by
  refine ((IsPushout.of_hasPushout ((cartesianCylinder.{u}.endpoint ε).app K) i).map
    MarkedPresheaf.forget).of_iso (Iso.refl _) (cartesianCylinderForgetIso.app K) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.app_hom, Iso.refl_hom, Category.id_comp]
    exact forget_map_cartesianEndpoint_app ε K
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      (Iso.hom_inv_id_app_assoc cartesianCylinderForgetIso K _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

private noncomputable def forgetEndpointBoxArrowIso (ε : Bool) {K Y : MarkedSSet.{u}} (i : K ⟶ Y) :
    Arrow.mk (MarkedPresheaf.forget.map (cartesianCylinder.{u}.endpointBox ε i)) ≅
      Arrow.mk (joyalInterval.{u}.cylinder.endpointBox ε (MarkedPresheaf.forget.map i)) :=
  Arrow.isoMk (isPushout_forget_map_endpointBoxSource ε i).isoPushout
    (cartesianCylinderForgetIso.app Y) (by
      dsimp only [ExactCylinder.endpointBox, ExactCylinder.endpointBoxSource, Arrow.mk_hom]
      refine (isPushout_forget_map_endpointBoxSource ε i).hom_ext ?_ ?_
      · rw [IsPushout.inl_isoPushout_hom_assoc]
        simp only [pushout.inl_desc, Category.assoc, ← Functor.map_comp_assoc]
        exact (NatIso.naturality_1 cartesianCylinderForgetIso i).symm
      · rw [IsPushout.inr_isoPushout_hom_assoc]
        simp only [pushout.inr_desc, ← Functor.map_comp_assoc]
        exact (forget_map_cartesianEndpoint_app ε Y).symm)

private theorem isPushout_forget_map_bothBoxSource {K Y : MarkedSSet.{u}} (i : K ⟶ Y) :
    IsPushout (joyalInterval.{u}.cylinder.endpoints (MarkedPresheaf.forget.obj K))
      (coprod.map (MarkedPresheaf.forget.map i) (MarkedPresheaf.forget.map i))
      (cartesianCylinderForgetIso.inv.app K ≫ MarkedPresheaf.forget.map
        (pushout.inl (cartesianCylinder.{u}.endpoints K) (coprod.map i i)))
      (coprodComparison MarkedPresheaf.forget Y Y ≫ MarkedPresheaf.forget.map
        (pushout.inr (cartesianCylinder.{u}.endpoints K) (coprod.map i i))) := by
  refine ((IsPushout.of_hasPushout (cartesianCylinder.{u}.endpoints K) (coprod.map i i)).map
    MarkedPresheaf.forget).of_iso (asIso (coprodComparison MarkedPresheaf.forget K K)).symm
    (cartesianCylinderForgetIso.app K) (asIso (coprodComparison MarkedPresheaf.forget Y Y)).symm
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, Iso.app_hom]
    exact coprodComparison_map_desc_comp MarkedPresheaf.forget _ _ _ _ _
      (forget_map_cartesianEndpoint_app false K) (forget_map_cartesianEndpoint_app true K)
  · rw [Iso.symm_hom, asIso_inv, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq, coprodComparison_natural]
  · exact (Category.comp_id _).trans
      (Iso.hom_inv_id_app_assoc cartesianCylinderForgetIso K _).symm
  · exact (Category.comp_id _).trans
      (Iso.inv_hom_id_assoc (asIso (coprodComparison MarkedPresheaf.forget Y Y)) _).symm

private noncomputable def forgetBothBoxArrowIso {K Y : MarkedSSet.{u}} (i : K ⟶ Y) :
    Arrow.mk (MarkedPresheaf.forget.map (cartesianCylinder.{u}.bothBox i)) ≅
      Arrow.mk (joyalInterval.{u}.cylinder.bothBox (MarkedPresheaf.forget.map i)) :=
  Arrow.isoMk (isPushout_forget_map_bothBoxSource i).isoPushout
    (cartesianCylinderForgetIso.app Y) (by
      dsimp only [ExactCylinder.bothBox, ExactCylinder.bothBoxSource, Arrow.mk_hom]
      refine (isPushout_forget_map_bothBoxSource i).hom_ext ?_ ?_
      · rw [IsPushout.inl_isoPushout_hom_assoc]
        simp only [pushout.inl_desc, Category.assoc, ← Functor.map_comp_assoc]
        exact (NatIso.naturality_1 cartesianCylinderForgetIso i).symm
      · rw [IsPushout.inr_isoPushout_hom_assoc]
        simp only [pushout.inr_desc, Category.assoc, ← Functor.map_comp_assoc]
        exact (coprodComparison_map_desc_comp MarkedPresheaf.forget _ _ _ _ _
          (forget_map_cartesianEndpoint_app false Y)
          (forget_map_cartesianEndpoint_app true Y)).symm)

private theorem nonempty_invStruct_of_section {A X : MarkedSSet.{u}}
    (g : A ⟶ cartesianCylinder.{u}.I.obj X) (ε : Bool) (s : X ⟶ A)
    (hs : s ≫ g = (cartesianCylinder.{u}.endpoint ε).app X) (Z : SSet.{u}) (hZ : Z.Quasicategory)
    (l : MarkedPresheaf.forget.obj (cartesianCylinder.{u}.I.obj X) ⟶ Z)
    (hl : ∀ e ∈ A.marked ⦋1⦌,
      Nonempty (Edge.mk' (l.app _ ((MarkedPresheaf.forget.map g).app _ e))).InvStruct)
    (e : (MarkedPresheaf.forget.obj (cartesianCylinder.{u}.I.obj X)) _⦋1⦌)
    (he : e ∈ (cartesianCylinder.{u}.I.obj X).marked ⦋1⦌) :
    Nonempty (Edge.mk' (l.app _ e)).InvStruct :=
  nonempty_invStruct_of_mem_marked_cylinder ε l (fun b hb => nonempty_invStruct_congr
    (congrArg (l.app _) (ConcreteCategory.congr_hom (congr_app
      ((MarkedPresheaf.forget.map_comp s g).symm.trans (congrArg MarkedPresheaf.forget.map hs))
        _) b))
    (hl _ (MarkedPresheaf.map_mem_marked s hb))) e he

theorem exists_eq_σ_of_mem_marked_flat {P : SSet.{u}} (e : P _⦋1⦌)
    (he : e ∈ ((MarkedPresheaf.flat edgeMarking).obj P).marked ⦋1⦌) : ∃ x, e = P.σ 0 x := by
  obtain ⟨⟨n⟩, p, ⟨-, hb⟩, y, rfl⟩ := (MarkedPresheaf.mem_marked_flat _ _ _ _).1 he
  change n = 0 at hb
  subst hb
  obtain rfl : p = SimplexCategory.σ 0 :=
    SimplexCategory.Hom.ext_one_left _ _ (Subsingleton.elim (α := Fin 1) _ _)
      (Subsingleton.elim (α := Fin 1) _ _)
  exact ⟨y, rfl⟩

private theorem llp_of_arrow_iso {A B A' B' : SSet.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk f') (h : quasicategoryIsofibrations.llp f') :
    quasicategoryIsofibrations.llp f :=
  fun _ _ p hp => (HasLiftingProperty.iff_of_arrow_iso_left e p).2 (h p hp)

private inductive cartesianAnodyneGenerators : MorphismProperty MarkedSSet.{u}
  | generator {A B : MarkedSSet.{u}} (g : A ⟶ B) (hg : cartesianGenerators g) :
      cartesianAnodyneGenerators g
  | endpointBox (ε : Bool) {K X : MarkedSSet.{u}} (i : K ⟶ X) (hi : Mono i) :
      cartesianAnodyneGenerators (cartesianCylinder.{u}.endpointBox ε i)
  | bothBox {K X : MarkedSSet.{u}} (i : K ⟶ X) (hi : cartesianAnodyneGenerators i) :
      cartesianAnodyneGenerators (cartesianCylinder.{u}.bothBox i)

private theorem llp_of_cartesianAnodyneGenerators {A B : MarkedSSet.{u}} (g : A ⟶ B)
    (hg : cartesianAnodyneGenerators g) :
    quasicategoryIsofibrations.llp
        (joyalInterval.{u}.cylinder.bothBox (MarkedPresheaf.forget.map g)) ∧
      naturalIsofibrations.llp g := by
  induction hg with
  | generator g hg =>
    cases hg with
    | innerHorn i h0 hn =>
      have h : quasicategoryIsofibrations.llp Λ[_ + 2, i].ι :=
        joyalAnodyne_le_llp _ (joyalInterval.{u}.cylinder.le_anodyne _ _
          (horn_ι_mem_innerHornInclusions h0 hn))
      refine ⟨llp_joyalBothBox _ h, llp_naturalIsofibrations_of_forget _ h ?_⟩
      intro Z _ l _ e he
      obtain ⟨x, rfl⟩ := exists_eq_σ_of_mem_marked_flat e he
      exact nonempty_invStruct_congr (σ_naturality_apply l 0 x).symm (nonempty_invStruct_σ _)
    | flatSharp =>
      have h : quasicategoryIsofibrations.llp (MarkedPresheaf.forget.map
          ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
            ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u}))) := by
        intro _ _ p _
        exact HasLiftingProperty.of_left_iso (𝟙 SSet.coherentIso.{u}) p
      refine ⟨llp_joyalBothBox _ h, llp_naturalIsofibrations_of_forget _ h ?_⟩
      intro Z _ l _ e _
      exact coherentIso.nonempty_invStruct_app (l : SSet.coherentIso.{u} ⟶ Z) e
    | sharpHom =>
      refine ⟨llp_bothBox_hom_edge, ?_⟩
      rintro X Y p ⟨hX, hXn, hY, hp⟩
      refine hasLiftingProperty_of_forget _ p fun u v w => ?_
      have sq : CommSq (MarkedPresheaf.forget.map u)
          (SSet.yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})
          (MarkedPresheaf.forget.map p) (MarkedPresheaf.forget.map v) :=
        ⟨by rw [← Functor.map_comp, w, Functor.map_comp]; rfl⟩
      have hu : Nonempty (Edge.mk' (SSet.yonedaEquiv (MarkedPresheaf.forget.map u))).InvStruct :=
        (hXn _).1 (MarkedPresheaf.map_mem_marked u
          ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl))
      have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) := hX
      have : SSet.Quasicategory (MarkedPresheaf.forget.obj Y) := hY
      obtain ⟨l⟩ := (hasLift_coherentIso_hom (MarkedPresheaf.forget.map p) sq hu).exists_lift
      exact ⟨l.l, l.fac_left, l.fac_right,
        fun e _ => (hXn _).2 (coherentIso.nonempty_invStruct_app l.l e)⟩
  | endpointBox ε i hi =>
    have hm : Mono (MarkedPresheaf.forget.map i) := (MarkedPresheaf.mono_iff i).1 hi
    have h : quasicategoryIsofibrations.llp
        (MarkedPresheaf.forget.map (cartesianCylinder.{u}.endpointBox ε i)) :=
      llp_of_arrow_iso (forgetEndpointBoxArrowIso ε i) (joyalAnodyne_le_llp _
        ((joyalInterval.{u}.cylinder.isAnodyneClass_anodyne _).endpointBox_mem ε _ hm))
    exact ⟨llp_joyalBothBox _ h, llp_naturalIsofibrations_of_forget _ h
      (nonempty_invStruct_of_section _ ε _ (cartesianCylinder.{u}.inr_endpointBox ε i))⟩
  | bothBox i hi ih =>
    have h : quasicategoryIsofibrations.llp
        (MarkedPresheaf.forget.map (cartesianCylinder.{u}.bothBox i)) :=
      llp_of_arrow_iso (forgetBothBoxArrowIso i) ih.1
    refine ⟨llp_joyalBothBox _ h, llp_naturalIsofibrations_of_forget _ h
      (nonempty_invStruct_of_section _ false (coprod.inl ≫ pushout.inr _ _) ?_)⟩
    rw [Category.assoc, cartesianCylinder.{u}.inr_bothBox, cartesianCylinder.{u}.inl_endpoints]

private theorem anodyne_le_llp_naturalIsofibrations :
    cartesianCylinder.{u}.anodyne cartesianGenerators ≤ naturalIsofibrations.llp := by
  refine (cartesianCylinder.{u}.anodyne_le _ (saturation.{u} cartesianAnodyneGenerators)
    ⟨inferInstance, fun _ _ g hg => le_saturation _ _ (.generator g hg),
      fun ε _ _ i hi => le_saturation _ _ (.endpointBox ε i hi), fun i _ hi => ?_⟩).trans
    (saturation_le _ _ fun _ _ g hg => (llp_of_cartesianAnodyneGenerators g hg).2)
  have := cartesianCylinder.{u}.isSaturated_bothBox_preimage
    (saturation.{u} cartesianAnodyneGenerators)
  exact saturation_le.{u} cartesianAnodyneGenerators
    (NatTrans.leibnizPreimage cartesianCylinder.{u}.endpointsNatTrans
      (saturation.{u} cartesianAnodyneGenerators))
    (fun _ _ g hg => le_saturation _ _ (.bothBox g hg)) i hi

private noncomputable def isTerminalForgetTerminal :
    IsTerminal (MarkedPresheaf.forget.obj (⊤_ MarkedSSet.{u})) :=
  terminalIsTerminal.isTerminalObj _ _

private theorem hasLiftingProperty_terminal_from_forget {X : MarkedSSet.{u}} {A B : SSet.{u}}
    (i : A ⟶ B) (h : HasLiftingProperty i (MarkedPresheaf.forget.map (terminal.from X))) :
    HasLiftingProperty i (terminal.from (MarkedPresheaf.forget.obj X)) :=
  HasLiftingProperty.of_arrow_iso_right i
    (Arrow.isoMk (f := Arrow.mk (MarkedPresheaf.forget.map (terminal.from X)))
      (g := Arrow.mk (terminal.from (MarkedPresheaf.forget.obj X))) (Iso.refl _)
      (isTerminalForgetTerminal.uniqueUpToIso (terminalIsTerminal (C := SSet.{u})))
      (terminal.hom_ext _ _))

theorem yonedaEquiv_symm_app_mem_marked {X : MarkedSSet.{u}} {e : X.underlying _⦋1⦌}
    (he : e ∈ X.marked ⦋1⦌) (e' : Δ[1] _⦋1⦌) :
    (yonedaEquiv.symm e : Δ[1] ⟶ X.underlying).app _ e' ∈ X.marked ⦋1⦌ := by
  change X.underlying.map (stdSimplex.objEquiv.{u} e').op e ∈ X.marked ⦋1⦌
  generalize stdSimplex.objEquiv.{u} e' = f
  by_cases h : f.toOrderHom 0 = f.toOrderHom 1
  · obtain ⟨c, p, q, hp, rfl⟩ := (edgeMarking_degenerate_iff f).2 h
    rw [op_comp, CategoryTheory.Functor.map_comp_apply]
    exact X.degenerate p hp _
  · have key : ∀ a c : Fin 2, a ≤ c → a ≠ c → a = 0 ∧ c = 1 := by decide
    obtain ⟨h₀, h₁⟩ := key _ _ (f.toOrderHom.monotone (Fin.zero_le 1)) h
    obtain rfl : f = 𝟙 _ := SimplexCategory.Hom.ext_one_left _ _ h₀ h₁
    rwa [op_id, CategoryTheory.Functor.map_id_apply]

private theorem yonedaEquiv_symm_app_stdSimplex_zero {P : SSet.{u}} (v : P _⦋0⦌)
    (e : Δ[0] _⦋1⦌) : (yonedaEquiv.symm v : Δ[0] ⟶ P).app _ e = P.σ 0 v := by
  change P.map (stdSimplex.objEquiv.{u} e).op v = P.map (SimplexCategory.σ 0).op v
  exact congrArg (fun g : ⦋1⦌ ⟶ ⦋0⦌ => P.map g.op v)
    (SimplexCategory.Hom.ext_one_left _ _ (Subsingleton.elim (α := Fin 1) _ _)
      (Subsingleton.elim (α := Fin 1) _ _))

private theorem joyalPoint_app_vertex (ε : Bool) (t : (⊤_ SSet.{u}) _⦋0⦌) :
    (joyalPoint.{u} ε).app _ t = cond ε coherentIso.x₁ coherentIso.x₀ := by
  apply coherentIso.simplexEquiv.injective
  funext i
  exact congrArg (coherentIso.simplexEquiv (cond ε coherentIso.x₁ coherentIso.x₀))
    (Subsingleton.elim (α := Fin 1) _ _)

end Lifting

namespace MarkedSSet.modelCategoryCartesian

noncomputable scoped instance cartesianModelCategory : ModelCategory MarkedSSet.{u} :=
  cartesianCylinder.modelCategoryOfEmbedding
    (BoundedEmbedding.separated (MarkedSite.topology edgeMarking)) cartesianGenerators
    cartesianGenerators_le_monomorphisms

theorem isFibrant_iff_isFibrant (X : MarkedSSet.{u}) :
    IsFibrant X ↔ cartesianCylinder.{u}.IsFibrant cartesianGenerators X :=
  (HomotopicalAlgebra.fibration_iff _).trans
    (cartesianCylinder.{u}.rlp_trivialCofibrations_terminal_from_iff _
      cartesianGenerators_le_monomorphisms X)

theorem isFibrant_iff (X : MarkedSSet.{u}) :
    IsFibrant X ↔ SSet.Quasicategory X.underlying ∧
      ∀ e : X.underlying _⦋1⦌, e ∈ X.marked ⦋1⦌ ↔ Nonempty (SSet.Edge.mk' e).InvStruct := by
  rw [isFibrant_iff_isFibrant]
  constructor
  · intro h
    have hq : SSet.Quasicategory X.underlying := by
      rw [SSet.quasicategory_iff_innerFibration]
      refine ⟨fun _ _ f hf => ?_⟩
      obtain ⟨i, h0, hn⟩ := hf
      exact hasLiftingProperty_terminal_from_forget _
        (((MarkedPresheaf.flatForgetAdjunction edgeMarking).hasLiftingProperty_iff _ _).1
          (h _ (cartesianCylinder.{u}.le_anodyne _ _ (cartesianGenerators.innerHorn i h0 hn))))
    refine ⟨hq, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
    · let u : (MarkedPresheaf.sharp edgeMarking).obj Δ[1] ⟶ X :=
        edgeHomMk (SSet.yonedaEquiv.symm e) fun e' _ => yonedaEquiv_symm_app_mem_marked he e'
      have sq : CommSq u ((MarkedPresheaf.sharp edgeMarking).map
          (SSet.yonedaEquiv.symm SSet.coherentIso.hom.edge)) (terminal.from X)
            (terminal.from _) := ⟨terminal.hom_ext _ _⟩
      have := h _ (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.sharpHom)
      have hl := congrArg SSet.yonedaEquiv (congrArg MarkedPresheaf.forget.map sq.fac_left)
      have h₁ : (MarkedPresheaf.forget.map sq.lift).app _ SSet.coherentIso.hom.edge = e :=
        (congrArg (fun x => (MarkedPresheaf.forget.map sq.lift).app _ x)
          (Equiv.apply_symm_apply SSet.yonedaEquiv _)).symm.trans
            ((SSet.yonedaEquiv_comp _ _).symm.trans (hl.trans (Equiv.apply_symm_apply _ _)))
      exact SSet.nonempty_invStruct_congr h₁
        (SSet.coherentIso.nonempty_invStruct_app (MarkedPresheaf.forget.map sq.lift) _)
    · obtain ⟨g, hg⟩ := SSet.exists_coherentIso_extension (SSet.Edge.mk' e) he.some
      let u : (MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u} ⟶ X :=
        ((MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv _ _).symm g
      have sq : CommSq u ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
          ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u})) (terminal.from X)
            (terminal.from _) := ⟨terminal.hom_ext _ _⟩
      have := h _ (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.flatSharp)
      have h₁ : (MarkedPresheaf.forget.map sq.lift).app _ SSet.coherentIso.hom.edge = e :=
        (ConcreteCategory.congr_hom
          (congr_app (congrArg MarkedPresheaf.forget.map sq.fac_left) _) _).trans hg
      exact h₁ ▸ MarkedPresheaf.map_mem_marked sq.lift
        ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  · rintro ⟨hq, hn⟩ _ _ f hf
    have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) := hq
    exact anodyne_le_llp_naturalIsofibrations f hf _ ⟨hq, hn,
      quasicategory_of_isTerminal isTerminalForgetTerminal,
      isofibration_of_isTerminal _ isTerminalForgetTerminal⟩

theorem isFibrant_natural (Z : SSet.{u}) [Z.Quasicategory] : IsFibrant (MarkedSSet.natural Z) :=
  (isFibrant_iff _).2
    ⟨inferInstanceAs Z.Quasicategory, fun e => MarkedSSet.mem_marked_ofEdges _ _ _ e⟩

theorem fibration_iff_isofibration {X Y : MarkedSSet.{u}} [IsFibrant X] [IsFibrant Y]
    (p : X ⟶ Y) : Fibration p ↔ SSet.Isofibration (MarkedPresheaf.forget.map p) := by
  obtain ⟨hXq, hXn⟩ := (isFibrant_iff X).1 inferInstance
  obtain ⟨hYq, hYn⟩ := (isFibrant_iff Y).1 inferInstance
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj X) := hXq
  have : SSet.Quasicategory (MarkedPresheaf.forget.obj Y) := hYq
  rw [HomotopicalAlgebra.fibration_iff]
  constructor
  · intro hp
    have hn : (cartesianCylinder.{u}.anodyne cartesianGenerators).rlp p := fun _ _ f hf =>
      hp f ⟨cartesianCylinder.{u}.anodyne_le_monomorphisms _ cartesianGenerators_le_monomorphisms
          f hf,
        cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms
          f hf⟩
    have hinner : SSet.InnerFibration (MarkedPresheaf.forget.map p) := ⟨fun _ _ f hf => by
      obtain ⟨i, h0, hi⟩ := hf
      exact ((MarkedPresheaf.flatForgetAdjunction edgeMarking).hasLiftingProperty_iff _ _).1
        (hn _ (cartesianCylinder.{u}.le_anodyne _ _ (cartesianGenerators.innerHorn i h0 hi)))⟩
    refine { toInnerFibration := hinner, exists_lift := fun x₀ y₁ g hg => ?_ }
    obtain ⟨G, hG⟩ := SSet.exists_coherentIso_extension g hg.some
    let Gm : MarkedSSet.sharpJ ⟶ Y :=
      edgeHomMk G fun e _ => (hYn _).2 (SSet.coherentIso.nonempty_invStruct_app G e)
    let T := (MarkedPresheaf.sharp edgeMarking).obj Δ[0]
    let x : T ⟶ X := edgeHomMk (SSet.yonedaEquiv.symm x₀) fun e _ =>
      (congrArg (· ∈ X.marked ⦋1⦌) (yonedaEquiv_symm_app_stdSimplex_zero x₀ e)).mpr
        (X.map_σ_mem_marked x₀)
    let k : MarkedSSet.sharpJ ⟶ MarkedSSet.sharpJ ⨯ T := prod.lift (𝟙 _)
      ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).homEquiv _ _
        (SSet.stdSimplex.isTerminalObj₀.from _))
    let pt : (MarkedPresheaf.forget.obj T) _⦋0⦌ := (SSet.yonedaEquiv (𝟙 Δ[0]) : Δ[0] _⦋0⦌)
    have hG₀ : G.app _ SSet.coherentIso.x₀ = (MarkedPresheaf.forget.map p).app _ x₀ :=
      calc G.app _ SSet.coherentIso.x₀ =
            G.app _ (SSet.coherentIso.δ 1 SSet.coherentIso.hom.edge) :=
            congrArg _ SSet.coherentIso.hom.src_eq.symm
        _ = _ := SSet.δ_naturality_apply G _ _
        _ = _ := (congrArg _ hG).trans g.src_eq
    have sq : CommSq x ((cartesianCylinder.{u}.endpoint false).app T) p (prod.fst ≫ Gm) := ⟨by
      refine MarkedPresheaf.hom_ext (SSet.yonedaEquiv.injective ?_)
      refine Eq.trans (?_ : _ = (MarkedPresheaf.forget.map p).app _ x₀) (hG₀.symm.trans ?_)
      · exact congrArg ((MarkedPresheaf.forget.map p).app _) (SSet.yonedaEquiv_symm_app_id x₀)
      · exact congrArg (G.app _) ((joyalPoint_app_vertex false
          ((MarkedPresheaf.forget.map (toSharpTerminal T)).app _ pt)).symm.trans
            (ConcreteCategory.congr_hom (congr_app (congrArg MarkedPresheaf.forget.map
              (prod.lift_fst (toSharpTerminal T ≫ sharpPoint false) (𝟙 T))) _) pt).symm)⟩
    obtain ⟨ℓ⟩ :=
      ((hn _ (cartesianCylinder.{u}.anodyne_endpoint _ false T)).sq_hasLift sq).exists_lift
    let F := MarkedPresheaf.forget.map (k ≫ ℓ.l)
    have hk : (MarkedPresheaf.forget.map k).app _ SSet.coherentIso.x₀ =
        (MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint false).app T)).app _ pt := by
      have e₁ : (MarkedPresheaf.forget.map (k ≫ prod.fst)).app _ SSet.coherentIso.x₀ =
          SSet.coherentIso.x₀ :=
        ConcreteCategory.congr_hom (congr_app (congrArg MarkedPresheaf.forget.map
          (prod.lift_fst _ _)) _) _
      have e₂ := congrArg (fun φ => (φ.app _ pt).1) (forget_map_cartesianEndpoint_app false T)
      have h₁ : (forgetProdIso T).hom.app _ ((MarkedPresheaf.forget.map k).app _
          SSet.coherentIso.x₀) = (forgetProdIso T).hom.app _
            ((MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint false).app T)).app _ pt) :=
        Prod.ext (e₁.trans ((joyalPoint_app_vertex false _).symm.trans e₂.symm))
          (SSet.stdSimplex.ext (n := 0) (d := 0) _ _ fun _ => Subsingleton.elim (α := Fin 1) _ _)
      exact (ConcreteCategory.congr_hom (congr_app (forgetProdIso T).hom_inv_id _) _).symm.trans
        ((congrArg ((forgetProdIso T).inv.app _) h₁).trans
          (ConcreteCategory.congr_hom (congr_app (forgetProdIso T).hom_inv_id _) _))
    have h₀ : F.app _ SSet.coherentIso.x₀ = x₀ :=
      calc F.app _ SSet.coherentIso.x₀ = (MarkedPresheaf.forget.map ℓ.l).app _
            ((MarkedPresheaf.forget.map k).app _ SSet.coherentIso.x₀) := rfl
        _ = (MarkedPresheaf.forget.map ℓ.l).app _
            ((MarkedPresheaf.forget.map ((cartesianCylinder.{u}.endpoint false).app T)).app _ pt) :=
          congrArg _ hk
        _ = (MarkedPresheaf.forget.map x).app _ pt :=
          ConcreteCategory.congr_hom (congr_app (congrArg MarkedPresheaf.forget.map ℓ.fac_left) _)
            pt
        _ = x₀ := SSet.yonedaEquiv_symm_app_id x₀
    have e₁ : k ≫ ℓ.l ≫ p = Gm :=
      (congrArg (k ≫ ·) ℓ.fac_right).trans ((prod.lift_fst_assoc _ _ _).trans (Category.id_comp _))
    have hpF : (MarkedPresheaf.forget.map p).app _ (F.app _ SSet.coherentIso.hom.edge) = g.edge :=
      (ConcreteCategory.congr_hom (congr_app (congrArg MarkedPresheaf.forget.map e₁) _) _).trans hG
    exact ⟨_, (SSet.coherentIso.hom.map F).ofEq h₀ rfl,
      ⟨SSet.coherentIso.invStructOfEqMapHom (g := F) rfl⟩, hpF⟩
  · intro hp
    exact cartesianCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne _
      cartesianGenerators_le_monomorphisms p
      (fun _ _ f hf => anodyne_le_llp_naturalIsofibrations f hf p ⟨hXq, hXn, hYq, hp⟩)
      ((isFibrant_iff_isFibrant Y).1 inferInstance)

theorem weakEquivalence_flatSharp_of_kanComplex (K : SSet.{u}) [K.KanComplex] :
    WeakEquivalence ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
      ((MarkedPresheaf.flat edgeMarking).obj K)) := by
  rw [weakEquivalence_iff]
  suffices h : trivialCofibrations MarkedSSet.{u}
      ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
        ((MarkedPresheaf.flat edgeMarking).obj K)) from h.2
  rw [← fibrations_llp]
  intro A B q hq
  have hJ : HasLiftingProperty ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
      ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u})) q :=
    hq _ ⟨cartesianCylinder.{u}.anodyne_le_monomorphisms _ cartesianGenerators_le_monomorphisms _
      (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.flatSharp),
      cartesianCylinder.{u}.anodyne_le_weakEquivalences _ cartesianGenerators_le_monomorphisms _
        (cartesianCylinder.{u}.le_anodyne _ _ cartesianGenerators.flatSharp)⟩
  refine ⟨fun {u v} sq => ?_⟩
  have hm : ∀ e ∈ ((MarkedPresheaf.sharp edgeMarking).obj K).marked ⦋1⦌,
      (MarkedPresheaf.forget.map u).app _ e ∈ A.marked ⦋1⦌ := by
    intro e _
    obtain ⟨G, hG⟩ := SSet.exists_coherentIso_extension (X := K) (SSet.Edge.mk' (e : K _⦋1⦌))
      (SSet.nonempty_invStruct_of_kanComplex K e).some
    have sq' : CommSq ((MarkedPresheaf.flat edgeMarking).map G ≫ u)
        ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
          ((MarkedPresheaf.flat edgeMarking).obj SSet.coherentIso.{u})) q
        ((MarkedPresheaf.sharp edgeMarking).map G ≫ v) :=
      ⟨MarkedPresheaf.hom_ext (congrArg (G ≫ ·) (congrArg MarkedPresheaf.forget.map sq.w))⟩
    have h₁ : (MarkedPresheaf.forget.map sq'.lift).app _ SSet.coherentIso.hom.edge =
        (MarkedPresheaf.forget.map u).app _ e :=
      (ConcreteCategory.congr_hom
        (congr_app (congrArg MarkedPresheaf.forget.map sq'.fac_left) _) _).trans
          (congrArg ((MarkedPresheaf.forget.map u).app _) hG)
    exact h₁ ▸ MarkedPresheaf.map_mem_marked sq'.lift
      ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  refine ⟨⟨⟨edgeHomMk (MarkedPresheaf.forget.map u) hm, MarkedPresheaf.hom_ext rfl,
    MarkedPresheaf.hom_ext ?_⟩⟩⟩
  rw [Functor.map_comp]
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg MarkedPresheaf.forget.map sq.w).trans (Functor.map_comp _ _ _))

end MarkedSSet.modelCategoryCartesian

end Atoms.Homotopical
