import Atoms.Homotopical.Simplicial.MarkedRightFibration

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open MonoidalCategory CartesianMonoidalCategory MonoidalCategory.Arrow

universe u

namespace Atoms.Homotopical

open MarkedPresheaf (forget)

def markedRightAnodyne : MorphismProperty MarkedSSet.{u} :=
  saturation.{u} markedRightGenerators

theorem markedRightAnodyne_eq_llp : markedRightAnodyne.{u} = markedRightFibrations.llp :=
  saturation_eq_llp_rlp _

theorem markedRightAnodyne_flatSharp (K : SSet.{u}) [K.KanComplex] :
    markedRightAnodyne (MarkedSSet.flatSharp K) := by
  rw [markedRightAnodyne_eq_llp]
  exact markedRightFibrations_llp_flatSharp K

section PushoutProduct

open SSet

instance isSaturated_markedRightAnodyne : IsSaturated.{u} markedRightAnodyne.{u} :=
  isSaturated_saturation _

private theorem const_app_edge {K Y : SSet.{u}} (y : Y _⦋0⦌) (x : K _⦋1⦌) :
    (SSet.const (X := K) y).app _ x = Y.σ 0 y :=
  congrArg (fun g : ⦋1⦌ ⟶ ⦋0⦌ => Y.map g.op y) (Subsingleton.elim _ _)

private theorem app_mem_marked_of_stdSimplex_zero {Y : MarkedSSet.{u}}
    (v : Δ[0] ⟶ forget.obj Y)
    (e : (Δ[0] : SSet.{u}) _⦋1⦌) : v.app _ e ∈ Y.marked ⦋1⦌ := by
  rw [show e = Δ[0].σ 0 (Δ[0].δ 0 e) from
    yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _)]
  exact (σ_naturality_apply v (0 : Fin 1) _).symm ▸ MarkedSSet.map_σ_mem_marked _ _

private theorem hasLiftingProperty_of_forget {S T X Y : MarkedSSet.{u}} (j : S ⟶ T)
    (p : X ⟶ Y)
    (h : ∀ (a : S ⟶ X) (b : T ⟶ Y), a ≫ p = j ≫ b → ∃ l : forget.obj T ⟶ forget.obj X,
      forget.map j ≫ l = forget.map a ∧ l ≫ forget.map p = forget.map b ∧
        ∀ e ∈ T.marked ⦋1⦌, l.app _ e ∈ X.marked ⦋1⦌) :
    HasLiftingProperty j p :=
  ⟨fun {a b} sq => by
    obtain ⟨l, h₁, h₂, h₃⟩ := h a b sq.w
    exact ⟨⟨⟨edgeHomMk l h₃, MarkedPresheaf.hom_ext ((forget.map_comp _ _).trans h₁),
      MarkedPresheaf.hom_ext ((forget.map_comp _ _).trans h₂)⟩⟩⟩⟩

private theorem app_mem_marked_of_fac {Z S T X : MarkedSSet.{u}} (j : S ⟶ T) (a : S ⟶ X)
    (l : forget.obj T ⟶ forget.obj X) (hl : forget.map j ≫ l = forget.map a) (k : Z ⟶ S)
    {x : Z.underlying _⦋1⦌} (hx : x ∈ Z.marked ⦋1⦌) :
    l.app _ ((forget.map (k ≫ j)).app _ x) ∈ X.marked ⦋1⦌ := by
  have e : forget.map (k ≫ j) ≫ l = forget.map (k ≫ a) := by
    rw [forget.map_comp, Category.assoc, hl, ← forget.map_comp]
  have := MarkedPresheaf.map_mem_marked (k ≫ a) hx
  rw [← e] at this
  exact this

private theorem mem_marked_of_hasLiftingProperty_endpointMarking {X Y : MarkedSSet.{u}}
    (p : X ⟶ Y) (h : HasLiftingProperty
      (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])) □
        Arrow.mk (MarkedSSet.flatSharp Δ[1])).hom p) (ψ : Δ[1] ⊗ Δ[1] ⟶ forget.obj X)
    (h₁ : ∀ e ∈ ((MarkedPresheaf.sharp edgeMarking).obj (Δ[1] : SSet.{u}) ⊗
      (MarkedPresheaf.flat edgeMarking).obj (Δ[1] : SSet.{u})).marked ⦋1⦌,
        ψ.app _ e ∈ X.marked ⦋1⦌)
    (h₂ : ∀ e : (Δ[0] ⊗ Δ[1] : SSet.{u}) _⦋1⦌,
      (stdSimplex.δ 0 ▷ Δ[1] ≫ ψ).app _ e ∈ X.marked ⦋1⦌)
    (h₃ : ∀ e : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋1⦌,
      (ψ ≫ forget.map p).app _ e ∈ Y.marked ⦋1⦌)
    (e : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋1⦌) : ψ.app _ e ∈ X.marked ⦋1⦌ := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]))
    (MarkedSSet.flatSharp Δ[1])
  let a : sq.pt ⟶ X := sq.isPushout.desc (edgeHomMk ψ h₁)
    (edgeHomMk (stdSimplex.δ 0 ▷ Δ[1] ≫ ψ) fun e _ => h₂ e) (MarkedPresheaf.hom_ext rfl)
  have csq : CommSq a sq.ι p (edgeHomMk (Y := Y) (ψ ≫ forget.map p) fun e _ => h₃ e) :=
    ⟨sq.isPushout.hom_ext
      (by
        rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc]
        exact MarkedPresheaf.hom_ext rfl)
      (by
        rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc]
        exact MarkedPresheaf.hom_ext rfl)⟩
  obtain ⟨l⟩ := (h.sq_hasLift csq).exists_lift
  have hl : forget.map l.l = ψ := congrArg forget.map ((sq.inl_ι_assoc l.l).symm.trans
    ((congrArg _ l.fac_left).trans (sq.isPushout.inl_desc _ _ _)))
  have hm := MarkedPresheaf.map_mem_marked l.l (x := e)
    ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
      (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl⟩)
  exact hl ▸ hm

private theorem markedRightAnodyne_pushoutProduct_innerHorn {n : ℕ} (i : Fin (n + 3))
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) {K L : MarkedSSet.{u}} (g : K ⟶ L) [Mono g] :
    markedRightAnodyne (Arrow.mk ((MarkedPresheaf.flat.{u} edgeMarking).map Λ[n + 2, i].ι) □
      Arrow.mk g).hom := by
  rw [markedRightAnodyne_eq_llp]
  intro X Y p hp
  have := ((markedRightFibrations_iff p).1 hp).1
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.flat.{u} edgeMarking).map Λ[n + 2, i].ι) g
  let sq' : (curriedTensor SSet.{u}).PushoutObjObj Λ[n + 2, i].ι (forget.map g) :=
    { pt := forget.obj sq.pt
      inl := forget.map sq.inl
      inr := forget.map sq.inr
      isPushout := sq.isPushout.map forget
      ι := forget.map sq.ι
      inl_ι := (forget.map_comp _ _).symm.trans (congrArg forget.map sq.inl_ι)
      inr_ι := (forget.map_comp _ _).symm.trans (congrArg forget.map sq.inr_ι) }
  have : Mono (forget.map g) := (MarkedPresheaf.mono_iff _).1 inferInstance
  have hA : innerAnodyneExtensions sq'.ι :=
    innerAnodyneExtensions_pushoutObjObjι' sq' fun _ _ q hq ↦ hq _ (.intro i h0 hn)
  refine hasLiftingProperty_of_forget sq.ι p fun a b w => ?_
  have w' : CommSq (forget.map a) sq'.ι (forget.map p) (forget.map b) :=
    ⟨(forget.map_comp _ _).symm.trans ((congrArg forget.map w).trans (forget.map_comp _ _))⟩
  obtain ⟨l⟩ := ((hA _ ((innerFibration_iff (forget.map p)).1 inferInstance)).sq_hasLift
    w').exists_lift
  refine ⟨l.l, l.fac_left, l.fac_right, fun e he => ?_⟩
  obtain ⟨he₁, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ he₁
  let v' : (Λ[n + 2, i] : SSet.{u}) _⦋0⦌ := ⟨v, by simp⟩
  have := app_mem_marked_of_fac sq.ι a l.l l.fac_left sq.inr
    (x := ((Λ[n + 2, i] : SSet.{u}).σ 0 v', e.2))
    ((MarkedSSet.mem_marked_tensor_iff _ _ _).2 ⟨MarkedSSet.map_σ_mem_marked _ _, he₂⟩)
  rw [sq.inr_ι] at this
  rw [show e = ((Δ[n + 2] : SSet.{u}).σ 0 v, e.2) from Prod.ext hv rfl]
  exact this

private theorem markedRightAnodyne_pushoutProduct_flatSharp {K L : MarkedSSet.{u}}
    (g : K ⟶ L) :
    markedRightAnodyne (Arrow.mk (MarkedSSet.flatSharp coherentIso.{u}) □ Arrow.mk g).hom := by
  rw [markedRightAnodyne_eq_llp]
  intro X Y p hp
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    (MarkedSSet.flatSharp coherentIso.{u}) g
  have : IsIso (forget.map sq.ι) := isIso_forget_map_pushoutProduct _ g
    (Or.inl (inferInstanceAs (IsIso (𝟙 coherentIso.{u}))))
  refine hasLiftingProperty_of_forget sq.ι p fun a b w => ?_
  let l := inv (forget.map sq.ι) ≫ forget.map a
  have hl : forget.map sq.ι ≫ l = forget.map a := IsIso.hom_inv_id_assoc _ _
  have hlp : l ≫ forget.map p = forget.map b := by
    rw [Category.assoc, ← forget.map_comp, w, forget.map_comp, IsIso.inv_hom_id_assoc]
  refine ⟨l, hl, hlp, fun e he => ?_⟩
  obtain ⟨-, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  have hJ (y : L.underlying _⦋0⦌) (e₁ : coherentIso.{u} _⦋1⦌) :
      l.app _ (e₁, SimplicialObject.σ (L.underlying : SSet.{u}) 0 y) ∈ X.marked ⦋1⦌ := by
    let G : coherentIso.{u} ⟶
        forget.obj ((MarkedPresheaf.sharp edgeMarking).obj coherentIso.{u} ⊗ L) :=
      lift (𝟙 _) (SSet.const y)
    have hc : (G ≫ l) ≫ forget.map p = G ≫ forget.map b := by
      rw [Category.assoc, hlp]
    refine MarkedSSet.mem_marked_of_eq
      (congrArg (fun z => l.app _ (e₁, z)) (const_app_edge y e₁).symm)
      ((hasLiftingProperty_flatSharp_iff p coherentIso).1 (hp _ markedRightGenerators.flatSharp)
        (G ≫ l) (fun e' => MarkedSSet.mem_marked_of_eq
          (congrArg (fun φ : coherentIso.{u} ⟶ forget.obj Y => φ.app _ e') hc)
          (MarkedPresheaf.map_mem_marked b ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
            ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, MarkedSSet.mem_marked_of_eq
              (const_app_edge y e') (MarkedSSet.map_σ_mem_marked L y)⟩))) e₁)
  obtain ⟨e₁, e₂⟩ := e
  let T : Δ[1] ⊗ Δ[1] ⟶
      forget.obj ((MarkedPresheaf.sharp edgeMarking).obj coherentIso.{u} ⊗ L) :=
    (SSet.yonedaEquiv.symm e₁ : Δ[1] ⟶ coherentIso.{u}) ⊗ₘ
      (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L)
  have hψ : (T ≫ l) ≫ forget.map p = T ≫ forget.map b :=
    (Category.assoc _ _ _).trans (congrArg _ hlp)
  refine MarkedSSet.mem_marked_of_eq (congrArg (l.app _) (Prod.ext
    (yonedaEquiv_symm_app_id (X := coherentIso.{u}) e₁).symm
    (yonedaEquiv_symm_app_id (X := forget.obj L) e₂).symm))
      (mem_marked_of_hasLiftingProperty_endpointMarking p
        (hp _ markedRightGenerators.endpointMarking) (T ≫ l) (fun e' he' => ?_) (fun e' => ?_)
        (fun e' => ?_) (yonedaEquiv (𝟙 _), yonedaEquiv (𝟙 _)))
  · obtain ⟨-, h⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e').1 he'
    obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ h
    have hx : T.app _ e' = (((SSet.yonedaEquiv.symm e₁ : Δ[1] ⟶ coherentIso.{u}).app _ e'.1,
        SimplicialObject.σ (L.underlying : SSet.{u}) 0
          ((SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L).app _ v)) :
            (forget.obj ((MarkedPresheaf.sharp edgeMarking).obj coherentIso.{u} ⊗ L)) _⦋1⦌) :=
      Prod.ext rfl ((congrArg _ hv).trans
        (σ_naturality_apply (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L) 0 v))
    exact MarkedSSet.mem_marked_of_eq (congrArg (l.app _) hx) (hJ _ _)
  · let x : ((MarkedPresheaf.flat edgeMarking).obj coherentIso.{u} ⊗ L).underlying _⦋1⦌ :=
      ((stdSimplex.δ 0 ≫ (SSet.yonedaEquiv.symm e₁ : Δ[1] ⟶ coherentIso.{u})).app _ e'.1,
        (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L).app _ e'.2)
    have hx : x ∈ ((MarkedPresheaf.flat edgeMarking).obj coherentIso.{u} ⊗ L).marked ⦋1⦌ :=
      (MarkedSSet.mem_marked_tensor_iff _ _ x).2
        ⟨app_mem_marked_of_stdSimplex_zero (Y := (MarkedPresheaf.flat edgeMarking).obj _) _ _,
          yonedaEquiv_symm_app_mem_marked he₂ _⟩
    have := app_mem_marked_of_fac sq.ι a l hl sq.inr hx
    rw [sq.inr_ι] at this
    exact this
  · exact MarkedSSet.mem_marked_of_eq
      (congrArg (fun φ : Δ[1] ⊗ Δ[1] ⟶ forget.obj Y => φ.app _ e') hψ)
      (MarkedPresheaf.map_mem_marked b (x := T.app _ e')
        ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
        ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, yonedaEquiv_symm_app_mem_marked he₂ _⟩))

private theorem markedRightAnodyne_pushoutProduct_sharp_δ_zero_of_isIso
    {K L : MarkedSSet.{u}} (g : K ⟶ L) [IsIso (forget.map g)] :
    markedRightAnodyne (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map
      (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) □ Arrow.mk g).hom := by
  rw [markedRightAnodyne_eq_llp]
  intro X Y p hp
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor MarkedSSet.{u})
    ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) g
  have : IsIso (forget.map sq.ι) := isIso_forget_map_pushoutProduct _ g (Or.inr inferInstance)
  refine hasLiftingProperty_of_forget sq.ι p fun a b w => ?_
  let l := inv (forget.map sq.ι) ≫ forget.map a
  have hl : forget.map sq.ι ≫ l = forget.map a := IsIso.hom_inv_id_assoc _ _
  have hlp : l ≫ forget.map p = forget.map b := by
    rw [Category.assoc, ← forget.map_comp, w, forget.map_comp, IsIso.inv_hom_id_assoc]
  refine ⟨l, hl, hlp, fun e he => ?_⟩
  obtain ⟨-, he₂⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e).1 he
  obtain ⟨e₁, e₂⟩ := e
  let T : Δ[1] ⊗ Δ[1] ⟶ forget.obj ((MarkedPresheaf.sharp edgeMarking).obj
      (Δ[1] : SSet.{u}) ⊗ L) :=
    𝟙 (Δ[1] : SSet.{u}) ⊗ₘ (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L)
  have hψ : (T ≫ l) ≫ forget.map p = T ≫ forget.map b :=
    (Category.assoc _ _ _).trans (congrArg _ hlp)
  refine MarkedSSet.mem_marked_of_eq (y := (T ≫ l).app _ (e₁, yonedaEquiv (𝟙 _)))
    (congrArg (l.app _) (Prod.ext rfl (yonedaEquiv_symm_app_id (X := forget.obj L) e₂).symm))
      (mem_marked_of_hasLiftingProperty_endpointMarking p
        (hp _ markedRightGenerators.endpointMarking) (T ≫ l) (fun e' he' => ?_) (fun e' => ?_)
        (fun e' => ?_) (e₁, yonedaEquiv (𝟙 _)))
  · obtain ⟨-, h⟩ := (MarkedSSet.mem_marked_tensor_iff _ _ e').1 he'
    obtain ⟨v, hv⟩ := exists_eq_σ_of_mem_marked_flat _ h
    let y := (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L).app _ v
    let x : ((MarkedPresheaf.sharp edgeMarking).obj (Δ[1] : SSet.{u}) ⊗ K).underlying _⦋1⦌ :=
      (e'.1, SimplicialObject.σ (K.underlying : SSet.{u}) 0 ((inv (forget.map g)).app _ y))
    have hx :
        x ∈ ((MarkedPresheaf.sharp edgeMarking).obj (Δ[1] : SSet.{u}) ⊗ K).marked ⦋1⦌ :=
      (MarkedSSet.mem_marked_tensor_iff _ _ x).2
        ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, MarkedSSet.map_σ_mem_marked _ _⟩
    have := app_mem_marked_of_fac sq.ι a l hl sq.inl hx
    rw [sq.inl_ι] at this
    have h₁ : (forget.map g).app _ ((inv (forget.map g)).app _ y) = y :=
      ConcreteCategory.congr_hom (congr_app (IsIso.inv_hom_id (forget.map g)) _) y
    have h₂ : (forget.map g).app _ x.2 =
        (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L).app _ e'.2 :=
      (σ_naturality_apply (forget.map g) 0 _).trans ((congrArg _ h₁).trans
        ((σ_naturality_apply (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L) 0 v).symm.trans
          (congrArg _ hv.symm)))
    refine MarkedSSet.mem_marked_of_eq ?_ this
    exact congrArg (l.app _) (Prod.ext rfl h₂.symm)
  · let x : ((MarkedPresheaf.sharp edgeMarking).obj (Δ[0] : SSet.{u}) ⊗ L).underlying _⦋1⦌ :=
      (e'.1, (SSet.yonedaEquiv.symm e₂ : Δ[1] ⟶ forget.obj L).app _ e'.2)
    have hx :
        x ∈ ((MarkedPresheaf.sharp edgeMarking).obj (Δ[0] : SSet.{u}) ⊗ L).marked ⦋1⦌ :=
      (MarkedSSet.mem_marked_tensor_iff _ _ x).2 ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl,
        yonedaEquiv_symm_app_mem_marked he₂ _⟩
    have := app_mem_marked_of_fac sq.ι a l hl sq.inr hx
    rw [sq.inr_ι] at this
    exact this
  · exact MarkedSSet.mem_marked_of_eq
      (congrArg (fun φ : Δ[1] ⊗ Δ[1] ⟶ forget.obj Y => φ.app _ e') hψ)
      (MarkedPresheaf.map_mem_marked b (x := T.app _ e')
        ((MarkedSSet.mem_marked_tensor_iff _ _ _).2
        ⟨(MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl, yonedaEquiv_symm_app_mem_marked he₂ _⟩))

private theorem markedRightAnodyne_pushoutProduct_sharp_δ_zero {K L : MarkedSSet.{u}}
    (m : K ⟶ L) [Mono m] :
    markedRightAnodyne (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map
      (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))) □ Arrow.mk m).hom := by
  let e := (MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ (Δ[1] : SSet.{u}))
  let α := (tensoringLeft MarkedSSet.{u}).map e
  have hiso {K' L' : MarkedSSet.{u}} (j : K' ⟶ L') :
      Arrow.mk (NatTrans.leibnizBox α j) ≅ (Arrow.mk e □ Arrow.mk j) :=
    NatTrans.leibnizBoxArrowIso α e (Iso.refl _) (Iso.refl _) (fun _ => by simp [α]) j
  have : IsSaturated.{u} (NatTrans.leibnizPreimage α markedRightAnodyne.{u}) :=
    NatTrans.isSaturated_leibnizPreimage α _
  have hG : functorImage (MarkedPresheaf.flat.{u} edgeMarking) SSet.modelCategoryQuillen.I ⊔
      MarkedPresheaf.markingMaps.{u} edgeMarking ≤
        NatTrans.leibnizPreimage α markedRightAnodyne := by
    rintro _ _ g (⟨K, L, t, ⟨n⟩, h⟩ | ⟨a, h⟩)
    · refine (MorphismProperty.arrow_mk_iso_iff _ (hiso _)).2
        ((MorphismProperty.arrow_mk_iso_iff _
          ((pushoutProduct.obj (Arrow.mk e)).mapIso (eqToIso h))).1 ?_)
      exact le_saturation _ _ (markedRightGenerators.endpointBoundary n)
    · exact (MorphismProperty.arrow_mk_iso_iff _ (hiso _)).2
        (markedRightAnodyne_pushoutProduct_sharp_δ_zero_of_isIso _)
  have h := saturation_le _ _ hG
  rw [MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps edgeMarking
    saturation_I_eq_monomorphisms] at h
  exact (MorphismProperty.arrow_mk_iso_iff _ (hiso _)).1 (h _ (monomorphisms.infer_property m))

theorem markedRightAnodyne_pushoutProduct {A B K L : MarkedSSet.{u}} (f : A ⟶ B)
    (hf : markedRightAnodyne f) (g : K ⟶ L) [Mono g] :
    markedRightAnodyne (Arrow.mk f □ Arrow.mk g).hom := by
  let P : MorphismProperty MarkedSSet.{u} := ⨅ g : {g : Arrow MarkedSSet.{u} // Mono g.hom},
    NatTrans.leibnizPreimage ((curriedTensor MarkedSSet.{u}).map g.1.hom) markedRightAnodyne
  have hP {A' B' : MarkedSSet.{u}} (f' : A' ⟶ B') : P f' ↔
      ∀ g : Arrow MarkedSSet.{u}, Mono g.hom → markedRightAnodyne (Arrow.mk f' □ g).hom :=
    (MorphismProperty.iInf_iff _ _).trans
      ⟨fun h g hg => (NatTrans.leibnizPreimage_curriedTensor_map_iff _ _ f').1 (h ⟨g, hg⟩),
        fun h g => (NatTrans.leibnizPreimage_curriedTensor_map_iff _ _ f').2 (h g.1 g.2)⟩
  have : IsSaturated.{u} P := isSaturated_sInf _ (by
    rintro _ ⟨g, rfl⟩
    exact NatTrans.isSaturated_leibnizPreimage_curriedTensor_map g.1.hom _)
  have hgen : markedRightGenerators ≤ P := by
    intro X Y s hs
    refine (hP s).2 fun g hg => ?_
    rcases hs with ⟨i, h0, hn⟩ | _ | _ | n
    · exact markedRightAnodyne_pushoutProduct_innerHorn i h0 hn g.hom
    · exact markedRightAnodyne_pushoutProduct_flatSharp g.hom
    · have : Mono (Arrow.mk (MarkedSSet.flatSharp Δ[1]) □ g).hom :=
        Arrow.mono_pushoutProduct _ _
      exact (markedRightAnodyne.arrow_mk_iso_iff (PushoutProduct.associator
        (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])))
        (Arrow.mk (MarkedSSet.flatSharp Δ[1])) g)).2
          (markedRightAnodyne_pushoutProduct_sharp_δ_zero
            (Arrow.mk (MarkedSSet.flatSharp Δ[1]) □ g).hom)
    · have : Mono ((MarkedPresheaf.flat edgeMarking).map
          (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι) :=
        (MarkedPresheaf.mono_iff _).2
          (inferInstanceAs (Mono (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι))
      have : Mono (Arrow.mk ((MarkedPresheaf.flat edgeMarking).map ∂Δ[n].ι) □ g).hom :=
        Arrow.mono_pushoutProduct _ _
      exact (markedRightAnodyne.arrow_mk_iso_iff (PushoutProduct.associator
        (Arrow.mk ((MarkedPresheaf.sharp edgeMarking).map (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])))
        (Arrow.mk ((MarkedPresheaf.flat edgeMarking).map ∂Δ[n].ι)) g)).2
          (markedRightAnodyne_pushoutProduct_sharp_δ_zero
            (Arrow.mk ((MarkedPresheaf.flat edgeMarking).map ∂Δ[n].ι) □ g).hom)
  exact (hP f).1 (saturation_le _ _ hgen f hf) (Arrow.mk g) (inferInstance : Mono g)

end PushoutProduct

end Atoms.Homotopical
