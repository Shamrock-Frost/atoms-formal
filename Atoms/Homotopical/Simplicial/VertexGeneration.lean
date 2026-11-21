import Atoms.Homotopical.Simplicial.KanDatum
import Atoms.Homotopical.Simplicial.Cells
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory HomotopicalAlgebra

universe u v

namespace Atoms.Homotopical

open SSet

section Vertex

variable (C : MorphismProperty SSet.{u}) [C.IsStableUnderCobaseChange]

theorem hom_mem_of_vertex (h₀ : C (𝟙 (Δ[0] : SSet.{u}))) {X Y : SSet.{u}} (e : X ≅ Y)
    (x : Δ[0] ⟶ X) : C e.hom :=
  C.of_isPushout (IsPushout.of_vert_isIso (f := x) (inr := x ≫ e.hom) ⟨by simp⟩) h₀

variable [C.IsStableUnderComposition]

variable (hvert : ∀ (m : ℕ) (x : Δ[0] ⟶ Δ[m]), C x)

include hvert in
theorem vertex_mem_of_iso {d : ℕ} {Y : SSet.{u}} (e : Δ[d] ≅ Y) (y : Δ[0] ⟶ Y) : C y := by
  rw [show y = (y ≫ e.inv) ≫ e.hom by simp]
  exact C.comp_mem _ _ (hvert _ _) (hom_mem_of_vertex C (hvert 0 _) e (y ≫ e.inv))

def vertexZero (d : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[d] :=
  stdSimplex.map (SimplexCategory.const _ _ 0)

variable (hcancel : ∀ ⦃X Y Z : SSet.{u}⦄ (f : X ⟶ Y) (g : Y ⟶ Z), Mono g → C f → C (f ≫ g) → C g)

include hvert hcancel in
theorem mono_mem_of_iso {a b : ℕ} {Y Z : SSet.{u}} (e : Δ[a] ≅ Y) (e' : Δ[b] ≅ Z) (g : Y ⟶ Z)
    [Mono g] : C g :=
  hcancel (vertexZero a ≫ e.hom) g inferInstance (vertex_mem_of_iso C hvert e _)
    (vertex_mem_of_iso C hvert e' _)

include hvert hcancel in
theorem vertex_prismUnion_zero_mem (m : ℕ) (y : Δ[0] ⟶ (prismUnion m 0).toSSet) :
    C (y ≫ (prismUnion m 0).ι) := by
  have key : ∀ k ≤ m, C (y ≫ Subcomplex.homOfLE (prismUnion_mono (Nat.zero_le k))) := by
    intro k hk
    induction k with
    | zero =>
      exact vertex_mem_of_iso C hvert
        (chainFaceIso _ ≪≫ Subcomplex.eqToIso prismUnion_zero.symm) _
    | succ k ih =>
      rw [← Subcomplex.homOfLE_comp (prismUnion_mono (Nat.zero_le k))
        (prismUnion_mono (Nat.le_succ k)), ← Category.assoc]
      refine C.comp_mem _ _ (ih (by omega)) ?_
      exact C.of_isPushout (prismUnion_bicartSq k (by omega)).isPushout
        (mono_mem_of_iso C hvert hcancel (chainFaceIso _) (chainFaceIso _) _)
  have hι : C (prismUnion m m).ι := hom_mem_of_vertex C (hvert 0 _)
    (Subcomplex.eqToIso prismUnion_self ≪≫ Subcomplex.topIso _)
    (y ≫ Subcomplex.homOfLE (prismUnion_mono (Nat.zero_le m)))
  rw [← Subcomplex.homOfLE_ι (prismUnion_mono (Nat.zero_le m)), ← Category.assoc]
  exact C.comp_mem _ _ (key m le_rfl) hι

include hvert hcancel in
theorem endpoint_mem_of_vertex_of_cancel (ε : Bool) (m : ℕ) :
    C ((simplicialCylinder.{u}.endpoint ε).app Δ[m]) := by
  let f := vertexZero m ≫ (simplicialCylinder.{u}.endpoint ε).app Δ[m]
  have hle : Subcomplex.range f ≤ prismUnion m 0 := by
    rintro U _ ⟨z, rfl⟩ i _
    change ((stdSimplex.objEquiv ((vertexZero m).app U z)).toOrderHom i : ℕ) ≤ 0
    exact le_rfl
  have hf := vertex_prismUnion_zero_mem C hvert hcancel m (Subcomplex.lift f hle)
  exact hcancel _ _ (simplicialCylinder.{u}.mono_endpoint ε _) (hvert _ _) hf

end Vertex

section Anodyne

variable (C : MorphismProperty SSet.{u}) [IsSaturated.{u} C]
  (hcancel : ∀ ⦃X Y Z : SSet.{u}⦄ (u : X ⟶ Y) (w : Y ⟶ Z), Mono w → C u → C (u ≫ w) → C w)

include hcancel in
theorem leibnizBox_endpoint_mem (ε : Bool) {K X : SSet.{u}} (i : K ⟶ X) [Mono i]
    (hK : C ((simplicialCylinder.{u}.endpoint ε).app K))
    (hX : C ((simplicialCylinder.{u}.endpoint ε).app X)) :
    C (NatTrans.leibnizBox (simplicialCylinder.{u}.endpoint ε) i) := by
  have sq := IsPushout.of_hasPushout ((simplicialCylinder.{u}.endpoint ε).app K) ((𝟭 _).map i)
  have hinr := C.of_isPushout sq.flip hK
  have : Mono (pushout.inr ((simplicialCylinder.{u}.endpoint ε).app K) ((𝟭 _).map i)) :=
    (MorphismProperty.monomorphisms _).of_isPushout sq.flip
      (simplicialCylinder.{u}.mono_endpoint ε K)
  refine hcancel _ _ (simplicialCylinder.{u}.mono_endpointBox ε i inferInstance) hinr ?_
  rw [NatTrans.inr_leibnizBox]
  exact hX

include hcancel in
theorem endpoint_mem_of_stdSimplex (ε : Bool)
    (hΔ : ∀ m : ℕ, C ((simplicialCylinder.{u}.endpoint ε).app Δ[m])) (X : SSet.{u}) :
    C ((simplicialCylinder.{u}.endpoint ε).app X) := by
  let E := simplicialCylinder.{u}.endpoint ε
  have hisoC : ∀ {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f], C f := fun f _ ↦
    isomorphisms_le_of_containsIdentities _ _ (isomorphisms.infer_property f)
  have hiso : ∀ {X Y : SSet.{u}} (_ : X ≅ Y), C (E.app X) → C (E.app Y) := by
    intro X Y e h
    have h' : e.hom ≫ E.app Y = E.app X ≫ simplicialCylinder.{u}.I.map e.hom := E.naturality e.hom
    have : E.app Y = e.inv ≫ E.app X ≫ simplicialCylinder.{u}.I.map e.hom := by
      rw [← h', Iso.inv_hom_id_assoc]
    rw [this]
    exact C.comp_mem _ _ (hisoC _) (C.comp_mem _ _ h (hisoC _))
  have hpush : ∀ {X₀ X₁ X₂ X : SSet.{u}} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X}
      {g₂ : X₂ ⟶ X}, IsPushout f₁ f₂ g₁ g₂ → Mono f₁ → C (E.app X₀) → C (E.app X₁) →
        C (E.app X₂) → C (E.app X) := by
    intro X₀ X₁ X₂ X f₁ f₂ g₁ g₂ sq hf₁ h₀ h₁ h₂
    have hbox := leibnizBox_endpoint_mem C hcancel ε f₁ h₀ h₁
    have hbox' : C (NatTrans.leibnizBox E g₂) :=
      C.of_isPushout (NatTrans.isPushout_leibnizBox E sq.flip) hbox
    have hinr := C.of_isPushout (IsPushout.of_hasPushout (E.app X₂) ((𝟭 _).map g₂)).flip h₂
    rw [← NatTrans.inr_leibnizBox E g₂]
    exact C.comp_mem _ _ hinr hbox'
  have hbotI : IsInitial (simplicialCylinder.{u}.I.obj (⊥_ SSet.{u})) :=
    IsInitial.isInitialObj _ _ initialIsInitial
  have : IsIso (E.app (⊥_ SSet.{u})) :=
    ⟨⟨hbotI.to _, initial.hom_ext _ _, hbotI.hom_ext _ _⟩⟩
  have hbot : C (E.app (⊥_ SSet.{u})) := hisoC _
  have hL : MorphismProperty.monomorphisms SSet.{u} ≤ NatTrans.leibnizPreimage E C := by
    have := simplicialCylinder.{u}.isSaturated_endpointBox_preimage ε C
    rw [← saturation_I_eq_monomorphisms]
    refine saturation_le _ _ ?_
    rintro _ _ _ ⟨n⟩
    exact leibnizBox_endpoint_mem C hcancel ε _
      (prop_boundary (fun X ↦ C (E.app X)) hiso hpush hbot hΔ n) (hΔ n)
  have hX : C (NatTrans.leibnizBox E (initial.to X)) := hL _ (monomorphisms.infer_property _)
  have : IsIso (pushout.inr (E.app (⊥_ SSet.{u})) ((𝟭 _).map (initial.to X))) :=
    (IsPushout.of_hasPushout (E.app (⊥_ SSet.{u})) ((𝟭 _).map (initial.to X))).isIso_inr_of_isIso
  rw [← NatTrans.inr_leibnizBox E (initial.to X)]
  exact C.comp_mem _ _ (hisoC _) hX

end Anodyne

theorem anodyneExtensions_le_of_vertex (C : MorphismProperty SSet.{u}) [IsSaturated.{u} C]
    (hcancel : ∀ ⦃X Y Z : SSet.{u}⦄ (f : X ⟶ Y) (g : Y ⟶ Z), Mono f → Mono g → C f →
      C (f ≫ g) → C g)
    (hvert : ∀ (m : ℕ) (x : Δ[0] ⟶ Δ[m]), C x) : SSet.anodyneExtensions.{u} ≤ C := by
  let C' := MorphismProperty.monomorphisms SSet.{u} ⊓ C
  have : IsSaturated.{u} C' := inferInstance
  have hC' : C' ≤ MorphismProperty.monomorphisms SSet.{u} := inf_le_left
  have hcancel' : ∀ ⦃X Y Z : SSet.{u}⦄ (u : X ⟶ Y) (w : Y ⟶ Z), Mono w → C' u → C' (u ≫ w) →
      C' w := fun _ _ _ u w hw hu huw ↦ ⟨hw, hcancel u w hu.1 hw hu.2 huw.2⟩
  have hvert' : ∀ (m : ℕ) (x : Δ[0] ⟶ Δ[m]), C' x := fun m x ↦
    ⟨IsTerminal.mono_from stdSimplex.isTerminalObj₀ x, hvert m x⟩
  have hend : ∀ (ε : Bool) (X : SSet.{u}), C' ((simplicialCylinder.{u}.endpoint ε).app X) :=
    fun ε ↦ endpoint_mem_of_stdSimplex C' hcancel' ε
      (endpoint_mem_of_vertex_of_cancel C' hvert' hcancel' ε)
  have hgen := simplicialCylinder.{u}.anodyneGenerators_le_of_endpoint_mem ⊥ C' hC' hcancel' hend
    bot_le
  rw [← anodyne_bot_eq_anodyneExtensions,
    simplicialCylinder.{u}.anodyne_eq_saturation_anodyneGenerators ⊥ bot_le]
  exact (saturation_le _ _ hgen).trans inf_le_right

theorem kanWeak_le_of_terminal_from (C : MorphismProperty SSet.{u})
    [C.HasTwoOutOfThreeProperty]
    [IsSaturated.{u} (MorphismProperty.monomorphisms SSet.{u} ⊓ C)]
    (h : ∀ m : ℕ, C (terminal.from Δ[m])) : kanWeak ≤ C := by
  have hisoC : ∀ {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f], C f := fun f _ ↦
    (isomorphisms_le_of_containsIdentities (MorphismProperty.monomorphisms SSet.{u} ⊓ C) _
      (isomorphisms.infer_property f)).2
  have hanod : SSet.anodyneExtensions.{u} ≤ C := by
    refine (anodyneExtensions_le_of_vertex (MorphismProperty.monomorphisms SSet.{u} ⊓ C)
      (fun _ _ _ f g _ hg hf hfg ↦ ⟨hg, C.of_precomp f g hf.2 hfg.2⟩) ?_).trans inf_le_right
    intro m x
    refine ⟨IsTerminal.mono_from stdSimplex.isTerminalObj₀ x,
      C.of_postcomp x (terminal.from Δ[m]) (h m) ?_⟩
    rw [terminal.comp_from]
    exact h 0
  intro X Y f hf
  obtain ⟨Y', j, hj, hY'⟩ := simplicialCylinder.{u}.exists_anodyne_isFibrant ⊥ bot_le Y
  have := simplicialCylinder.{u}.hasFunctorialFactorization_anodyne ⊥ bot_le
  let F := MorphismProperty.factorizationData (simplicialCylinder.{u}.anodyne ⊥)
    (simplicialCylinder.{u}.anodyne ⊥).rlp (f ≫ j)
  have hA : simplicialCylinder.{u}.anodyne ⊥ ≤ SSet.anodyneExtensions.{u} :=
    anodyne_bot_eq_anodyneExtensions.le
  have hi := hA _ F.hi
  replace hj := hA _ hj
  have hpW : kanWeak F.p := by
    have h₁ : kanWeak (f ≫ j) := kanWeak.comp_mem _ _ hf (anodyneExtensions_le_kanWeak _ hj)
    rw [← F.fac] at h₁
    exact kanWeak.of_precomp _ _ (anodyneExtensions_le_kanWeak _ hi) h₁
  have hp := (simplicialCylinder.{u}.weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne ⊥ F.p
    F.hp hY').1 hpW
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms F.p hp
  have hZ := simplicialCylinder.{u}.isFibrant_of_rlp_anodyne ⊥ F.p F.hp hY'
  have hsW : kanWeak s := kanWeak.of_postcomp s F.p hpW (by
    rw [hs]
    exact IsALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
  have hsA := (simplicialCylinder.{u}.anodyne_iff_weakEquivalences_of_isFibrant ⊥ bot_le s
    (SplitMono.mono ⟨F.p, hs⟩) hZ).2 hsW
  have hpC : C F.p := C.of_precomp s F.p (hanod _ (hA _ hsA)) (by
    rw [hs]
    exact hisoC _)
  have hfj : C (f ≫ j) := by
    rw [← F.fac]
    exact C.comp_mem _ _ (hanod _ hi) hpC
  exact C.of_postcomp f j (hanod _ hj) hfj

section Nerve

variable (C : Type u) [SmallCategory C] [HasTerminal C]

noncomputable def toTerminal : 𝟭 C ⟶ (Functor.const C).obj (⊤_ C) where
  app c := terminal.from c
  naturality _ _ _ := terminal.hom_ext _ _

noncomputable def contractToTerminal : Fin (1 + 1) × C ⥤ C :=
  Functor.uncurry.obj (ComposableArrows.mk₁ (toTerminal C))

noncomputable def nerveContraction : (Δ[1] ⊗ nerve C : SSet.{u}) ⟶ nerve C where
  app _ := TypeCat.ofHom fun x ↦
    ((stdSimplex.objEquiv x.1).toOrderHom.monotone.functor.prod' x.2) ⋙ contractToTerminal C
  naturality _ _ _ := rfl

noncomputable def nerveTerminal : ⊤_ SSet.{u} ⟶ nerve C where
  app _ := TypeCat.ofHom fun _ ↦ (Functor.const _).obj (⊤_ C)
  naturality _ _ _ := rfl

theorem prod_const_zero_comp_contractToTerminal {n : ℕ} (x : ComposableArrows C n) :
    (monotone_const (β := Fin (1 + 1)) (c := 0) (α := Fin (n + 1))).functor.prod' x ⋙
      contractToTerminal C = x := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j g ↦ ?_)
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((ComposableArrows.mk₁ (toTerminal C)).map (homOfLE (le_refl (0 : Fin (1 + 1))))).app
    (x.obj i) ≫ (𝟭 C).map (x.map g) = x.map g
  rw [Subsingleton.elim (homOfLE _) (𝟙 _), CategoryTheory.Functor.map_id, NatTrans.id_app]
  exact Category.id_comp _

theorem endpoint_false_nerveContraction :
    (simplicialCylinder.{u}.endpoint false).app (nerve C) ≫ nerveContraction C = 𝟙 _ := by
  ext U x
  exact prod_const_zero_comp_contractToTerminal C x

theorem endpoint_true_nerveContraction :
    (simplicialCylinder.{u}.endpoint true).app (nerve C) ≫ nerveContraction C =
      terminal.from (nerve C) ≫ nerveTerminal C := by
  ext U x
  refine CategoryTheory.Functor.ext (fun i ↦ rfl) (fun i j g ↦ ?_)
  exact terminal.hom_ext _ _

end Nerve

theorem terminal_from_nerve_mem_kanWeak (C : Type u) [SmallCategory C] [HasTerminal C] :
    kanWeak (terminal.from (nerve C)) := by
  have hfg : simplicialCylinder.{u}.Homotopic (terminal.from (nerve C) ≫ nerveTerminal C) (𝟙 _) :=
    Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨nerveContraction C,
      endpoint_false_nerveContraction C, endpoint_true_nerveContraction C⟩)
  have hgf :
      simplicialCylinder.{u}.Homotopic (nerveTerminal C ≫ terminal.from (nerve C)) (𝟙 _) := by
    rw [terminal.hom_ext (nerveTerminal C ≫ terminal.from (nerve C)) (𝟙 _)]
    exact Relation.EqvGen.refl _
  exact simplicialCylinder.{u}.weakEquivalences_of_homotopic ⊥ _ _ hfg hgf

theorem terminal_from_stdSimplex_mem_kanWeak (m : ℕ) : kanWeak (terminal.from Δ[m]) := by
  rw [show terminal.from Δ[m] = (stdSimplex.isoNerve m).hom ≫ terminal.from _ from
    terminal.hom_ext _ _]
  exact kanWeak.comp_mem _ _ (IsALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
    (terminal_from_nerve_mem_kanWeak _)

theorem terminal_from_yoneda_mem_kanWeak (a : SimplexCategory) :
    kanWeak.{0} (terminal.from (yoneda.obj a)) := by
  rw [show terminal.from (yoneda.obj a) =
      ((uliftYonedaIsoYoneda.{0} (C := SimplexCategory)).app a).inv ≫ terminal.from Δ[a.len] from
    terminal.hom_ext _ _]
  exact kanWeak.comp_mem _ _ (IsALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
    (terminal_from_stdSimplex_mem_kanWeak a.len)

theorem kanWeak_eq_generatedALocalizer_terminal_from :
    kanWeak = generatedALocalizer
      (MorphismProperty.ofHoms fun m : ℕ ↦ terminal.from (Δ[m] : SSet.{u})) := by
  refine le_antisymm ?_ (generatedALocalizer_le ?_)
  · exact kanWeak_le_of_terminal_from _ fun m ↦ le_generatedALocalizer _ _ ⟨m⟩
  · rintro _ _ _ ⟨m⟩
    exact terminal_from_stdSimplex_mem_kanWeak m

theorem kanWeak_le_inverseImage {A : Type v} [SmallCategory A]
    (F : SSet.{u} ⥤ Aᵒᵖ ⥤ Type (max u v))
    [PreservesColimitsOfSize.{u, u} F]
    (hF : ∀ ⦃X Y : SSet.{u}⦄ (f : X ⟶ Y), Mono f → Mono (F.map f))
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max u v))} [hV : IsALocalizer V]
    (h : ∀ m : ℕ, V (F.map (terminal.from Δ[m]))) : kanWeak ≤ V.inverseImage F := by
  have hQ := hV.isSaturated_monomorphisms_inf
  have : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  have : IsStableUnderTransfiniteComposition.{u}
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max u v)) ⊓ V) :=
    IsStableUnderTransfiniteComposition.shrink.{u, max u v} _
  have : IsSaturated.{u} (MorphismProperty.monomorphisms SSet.{u} ⊓ V.inverseImage F) :=
    { isStableUnderCobaseChange := ⟨fun sq hf ↦
        ⟨(MorphismProperty.monomorphisms _).of_isPushout sq hf.1,
          (hQ.isStableUnderCobaseChange.of_isPushout (sq.map F) ⟨hF _ hf.1, hf.2⟩).2⟩⟩
      isStableUnderRetracts :=
        ⟨fun r hg ↦ ⟨(MorphismProperty.monomorphisms _).of_retract r hg.1,
          V.of_retract (r.map F) hg.2⟩⟩
      isStableUnderTransfiniteComposition := ⟨fun J _ _ _ _ ↦ ⟨fun X Y f ⟨hf⟩ ↦ by
        have : PreservesWellOrderContinuousOfShape J F := ⟨fun _ _ ↦ inferInstance⟩
        refine ⟨(MorphismProperty.monomorphisms _).transfiniteCompositionsOfShape_le J f
          (hf.ofLE inf_le_left).mem, ?_⟩
        have hf' := hf.ofLE
          (W' := (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max u v)) ⊓ V).inverseImage F)
          (fun _ _ g hg ↦ ⟨hF g hg.1, hg.2⟩)
        exact ((MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max u v)) ⊓
          V).transfiniteCompositionsOfShape_le J _ hf'.map.mem).2⟩⟩ }
  exact kanWeak_le_of_terminal_from _ h

end Atoms.Homotopical
