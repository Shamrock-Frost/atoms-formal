import Atoms.Homotopical.Simplicial.MarkedRightAnodyne

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial
open MonoidalCategory CartesianMonoidalCategory MonoidalCategory.Arrow

universe u

namespace Atoms.Homotopical

open MarkedPresheaf (forget)

open SSet MarkedSSet.modelCategoryCartesian

private theorem stdSimplex_two_edge_of_notMem_horn {i : Fin 3} (e : (Δ[2] : SSet.{u}) _⦋1⦌)
    (he : e ∉ (horn.{u} 2 i).obj (op ⦋1⦌)) :
    e = SSet.yonedaEquiv (stdSimplex.δ i) := by
  rw [mem_horn_iff_notMem_range] at he
  push Not at he
  have hm : e 0 ≤ e 1 := stdSimplex.monotone_apply e (by decide)
  have key : ∀ j : Fin 3, j ≠ i → j = e 0 ∨ j = e 1 := fun j hj => by
    obtain ⟨t, ht⟩ := he j hj
    fin_cases t
    exacts [Or.inl ht.symm, Or.inr ht.symm]
  have hm' : (e 0 : ℕ) ≤ e 1 := hm
  have k (j : Fin 3) (hj : j ≠ i) : (j : ℕ) = e 0 ∨ (j : ℕ) = e 1 :=
    (key j hj).imp (congrArg Fin.val) (congrArg Fin.val)
  have h₀ := (e 0).isLt
  have h₁ := (e 1).isLt
  refine stdSimplex.ext _ _ (Fin.forall_fin_two.2 ⟨Fin.ext ?_, Fin.ext ?_⟩) <;>
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals
    have k₀ := k 0; have k₁ := k 1; have k₂ := k 2
    simp (config := { decide := true }) only [Fin.isValue, Fin.val_zero, Fin.val_one,
      Fin.val_two, forall_const, IsEmpty.forall_iff] at k₀ k₁ k₂
    first
      | (change (e _ : ℕ) = 0; omega)
      | (change (e _ : ℕ) = 1; omega)
      | (change (e _ : ℕ) = 2; omega)

section MarkedCore

variable {Y B : MarkedSSet.{u}} (q : Y ⟶ B)

private theorem mem_marked_δ_comp_of_horn {i j : Fin 3} (hj : j ≠ i)
    (a : (Λ[2, i] : SSet.{u}) ⟶ forget.obj Y) (l : Δ[2] ⟶ forget.obj Y)
    (hl : Λ[2, i].ι ≫ l = a) (ha : ∀ e, a.app (op ⦋1⦌) e ∈ Y.marked ⦋1⦌) :
    SSet.yonedaEquiv (stdSimplex.δ j ≫ l) ∈ Y.marked ⦋1⦌ := by
  have h : stdSimplex.δ j ≫ l = horn.ι i j hj ≫ a := by
    rw [← hl, ← Category.assoc, horn.ι_ι]
  rw [h, SSet.yonedaEquiv_comp]
  exact ha _

private theorem exists_lift_rightHorn (hq : markedRightFibrations q) {n : ℕ} (i : Fin (n + 2))
    (h0 : 0 < i) (a : (Λ[n + 1, i] : SSet.{u}) ⟶ forget.obj Y) (b : Δ[n + 1] ⟶ forget.obj B)
    (w : a ≫ forget.map q = Λ[n + 1, i].ι ≫ b)
    (ha : ∀ e, a.app (op ⦋1⦌) e ∈ Y.marked ⦋1⦌) (hb : ∀ e, b.app (op ⦋1⦌) e ∈ B.marked ⦋1⦌) :
    ∃ l : Δ[n + 1] ⟶ forget.obj Y, Λ[n + 1, i].ι ≫ l = a ∧ l ≫ forget.map q = b ∧
      ∀ e, l.app (op ⦋1⦌) e ∈ Y.marked ⦋1⦌ := by
  obtain ⟨h₁, h₂, h₃⟩ := (markedRightFibrations_iff q).1 hq
  obtain _ | m := n
  · obtain rfl : i = 1 := (by decide : ∀ i : Fin 2, 0 < i → i = 1) i h0
    have h10 : (0 : Fin 2) ≠ 1 := by decide
    have hδ : stdSimplex.δ 0 ≫ b = (horn.ι 1 0 h10 ≫ a) ≫ forget.map q := by
      rw [Category.assoc, w, ← Category.assoc, horn.ι_ι]
    obtain ⟨f', hf', hy, hp⟩ := h₂ (SSet.yonedaEquiv (horn.ι 1 0 h10 ≫ a))
      (SSet.yonedaEquiv b) (hb _)
      ((stdSimplex.yonedaEquiv_δ_comp b 0).symm.trans (congrArg SSet.yonedaEquiv hδ))
    refine ⟨SSet.yonedaEquiv.symm f', horn.hom_ext' fun j hj => ?_, ?_,
      yonedaEquiv_symm_app_mem_marked hf'⟩
    · obtain rfl : j = 0 := by omega
      rw [← Category.assoc, horn.ι_ι]
      exact (stdSimplex.δ_comp_yonedaEquiv_symm (X := forget.obj Y) f' 0).trans
        ((congrArg SSet.yonedaEquiv.symm hy).trans (Equiv.symm_apply_apply _ _))
    · exact (yonedaEquiv_symm_comp f' _).trans
        ((congrArg SSet.yonedaEquiv.symm hp).trans (Equiv.symm_apply_apply _ _))
  · obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Δ[m + 2] ⟶ forget.obj Y,
        Λ[m + 2, i].ι ≫ l = a ∧ l ≫ forget.map q = b := by
      by_cases hi : i = Fin.last (m + 2)
      · subst hi
        have hc := ((h₃ _).1 (ha (horn.edge (m + 2) (Fin.last (m + 2)) (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2)) (Fin.le_last _) (by simp)))).2
        obtain ⟨l⟩ := ((isCartesianEdge_iff_hasLift_horn _ _).1 hc m a b ⟨w⟩
          (Equiv.apply_symm_apply _ _).symm).exists_lift
        exact ⟨l.l, l.fac_left, l.fac_right⟩
      · obtain ⟨l⟩ := ((h₁.mem _ (horn_ι_mem_innerHornInclusions h0
          (lt_of_le_of_ne (Fin.le_last i) hi))).sq_hasLift ⟨w⟩).exists_lift
        exact ⟨l.l, l.fac_left, l.fac_right⟩
    refine ⟨l, hl₁, hl₂, fun e => ?_⟩
    by_cases he : e ∈ (horn.{u} (m + 2) i).obj (op ⦋1⦌)
    · exact (congrArg (fun φ => φ.app (op ⦋1⦌) ⟨e, he⟩) hl₁) ▸ ha ⟨e, he⟩
    obtain _ | k := m
    swap
    · exact absurd (horn_obj_eq_univ i 1 ▸ Set.mem_univ e) he
    rw [stdSimplex_two_edge_of_notMem_horn e he, ← SSet.yonedaEquiv_comp]
    have hσ (e' : (Δ[2] : SSet.{u}) _⦋1⦌) : (l ≫ forget.map q).app _ e' ∈ B.marked ⦋1⦌ :=
      hl₂ ▸ hb e'
    obtain rfl | rfl := (by decide : ∀ i : Fin 3, 0 < i → i = 1 ∨ i = 2) i h0
    · exact mem_marked_δ_one_of_hasLiftingProperty q
        (hq _ markedRightGenerators.endpointMarking) l
        (mem_marked_δ_comp_of_horn (by decide) a l hl₁ ha)
        (mem_marked_δ_comp_of_horn (by decide) a l hl₁ ha) hσ
    · have hcart (j : Fin 3) (hj : j ≠ 2) : IsCartesianEdge (forget.map q) (stdSimplex.δ j ≫ l) :=
        (congrArg (IsCartesianEdge (forget.map q)) (Equiv.symm_apply_apply _ _)).mp
          ((h₃ _).1 (mem_marked_δ_comp_of_horn hj a l hl₁ ha)).2
      have := h₁
      exact mem_marked_of_isLocallyCartesianEdge q h₂ h₃
        ((isLocallyCartesianEdge_of_simplex q l (hcart 0 (by decide))).2 (hcart 1 (by decide)))
        (hσ _)

variable (Y) in
def MarkedSSet.markedCore : SSet.Subcomplex (forget.obj Y) where
  obj n := {x | ∀ f : ⦋1⦌ ⟶ n.unop, (forget.obj Y).map f.op x ∈ Y.marked ⦋1⦌}
  map g x hx f := by
    have := hx (f ≫ g.unop)
    rwa [op_comp, Functor.map_comp_apply] at this

private theorem mem_marked_of_mem_markedCore {x : Y.underlying _⦋1⦌}
    (hx : x ∈ (MarkedSSet.markedCore Y).obj (op ⦋1⦌)) : x ∈ Y.marked ⦋1⦌ := by
  exact (congrArg (· ∈ Y.marked ⦋1⦌) ((forget.obj Y).map_id_apply (op ⦋1⦌) x)).mp (hx (𝟙 _))

private theorem range_le_markedCore {K : SSet.{u}} (φ : K ⟶ forget.obj Y)
    (hφ : ∀ e, φ.app (op ⦋1⦌) e ∈ Y.marked ⦋1⦌) :
    Subcomplex.range φ ≤ MarkedSSet.markedCore Y := by
  rintro n _ ⟨x, rfl⟩ f
  rw [← NatTrans.naturality_apply]
  exact hφ _

private theorem app_ι_mem_marked {K : SSet.{u}} (φ : K ⟶ MarkedSSet.markedCore Y)
    (e : K _⦋1⦌) : (φ ≫ (MarkedSSet.markedCore Y).ι).app (op ⦋1⦌) e ∈ Y.marked ⦋1⦌ :=
  mem_marked_of_mem_markedCore (φ.app _ e).2

private def markedCoreMap : (MarkedSSet.markedCore Y : SSet.{u}) ⟶ MarkedSSet.markedCore B :=
  Subcomplex.lift ((MarkedSSet.markedCore Y).ι ≫ forget.map q) (range_le_markedCore _ fun e =>
    MarkedPresheaf.map_mem_marked q (mem_marked_of_mem_markedCore e.2))

private theorem markedCoreMap_ι :
    markedCoreMap q ≫ (MarkedSSet.markedCore B).ι = (MarkedSSet.markedCore Y).ι ≫ forget.map q :=
  Subcomplex.lift_ι _ _

private theorem rightFibrations_markedCoreMap (hq : markedRightFibrations q) :
    SSet.rightFibrations (markedCoreMap q) := by
  rintro X₀ Y₀ _ ⟨i, h0⟩
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_lift_rightHorn q hq i h0 (a ≫ (MarkedSSet.markedCore _).ι)
    (b ≫ (MarkedSSet.markedCore _).ι)
    (by rw [Category.assoc, ← markedCoreMap_ι, ← Category.assoc, sq.w, Category.assoc])
    (app_ι_mem_marked a) (app_ι_mem_marked b)
  exact ⟨⟨⟨Subcomplex.lift l (range_le_markedCore l h₃),
    (cancel_mono (MarkedSSet.markedCore _).ι).1 h₁,
    (cancel_mono (MarkedSSet.markedCore _).ι).1 (by
      rw [Category.assoc, markedCoreMap_ι, ← Category.assoc, Subcomplex.lift_ι]
      exact h₂)⟩⟩⟩

end MarkedCore

theorem markedRightAnodyne_sharp_map {K L : SSet.{u}} {i : K ⟶ L}
    (hi : SSet.rightAnodyneExtensions i) :
    markedRightAnodyne ((MarkedPresheaf.sharp edgeMarking).map i) := by
  rw [markedRightAnodyne_eq_llp]
  intro Y B q hq
  refine ⟨fun {a b} sq => ?_⟩
  have hsharp {Z : SSet.{u}} {X : MarkedSSet.{u}} (φ : (MarkedPresheaf.sharp edgeMarking).obj Z ⟶ X)
      (e : Z _⦋1⦌) : (forget.map φ).app (op ⦋1⦌) e ∈ X.marked ⦋1⦌ :=
    MarkedPresheaf.map_mem_marked φ ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  let a' : K ⟶ MarkedSSet.markedCore Y :=
    Subcomplex.lift (forget.map a) (range_le_markedCore _ (hsharp a))
  let b' : L ⟶ MarkedSSet.markedCore B :=
    Subcomplex.lift (forget.map b) (range_le_markedCore _ (hsharp b))
  have ha' : a' ≫ (MarkedSSet.markedCore Y).ι = forget.map a := Subcomplex.lift_ι _ _
  have hb' : b' ≫ (MarkedSSet.markedCore B).ι = forget.map b := Subcomplex.lift_ι _ _
  have w : a' ≫ markedCoreMap q = i ≫ b' := (cancel_mono (MarkedSSet.markedCore B).ι).1 (by
    rw [Category.assoc, markedCoreMap_ι, ← Category.assoc, ha', Category.assoc, hb']
    exact ((forget.map_comp a q).symm.trans (congrArg forget.map sq.w)).trans
      (forget.map_comp _ _))
  obtain ⟨l⟩ := ((hi _ (rightFibrations_markedCoreMap q hq)).sq_hasLift ⟨w⟩).exists_lift
  refine ⟨⟨⟨edgeHomMk (l.l ≫ (MarkedSSet.markedCore Y).ι) fun e _ => app_ι_mem_marked l.l e,
    MarkedPresheaf.hom_ext ?_, MarkedPresheaf.hom_ext ?_⟩⟩⟩
  · rw [forget.map_comp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) l.fac_left).trans
      (Subcomplex.lift_ι _ _))
  · rw [forget.map_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (l.l ≫ ·) (markedCoreMap_ι q).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) l.fac_right).trans hb')))

theorem rightAnodyneExtensions_forget_map {K L : MarkedSSet.{u}} {f : K ⟶ L}
    (hf : markedRightAnodyne f) : SSet.rightAnodyneExtensions (forget.map f) := by
  intro X S p hp
  obtain ⟨hc, hall⟩ := (rightFibrations_iff_isCartesianFibration_and_forall p).1 hp
  have hs : markedRightFibrations ((MarkedPresheaf.sharp edgeMarking).map p) :=
    (markedRightFibrations_iff_of_forall_mem_marked _ fun _ =>
      (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl).2
      ⟨hc, fun _ => iff_of_true ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl) (hall _)⟩
  rw [markedRightAnodyne_eq_llp] at hf
  exact ((MarkedPresheaf.forgetSharpAdjunction edgeMarking).hasLiftingProperty_iff _ _).2
    (hf _ hs)

private noncomputable def unitIsoSharpStdSimplexZero :
    𝟙_ MarkedSSet.{u} ≅ (MarkedPresheaf.sharp edgeMarking).obj Δ[0] where
  hom := edgeHomMk (stdSimplex.isTerminalObj₀.from _) fun _ _ =>
    (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl
  inv := toUnit _
  hom_inv_id := toUnit_unique _ _
  inv_hom_id := MarkedPresheaf.hom_ext (stdSimplex.isTerminalObj₀.hom_ext _ _)

theorem markedRightAnodyne_sharpJPoint (ε : Bool) :
    markedRightAnodyne (MarkedSSet.sharpJPoint.{u} ε) := by
  refine (markedRightAnodyne.arrow_mk_iso_iff (Arrow.isoMk unitIsoSharpStdSimplexZero
    (Iso.refl _) ?_)).2 (markedRightAnodyne_sharp_map (rightAnodyneExtensions_coherentIso_vertex ε))
  refine MarkedPresheaf.hom_ext ?_
  have h₁ := congr_app (whiskerRight_endpoint_forget_comp_cartesianCylinderForgetIso_hom.{u} ε)
    (𝟙_ MarkedSSet.{u})
  have e : cartesianCylinderForgetIso.{u}.hom.app (𝟙_ MarkedSSet.{u}) ≫ fst _ _ =
      MarkedPresheaf.forget.map prod.fst :=
    CartesianMonoidalCategory.lift_fst _ _
  have h₂ : MarkedPresheaf.forget.map (MarkedSSet.sharpJPoint.{u} ε) =
      (joyalInterval.{u}.cylinder.endpoint ε).app (MarkedPresheaf.forget.obj (𝟙_ _)) ≫
        fst _ _ :=
    (Functor.map_comp _ _ _).trans ((congrArg _ e.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ fst _ _) h₁)))
  refine (forget.map_comp _ _).trans (Eq.trans ?_ (forget.map_comp _ _).symm)
  refine Eq.trans ?_ (congrArg (· ≫ _) h₂.symm)
  ext n x
  apply coherentIso.simplexEquiv.injective
  funext j
  cases ε <;> rfl

private theorem mono_coprod_desc_sharpJPoint :
    Mono (coprod.desc (MarkedSSet.sharpJPoint.{u} false) (MarkedSSet.sharpJPoint true)) := by
  have h : coprod.desc (MarkedSSet.sharpJPoint.{u} false) (MarkedSSet.sharpJPoint true) =
      cartesianCylinder.{u}.endpoints (𝟙_ _) ≫ cartesianCylinderTensorLeftIso.{u}.iso.hom.app _ ≫
        (ρ_ _).hom := by
    have key (ε : Bool) : MarkedSSet.sharpJPoint.{u} ε = (cartesianCylinder.{u}.endpoint ε).app _ ≫
        cartesianCylinderTensorLeftIso.{u}.iso.hom.app _ ≫ (ρ_ _).hom := by
      rw [← Category.assoc, cartesianCylinderTensorLeftIso.{u}.endpoint_app_comp_iso_hom_app,
        Category.assoc, rightUnitor_naturality, ← Category.assoc, ← unitors_equal,
        Iso.inv_hom_id, Category.id_comp]
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, key, ExactCylinder.endpoints, coprod.inl_desc_assoc]
    · rw [coprod.inr_desc, key, ExactCylinder.endpoints, coprod.inr_desc_assoc]
  rw [h]
  infer_instance

theorem anodyne_cartesianCylinder_markedRightGenerators :
    cartesianCylinder.{u}.anodyne markedRightGenerators = markedRightAnodyne := by
  refine le_antisymm (cartesianCylinder.anodyne_le _ _ ⟨inferInstance, le_saturation _,
    fun ε {_ _} i _ => ?_, fun {_ _} i _ hi => ?_⟩)
    (saturation_le _ _ (cartesianCylinder.le_anodyne _))
  · exact (markedRightAnodyne.arrow_mk_iso_iff
      (cartesianCylinderTensorLeftIso.endpointBoxArrowIso ε i)).2
      (markedRightAnodyne_pushoutProduct _ (markedRightAnodyne_sharpJPoint ε) i)
  · have := mono_coprod_desc_sharpJPoint.{u}
    exact (markedRightAnodyne.arrow_mk_iso_iff (cartesianCylinderTensorLeftIso.bothBoxArrowIso i ≪≫
      PushoutProduct.braiding _ _)).2 (markedRightAnodyne_pushoutProduct _ hi _)

end Atoms.Homotopical
