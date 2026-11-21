import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Atoms.Homotopical.Localizer.CellularContractions
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra

universe u

namespace Atoms.Homotopical

open MonoidalCategory CartesianMonoidalCategory

noncomputable def simplicialPoint (b : Bool) : ⊤_ SSet.{u} ⟶ Δ[1] :=
  (terminalIsoIsTerminal SSet.stdSimplex.isTerminalObj₀).hom ≫ SSet.stdSimplex.δ (cond b 0 1)

theorem simplicialPoint_app_apply (b : Bool) (d : SimplexCategoryᵒᵖ)
    (t : (⊤_ SSet.{u}).obj d) (j : Fin (d.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((simplicialPoint b).app d t)).toOrderHom j = cond b 1 0 := by
  cases b <;> rfl

theorem isPullback_simplicialPoint :
    IsPullback (initial.to (⊤_ SSet.{u})) (initial.to (⊤_ SSet.{u}))
      (simplicialPoint false) (simplicialPoint true) := by
  refine isPullback_of_app_ne simplicialPoint fun a _ _ h ↦ ?_
  have := congrArg (fun y ↦ (SSet.stdSimplex.objEquiv y).toOrderHom 0) h
  simp only [simplicialPoint_app_apply] at this
  exact absurd this (by decide)

noncomputable def simplicialInterval : SeparatingInterval.{u, 0} SimplexCategory :=
  ⟨Δ[1], simplicialPoint, isPullback_simplicialPoint⟩

noncomputable def simplicialCylinder : ExactCylinder.{u} SSet.{u} :=
  simplicialInterval.cylinder

noncomputable def terminalTensorIso (K : SSet.{u}) : K ≅ (⊤_ SSet.{u}) ⊗ K where
  hom := lift (terminal.from K) (𝟙 K)
  inv := snd _ _
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · exact terminal.hom_ext _ _
    · simp

@[reassoc]
theorem terminalTensorIso_hom_naturality {K X : SSet.{u}} (i : K ⟶ X) :
    i ≫ (terminalTensorIso X).hom = (terminalTensorIso K).hom ≫ (⊤_ SSet.{u}) ◁ i := by
  apply CartesianMonoidalCategory.hom_ext
  · exact terminal.hom_ext _ _
  · simp [terminalTensorIso]

private noncomputable def pushoutObjObjOfIso {S₁ S₂ K X K' X' : SSet.{u}} (s : S₁ ⟶ S₂)
    (i : K ⟶ X) (eK : K' ≅ S₁ ⊗ K) (eX : X' ≅ S₁ ⊗ X) (j : K' ⟶ S₂ ⊗ K) (k : K' ⟶ X')
    (j' : X' ⟶ S₂ ⊗ X) (hj : j = eK.hom ≫ s ▷ K) (hj' : j' = eX.hom ≫ s ▷ X)
    (hk : k ≫ eX.hom = eK.hom ≫ S₁ ◁ i) (box : pushout j k ⟶ S₂ ⊗ X)
    (hl : pushout.inl j k ≫ box = S₂ ◁ i) (hr : pushout.inr j k ≫ box = j') :
    (curriedTensor SSet.{u}).PushoutObjObj s i where
  pt := pushout j k
  inl := pushout.inl _ _
  inr := eX.inv ≫ pushout.inr _ _
  isPushout :=
    (IsPushout.of_hasPushout j k).of_iso eK (Iso.refl _) eX (Iso.refl _)
      ((Category.comp_id _).trans hj) hk
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
  ι := box
  inl_ι := hl
  inr_ι := by rw [Category.assoc, hr, hj']; exact Iso.inv_hom_id_assoc _ _

noncomputable def coprodTensorIso (K : SSet.{u}) :
    K ⨿ K ≅ ((⊤_ SSet.{u}) ⨿ (⊤_ SSet.{u})) ⊗ K :=
  coprod.mapIso (terminalTensorIso K) (terminalTensorIso K) ≪≫
    PreservesColimitPair.iso (tensorRight K) _ _

theorem coprodTensorIso_hom (K : SSet.{u}) :
    (coprodTensorIso K).hom = coprod.desc ((terminalTensorIso K).hom ≫ coprod.inl ▷ K)
      ((terminalTensorIso K).hom ≫ coprod.inr ▷ K) := by
  refine coprod.hom_ext ?_ ?_ <;>
    (simp only [coprodTensorIso, coprodComparison, Iso.trans_hom, coprod.mapIso_hom,
      PreservesColimitPair.iso_hom, coprod.inl_map_assoc, coprod.inr_map_assoc, coprod.inl_desc,
      coprod.inr_desc]
     rfl)

theorem coprodTensorIso_hom_naturality {K X : SSet.{u}} (i : K ⟶ X) :
    coprod.map i i ≫ (coprodTensorIso X).hom =
      (coprodTensorIso K).hom ≫ ((⊤_ SSet.{u}) ⨿ (⊤_ SSet.{u})) ◁ i := by
  rw [coprodTensorIso_hom, coprodTensorIso_hom]
  refine coprod.hom_ext ?_ ?_ <;>
    simp only [coprod.inl_map_assoc, coprod.inr_map_assoc, coprod.inl_desc, coprod.inr_desc,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, terminalTensorIso_hom_naturality_assoc,
      whisker_exchange, Category.assoc]

instance isIso_fst_terminal (X : SSet.{u}) : IsIso (fst X (⊤_ SSet.{u})) :=
  ⟨lift (𝟙 _) (terminal.from _), CartesianMonoidalCategory.hom_ext _ _ (by simp)
    (terminal.hom_ext _ _), by simp⟩

namespace SeparatingInterval

variable (I : SeparatingInterval.{u, 0} SimplexCategory)

theorem cylinder_endpoint_app (ε : Bool) (K : SSet.{u}) :
    (I.cylinder.endpoint ε).app K = (terminalTensorIso K).hom ≫ I.pt ε ▷ K := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [SeparatingInterval.cylinder, segmentEndpoint, terminalTensorIso]

noncomputable def endpointBoxPushoutObjObj (ε : Bool) {K X : SSet.{u}} (i : K ⟶ X) :
    (curriedTensor SSet.{u}).PushoutObjObj (I.pt ε) i :=
  pushoutObjObjOfIso _ i (terminalTensorIso K) (terminalTensorIso X)
    ((I.cylinder.endpoint ε).app K) i ((I.cylinder.endpoint ε).app X)
    (I.cylinder_endpoint_app ε K) (I.cylinder_endpoint_app ε X)
    (terminalTensorIso_hom_naturality i) (I.cylinder.endpointBox ε i)
    (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _)

noncomputable def boundary : (⊤_ SSet.{u}) ⨿ (⊤_ SSet.{u}) ⟶ I.interval :=
  coprod.desc (I.pt false) (I.pt true)

theorem coprodTensorIso_hom_whiskerRight_boundary (K : SSet.{u}) :
    (coprodTensorIso K).hom ≫ I.boundary ▷ K =
      coprod.desc ((terminalTensorIso K).hom ≫ I.pt false ▷ K)
        ((terminalTensorIso K).hom ≫ I.pt true ▷ K) := by
  rw [coprodTensorIso_hom]
  refine coprod.hom_ext ?_ ?_ <;>
    simp only [coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
      ← comp_whiskerRight, Category.assoc, boundary]

theorem cylinder_endpoints (K : SSet.{u}) :
    I.cylinder.endpoints K = (coprodTensorIso K).hom ≫ I.boundary ▷ K := by
  refine Eq.trans ?_ (I.coprodTensorIso_hom_whiskerRight_boundary K).symm
  simp only [ExactCylinder.endpoints, cylinder_endpoint_app]
  rfl

noncomputable def bothBoxPushoutObjObj {K X : SSet.{u}} (i : K ⟶ X) :
    (curriedTensor SSet.{u}).PushoutObjObj I.boundary i :=
  pushoutObjObjOfIso _ i (coprodTensorIso K) (coprodTensorIso X)
    (I.cylinder.endpoints K) (coprod.map i i) (I.cylinder.endpoints X)
    (I.cylinder_endpoints K) (I.cylinder_endpoints X)
    (coprodTensorIso_hom_naturality i) (I.cylinder.bothBox i)
    (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _)

instance mono_boundary : Mono I.boundary := by
  have h₀ : Mono (I.cylinder.endpoints (⊤_ SSet.{u})) := inferInstance
  have h : Mono ((coprodTensorIso (⊤_ SSet.{u})).hom ≫ I.boundary ▷ ⊤_ SSet.{u}) := by
    rwa [cylinder_endpoints] at h₀
  have h' : Mono (((coprodTensorIso (⊤_ SSet.{u})).hom ≫ fst _ _) ≫ I.boundary) := by
    rw [Category.assoc, ← whiskerRight_fst, ← Category.assoc]
    infer_instance
  exact (mono_comp_iff_of_isIso _ _).1 h'

end SeparatingInterval

theorem face_singleton_eq_horn (i : Fin 2) :
    SSet.stdSimplex.face.{u} {i} = SSet.horn 1 i := by
  ext m x
  simp only [SSet.stdSimplex.face_obj, SSet.mem_horn_iff]
  simp only [Nat.reduceAdd, Finset.top_eq_univ, Finset.subset_iff, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_singleton, forall_exists_index, forall_apply_eq_imp_iff,
    Set.mem_ofPred_eq, Set.union_singleton, ne_eq, Set.eq_univ_iff_forall, Set.mem_insert_iff,
    Set.mem_range, Fin.forall_fin_two, Fin.isValue, not_and, not_or, not_exists]
  change (∀ a, SSet.stdSimplex.asOrderHom x a = i) ↔ _
  generalize (SSet.stdSimplex.asOrderHom x : Fin _ → Fin 2) = f
  fin_cases i
  · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, true_or, Fin.one_eq_zero_iff,
      OfNat.ofNat_ne_one, not_false_eq_true, true_and, forall_const]
    exact forall_congr' fun t ↦ by generalize f t = b; revert b; decide
  · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      false_or, not_true_eq_false, false_and, imp_false, not_exists]
    exact forall_congr' fun t ↦ by generalize f t = b; revert b; decide

theorem anodyneExtensions_simplicialPoint (b : Bool) :
    SSet.anodyneExtensions (simplicialPoint.{u} b) := by
  refine SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _) ?_
  have h : (SSet.stdSimplex.faceSingletonIso.{u} (cond b 1 0 : Fin 2)).hom ≫
      (SSet.stdSimplex.face {(cond b 1 0 : Fin 2)}).ι = SSet.stdSimplex.δ (cond b 0 1) := by
    cases b
    · exact SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ
    · exact SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ
  change SSet.anodyneExtensions (SSet.stdSimplex.δ (cond b 0 1))
  rw [← h]
  exact SSet.anodyneExtensions.hom_comp_ι_of_eq_horn _ (face_singleton_eq_horn _) _

instance isSaturated_anodyneExtensions : IsSaturated.{u} SSet.anodyneExtensions.{u} := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  infer_instance

theorem isAnodyneClass_anodyneExtensions (S : MorphismProperty SSet.{u})
    (hS : S ≤ SSet.anodyneExtensions.{u}) :
    IsAnodyneClass simplicialCylinder.{u} S SSet.anodyneExtensions.{u} where
  isSaturated := inferInstance
  generators_le := hS
  endpointBox_mem ε {_ _} i hi :=
    have := hi
    SSet.anodyneExtensions_pushoutObjObjι' (simplicialInterval.{u}.endpointBoxPushoutObjObj ε i)
      (anodyneExtensions_simplicialPoint ε)
  bothBox_mem {_ _} i _ h :=
    SSet.anodyneExtensions_pushoutObjObjι (simplicialInterval.{u}.bothBoxPushoutObjObj i) h

section HornRetraction

variable {n : ℕ} (k : Fin (n + 2))

def hornRetractionFun (e : Fin 2) (i : Fin (n + 2)) : Fin (n + 2) :=
  if e = 0 then min i k else max i k

theorem hornRetractionFun_eq_or (e : Fin 2) (i : Fin (n + 2)) :
    hornRetractionFun k e i = i ∨ hornRetractionFun k e i = k := by
  unfold hornRetractionFun
  split_ifs
  · exact min_choice i k
  · exact max_choice i k

theorem hornRetractionFun_mono {e e' : Fin 2} {i i' : Fin (n + 2)} (he : e ≤ e') (hi : i ≤ i') :
    hornRetractionFun k e i ≤ hornRetractionFun k e' i' := by
  unfold hornRetractionFun
  by_cases h : e = 0
  · by_cases h' : e' = 0
    · rw [if_pos h, if_pos h']
      exact min_le_min hi le_rfl
    · rw [if_pos h, if_neg h']
      exact (min_le_left _ _).trans (hi.trans (le_max_left _ _))
  · have h' : ¬ e' = 0 := fun h' ↦ h (le_antisymm (h' ▸ he) (Fin.zero_le _))
    rw [if_neg h, if_neg h']
    exact max_le_max hi le_rfl

def hornSectionOrderHom : Fin (n + 2) →o Fin 2 where
  toFun i := if k < i then 1 else 0
  monotone' i i' h := by
    dsimp only
    split_ifs with h₁ h₂
    · exact le_rfl
    · exact absurd (h₁.trans_le h) h₂
    · exact Fin.zero_le _
    · exact le_rfl

theorem hornRetractionFun_hornSectionOrderHom (i : Fin (n + 2)) :
    hornRetractionFun k (hornSectionOrderHom k i) i = i := by
  change (if (if k < i then (1 : Fin 2) else 0) = 0 then min i k else max i k) = i
  by_cases h : k < i
  · rw [if_pos h, if_neg (by decide)]
    exact max_eq_left h.le
  · rw [if_neg h, if_pos rfl]
    exact min_eq_left (not_lt.1 h)

def hornRetraction : (Δ[1] ⊗ Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 1] where
  app _ := ↾fun x ↦ SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    { toFun := fun j ↦ hornRetractionFun k ((SSet.stdSimplex.objEquiv x.1).toOrderHom j)
        ((SSet.stdSimplex.objEquiv x.2).toOrderHom j)
      monotone' := fun _ _ h ↦ hornRetractionFun_mono k
        ((SSet.stdSimplex.objEquiv x.1).toOrderHom.monotone h)
        ((SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone h) })
  naturality _ _ _ := rfl

def hornSection : (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n + 1] :=
  lift (SSet.stdSimplex.map (SimplexCategory.Hom.mk (hornSectionOrderHom k))) (𝟙 _)

theorem hornSection_hornRetraction : hornSection k ≫ hornRetraction k = 𝟙 _ := by
  ext _ x
  apply SSet.stdSimplex.objEquiv.injective
  ext j : 3
  exact hornRetractionFun_hornSectionOrderHom k _

theorem hornRetraction_mem_horn {d : SimplexCategoryᵒᵖ} (x : (Δ[1] ⊗ Δ[n + 1] : SSet.{u}).obj d)
    (hx : x.2 ∈ (SSet.horn (n + 1) k).obj d) :
    (hornRetraction k).app d x ∈ (SSet.horn (n + 1) k).obj d := by
  rw [SSet.mem_horn_iff] at hx ⊢
  obtain ⟨j, hj⟩ := (Set.ne_univ_iff_exists_notMem _).1 hx
  refine (Set.ne_univ_iff_exists_notMem _).2 ⟨j, ?_⟩
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_or, not_exists] at hj ⊢
  refine ⟨fun t ht ↦ ?_, hj.2⟩
  rcases hornRetractionFun_eq_or k ((SSet.stdSimplex.objEquiv x.1).toOrderHom t)
    ((SSet.stdSimplex.objEquiv x.2).toOrderHom t) with h | h
  · exact hj.1 t (h.symm.trans ht)
  · exact hj.2 (h.symm.trans ht).symm

def hornEndpoint : Bool := decide (k = Fin.last (n + 1))

theorem hornRetraction_mem_horn_of_endpoint {d : SimplexCategoryᵒᵖ}
    (x : (Δ[1] ⊗ Δ[n + 1] : SSet.{u}).obj d)
    (hx : ∀ t, (SSet.stdSimplex.objEquiv x.1).toOrderHom t = cond (hornEndpoint k) 1 0) :
    (hornRetraction k).app d x ∈ (SSet.horn (n + 1) k).obj d := by
  rw [SSet.mem_horn_iff, Set.ne_univ_iff_exists_notMem]
  by_cases hk : k = Fin.last (n + 1)
  · have he : hornEndpoint k = true := decide_eq_true hk
    refine ⟨0, ?_⟩
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_or, not_exists]
    refine ⟨fun t ht ↦ ?_, fun h0 ↦ ?_⟩
    · have ht' : hornRetractionFun k 1 ((SSet.stdSimplex.objEquiv x.2).toOrderHom t) = 0 := by
        rw [← ht]
        exact congrArg (fun e ↦ hornRetractionFun k e _) ((hx t).trans (by rw [he]; rfl)).symm
      rw [hornRetractionFun, if_neg (by decide)] at ht'
      have : k ≤ 0 := ht' ▸ le_max_right _ _
      rw [hk] at this
      exact absurd this (by simp)
    · rw [hk] at h0
      exact absurd h0 (by simp [Fin.ext_iff])
  · have he : hornEndpoint k = false := decide_eq_false hk
    refine ⟨Fin.last (n + 1), ?_⟩
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_or, not_exists]
    refine ⟨fun t ht ↦ ?_, fun h0 ↦ hk h0.symm⟩
    have ht' : hornRetractionFun k 0 ((SSet.stdSimplex.objEquiv x.2).toOrderHom t) =
        Fin.last (n + 1) := by
      rw [← ht]
      exact congrArg (fun e ↦ hornRetractionFun k e _) ((hx t).trans (by rw [he]; rfl)).symm
    rw [hornRetractionFun, if_pos rfl] at ht'
    have : Fin.last (n + 1) ≤ k := ht' ▸ min_le_right _ _
    exact hk (le_antisymm (Fin.le_last k) this)

def hornRetractionBox :
    (Δ[1] : SSet.{u}) ⊗ (SSet.horn (n + 1) k : SSet.{u}) ⟶ (SSet.horn (n + 1) k : SSet.{u}) :=
  SSet.Subcomplex.lift ((Δ[1] : SSet.{u}) ◁ (SSet.horn (n + 1) k).ι ≫ hornRetraction k) (by
    rintro d _ ⟨x, rfl⟩
    exact hornRetraction_mem_horn k _ x.2.2)

noncomputable def hornRetractionEnd :
    (⊤_ SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ (SSet.horn (n + 1) k : SSet.{u}) :=
  SSet.Subcomplex.lift (simplicialPoint (hornEndpoint k) ▷ (Δ[n + 1] : SSet.{u}) ≫
    hornRetraction k) (by
    rintro d _ ⟨x, rfl⟩
    exact hornRetraction_mem_horn_of_endpoint k _
      fun t ↦ simplicialPoint_app_apply (hornEndpoint k) d x.1 t)

@[reassoc]
theorem hornRetractionBox_ι :
    hornRetractionBox k ≫ (SSet.horn (n + 1) k).ι =
      (Δ[1] : SSet.{u}) ◁ (SSet.horn (n + 1) k).ι ≫ hornRetraction k := rfl

@[reassoc]
theorem hornRetractionEnd_ι :
    hornRetractionEnd k ≫ (SSet.horn (n + 1) k).ι =
      simplicialPoint (hornEndpoint k) ▷ (Δ[n + 1] : SSet.{u}) ≫ hornRetraction k := rfl

noncomputable def hornRetract :
    RetractArrow (SSet.horn (n + 1) k).ι
      (simplicialInterval.{u}.endpointBoxPushoutObjObj (hornEndpoint k)
        (SSet.horn (n + 1) k).ι).ι := by
  let sq : (curriedTensor SSet.{u}).PushoutObjObj (simplicialPoint (hornEndpoint k))
      (SSet.horn (n + 1) k).ι :=
    simplicialInterval.{u}.endpointBoxPushoutObjObj (hornEndpoint k) (SSet.horn (n + 1) k).ι
  change RetractArrow (SSet.horn (n + 1) k).ι sq.ι
  have hr : ((curriedTensor SSet.{u}).map (simplicialPoint (hornEndpoint k))).app
      (SSet.horn (n + 1) k : SSet.{u}) ≫ hornRetractionBox k =
      ((curriedTensor SSet.{u}).obj (⊤_ SSet.{u})).map (SSet.horn (n + 1) k).ι ≫
        hornRetractionEnd k := by
    rw [← cancel_mono (SSet.horn (n + 1) k).ι]
    simp only [Category.assoc, hornRetractionBox_ι, hornRetractionEnd_ι, curriedTensor_map_app,
      curriedTensor_obj_map]
    rw [whisker_exchange_assoc]
  exact
    { i := Arrow.homMk' (lift ((SSet.horn (n + 1) k).ι ≫
          SSet.stdSimplex.map (SimplexCategory.Hom.mk (hornSectionOrderHom k))) (𝟙 _) ≫ sq.inl)
        (hornSection k) (by
          rw [Category.assoc, sq.inl_ι, curriedTensor_obj_map]
          apply CartesianMonoidalCategory.hom_ext <;> simp [hornSection])
      r := Arrow.homMk' (sq.isPushout.desc (hornRetractionBox k) (hornRetractionEnd k) hr)
        (hornRetraction k) (by
          apply sq.isPushout.hom_ext
          · rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc, hornRetractionBox_ι,
              curriedTensor_obj_map]
          · rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc, hornRetractionEnd_ι,
              curriedTensor_map_app])
      retract := by
        apply Arrow.hom_ext
        · simp only [Arrow.comp_left, Arrow.homMk'_left, Arrow.id_left, Arrow.mk_left]
          rw [← cancel_mono (SSet.horn (n + 1) k).ι, Category.assoc, Category.assoc,
            sq.isPushout.inl_desc_assoc, hornRetractionBox_ι, Category.id_comp, ← Category.assoc]
          have h : lift ((SSet.horn (n + 1) k).ι ≫ SSet.stdSimplex.map
              (SimplexCategory.Hom.mk (hornSectionOrderHom k))) (𝟙 _) ≫
                (Δ[1] : SSet.{u}) ◁ (SSet.horn (n + 1) k).ι =
              (SSet.horn (n + 1) k).ι ≫ hornSection k := by
            apply CartesianMonoidalCategory.hom_ext <;> simp [hornSection]
          rw [h, Category.assoc, hornSection_hornRetraction, Category.comp_id]
        · simpa using hornSection_hornRetraction k }

end HornRetraction

theorem J_le_anodyne_bot :
    SSet.modelCategoryQuillen.J.{u} ≤ simplicialCylinder.{u}.anodyne ⊥ := by
  intro _ _ f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  exact MorphismProperty.of_retract (hornRetract k)
    ((simplicialCylinder.{u}.isAnodyneClass_anodyne ⊥).endpointBox_mem _ _ inferInstance)

theorem anodyne_bot_eq_anodyneExtensions :
    simplicialCylinder.{u}.anodyne ⊥ = SSet.anodyneExtensions.{u} := by
  refine le_antisymm (simplicialCylinder.{u}.anodyne_le ⊥ _
    (isAnodyneClass_anodyneExtensions ⊥ bot_le)) ?_
  rw [SSet.anodyneExtensions_eq_llp_rlp, ← saturation_eq_llp_rlp]
  exact saturation_le _ _ J_le_anodyne_bot

theorem anodyne_J_eq_anodyneExtensions :
    simplicialCylinder.{u}.anodyne SSet.modelCategoryQuillen.J.{u} =
      SSet.anodyneExtensions.{u} := by
  refine le_antisymm (simplicialCylinder.{u}.anodyne_le _ _
    (isAnodyneClass_anodyneExtensions _ ?_)) ?_
  · rw [SSet.anodyneExtensions_eq_llp_rlp]
    exact le_llp_rlp _
  · rw [← anodyne_bot_eq_anodyneExtensions]
    exact simplicialCylinder.{u}.anodyne_mono bot_le

theorem rlp_anodyne_bot_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    (simplicialCylinder.{u}.anodyne ⊥).rlp p ↔ SSet.modelCategoryQuillen.J.rlp p := by
  rw [anodyne_bot_eq_anodyneExtensions, SSet.anodyneExtensions_eq_llp_rlp, rlp_llp_rlp]

open SSet.modelCategoryQuillen in
theorem isFibrant_bot_iff_kanComplex (X : SSet.{u}) :
    simplicialCylinder.{u}.IsFibrant ⊥ X ↔ SSet.KanComplex X := by
  rw [ExactCylinder.IsFibrant, rlp_anodyne_bot_iff]
  exact (SSet.modelCategoryQuillen.fibration_iff (terminal.from X)).symm

def kanWeak : MorphismProperty SSet.{u} := simplicialCylinder.{u}.weakEquivalences ⊥

theorem kanWeak_eq_weakEquivalences_J :
    kanWeak = simplicialCylinder.{u}.weakEquivalences SSet.modelCategoryQuillen.J.{u} := by
  unfold kanWeak ExactCylinder.weakEquivalences ExactCylinder.IsFibrant
  rw [anodyne_bot_eq_anodyneExtensions, anodyne_J_eq_anodyneExtensions]

instance isALocalizer_kanWeak : IsALocalizer kanWeak.{u} :=
  simplicialCylinder.{u}.isALocalizer_weakEquivalences ⊥ bot_le

instance isAccessibleALocalizer_kanWeak : IsAccessibleALocalizer kanWeak.{u} :=
  simplicialCylinder.{u}.isAccessibleALocalizer_weakEquivalences ⊥ bot_le

theorem anodyneExtensions_le_kanWeak : SSet.anodyneExtensions.{u} ≤ kanWeak := by
  rw [← anodyne_bot_eq_anodyneExtensions]
  exact simplicialCylinder.{u}.anodyne_le_weakEquivalences ⊥ bot_le

theorem kanWeak_eq_generatedALocalizer_cellularContractions :
    kanWeak = generatedALocalizer simplicialCylinder.{u}.cellularContractions := by
  rw [kanWeak, simplicialCylinder.{u}.weakEquivalences_eq_generatedALocalizer_cellularContractions ⊥
    bot_le, bot_sup_eq]

end Atoms.Homotopical
