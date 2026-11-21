import Atoms.Homotopical.Regular.Presheaf

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A] {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}

instance isEmpty_costructuredArrow_initial :
    IsEmpty (CostructuredArrow yoneda (⊥_ (Aᵒᵖ ⥤ Type v))) :=
  ⟨fun c ↦ PEmpty.elim
    ((initial.to ((Functor.const Aᵒᵖ).obj PEmpty.{v + 1})).app _ (yonedaEquiv c.hom))⟩

theorem IsALocalizer.isRegular_initial [hV : IsALocalizer V] :
    IsRegular V (⊥_ (Aᵒᵖ ⥤ Type v)) := by
  have : IsIso (regularizationMap (⊥_ (Aᵒᵖ ⥤ Type v))) :=
    ⟨⟨initial.to _, colimit.hom_ext fun c ↦ isEmptyElim c, initial.hom_ext _ _⟩⟩
  exact hV.isomorphisms_le _ (isomorphisms.infer_property _)

section SieveChain

variable {C : Type v} [SmallCategory C] {J : Type v} [LinearOrder J]
  (P : J → ObjectProperty C) (hP : ∀ ⦃i j : J⦄, i ≤ j → P i ≤ P j) (F : C ⥤ Aᵒᵖ ⥤ Type v)

noncomputable def sieveChain : J ⥤ Aᵒᵖ ⥤ Type v where
  obj j := colimit ((P j).ι ⋙ F)
  map {i j} φ := sievePre (hP (leOfHom φ)) F
  map_id j := colimit.hom_ext fun x ↦ by
    rw [ι_sievePre, Category.comp_id]
    rfl
  map_comp {i j k} φ ψ := colimit.hom_ext fun x ↦ by
    rw [ι_sievePre, ← Category.assoc, ι_sievePre, ι_sievePre]
    rfl

noncomputable def sieveChainCocone : Cocone (sieveChain P hP F) where
  pt := colimit F
  ι :=
    { app j := colimit.pre F (P j).ι
      naturality {i j} φ := colimit.hom_ext fun x ↦ by
        change colimit.ι _ x ≫ sievePre _ F ≫ colimit.pre F (P j).ι = _ ≫ _ ≫ 𝟙 _
        rw [ι_sievePre_assoc, colimit.ι_pre, Category.comp_id, colimit.ι_pre]
        rfl }

variable {P hP} in
theorem sieveChain_ι_eq (s : Cocone (sieveChain P hP F)) (c : C) {i j : J} (hi : P i c)
    (hj : P j c) :
    colimit.ι ((P i).ι ⋙ F) ⟨c, hi⟩ ≫ s.ι.app i = colimit.ι ((P j).ι ⋙ F) ⟨c, hj⟩ ≫ s.ι.app j := by
  have key : ∀ {i j : J} (hij : i ≤ j) (hi : P i c) (hj : P j c),
      colimit.ι ((P i).ι ⋙ F) ⟨c, hi⟩ ≫ s.ι.app i =
        colimit.ι ((P j).ι ⋙ F) ⟨c, hj⟩ ≫ s.ι.app j := by
    intro i j hij hi hj
    rw [← s.w (homOfLE hij)]
    exact (ι_sievePre_assoc (hP hij) F ⟨c, hi⟩ _).trans rfl
  rcases le_total i j with h | h
  · exact key h hi hj
  · exact (key h hj hi).symm

noncomputable def isColimitSieveChainCocone
    (hpred : ∀ (j : J) ⦃c c' : C⦄, (c ⟶ c') → P j c' → P j c) (hcov : ∀ c, ∃ j, P j c) :
    IsColimit (sieveChainCocone P hP F) := by
  choose k hk using hcov
  let cc : Cocone (sieveChain P hP F) → Cocone F := fun s ↦
    { pt := s.pt
      ι :=
        { app c := colimit.ι ((P (k c)).ι ⋙ F) ⟨c, hk c⟩ ≫ s.ι.app (k c)
          naturality c c' φ := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            rw [sieveChain_ι_eq F s c (hk c) (hpred (k c') φ (hk c'))]
            exact colimit.w_assoc ((P (k c')).ι ⋙ F)
              (ObjectProperty.homMk φ :
                (⟨c, hpred (k c') φ (hk c')⟩ : (P (k c')).FullSubcategory) ⟶ ⟨c', hk c'⟩)
              (s.ι.app (k c')) } }
  exact
    { desc s := colimit.desc F (cc s)
      fac s j := colimit.hom_ext fun x ↦ by
        change colimit.ι _ x ≫ colimit.pre F (P j).ι ≫ _ = _
        rw [colimit.ι_pre_assoc, colimit.ι_desc]
        exact sieveChain_ι_eq F s x.obj (hk x.obj) x.property
      uniq s m hm := colimit.hom_ext (F := F) fun c ↦ by
        rw [colimit.ι_desc]
        change colimit.ι F c ≫ m = colimit.ι ((P (k c)).ι ⋙ F) ⟨c, hk c⟩ ≫ s.ι.app (k c)
        rw [← hm (k c)]
        exact (colimit.ι_pre_assoc F (P (k c)).ι ⟨c, hk c⟩ (m : colimit F ⟶ s.pt)).symm }

end SieveChain

theorem mono_ι_app_of_isColimit {J : Type v} [LinearOrder J] (F : J ⥤ Aᵒᵖ ⥤ Type v)
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) {c : Cocone F}
    (hc : IsColimit c) (j : J) : Mono (c.ι.app j) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun a ↦ (mono_iff_injective _).2 fun x y hxy ↦ ?_
  have hc' := isColimitOfPreserves ((evaluation Aᵒᵖ (Type v)).obj a) hc
  obtain ⟨k, f, g, hfg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ (evaluation Aᵒᵖ (Type v)).obj a) hc'
      (xi := x) (xj := y)).1 hxy
  have hg : g = f := Subsingleton.elim _ _
  subst hg
  have hm : Mono ((F.map g).app a) := by
    have h := hF j k (leOfHom g)
    rw [show homOfLE (leOfHom g) = g from Subsingleton.elim _ _] at h
    exact inferInstance
  exact (mono_iff_injective ((F.map g).app a)).1 hm hfg

theorem IsAccessibleALocalizer.isRegular_of_isColimit [hV : IsAccessibleALocalizer V]
    {J : Type v} [LinearOrder J] [WellFoundedLT J] (F : J ⥤ Aᵒᵖ ⥤ Type v)
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) {c : Cocone F}
    (hc : IsColimit c) (h : ∀ j, IsRegular V (F.obj j)) : IsRegular V c.pt := by
  have hm : ∀ j, Mono (c.ι.app j) := fun j ↦ mono_ι_app_of_isColimit F hF hc j
  let Q := (projectiveReplacement A (CostructuredArrow yoneda c.pt)).obj
    (representablesOver c.pt)
  let π := (projectiveReplacementπ A (CostructuredArrow yoneda c.pt)).app
    (representablesOver c.pt)
  let P : J → ObjectProperty (CostructuredArrow yoneda c.pt) := fun j ↦ elementsSieve (c.ι.app j)
  have hP : ∀ ⦃i j : J⦄, i ≤ j → P i ≤ P j := by
    rintro i j hij s ⟨x, hx⟩
    exact ⟨x ≫ F.map (homOfLE hij), by rw [Category.assoc, c.w, hx]⟩
  have hpred : ∀ (j : J) ⦃s s' : CostructuredArrow yoneda c.pt⦄, (s ⟶ s') → P j s' → P j s :=
    fun j _ _ φ ↦ elementsSieve_of_hom _ φ
  have hcov : ∀ s, ∃ j, P j s := by
    intro s
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation Aᵒᵖ (Type v)).obj (Opposite.op s.left)) hc)
      (yonedaEquiv s.hom)
    refine ⟨j, yonedaEquiv.symm x, yonedaEquiv.injective ?_⟩
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hx
  have hQ : projectiveCofibrations A _ (initial.to Q) :=
    projectiveCofibrations_initial_to_projectiveReplacement _
  have hmono : ∀ (i j : J) (hij : i ≤ j),
      Mono ((sieveChain P hP Q).map (homOfLE hij)) := fun i j hij ↦
    mono_sievePre (hP hij) (hpred i) Q (projectiveCofibrations_initial_to_comp _
      (projectiveCofibrations_whiskerLeft_ι _ (hpred j) hQ))
  let φ : sieveChain P hP Q ⟶ F :=
    { app j := sieveComparison (c.ι.app j) Q π
      naturality i j hij := by
        refine (cancel_mono (c.ι.app j)).1 (colimit.hom_ext fun s ↦ ?_)
        change colimit.ι _ s ≫ (sievePre (hP (leOfHom hij)) Q ≫
            sieveComparison (c.ι.app j) Q π) ≫ c.ι.app j =
          colimit.ι _ s ≫ (sieveComparison (c.ι.app i) Q π ≫ F.map hij) ≫ c.ι.app j
        repeat rw [Category.assoc]
        rw [c.w, ι_sievePre_assoc, ι_sieveComparison_comp, ι_sieveComparison_comp]
        rfl }
  refine hV.isALocalizer.of_isColimit hmono hF φ
    (fun j ↦ hV.sieveComparison_mem (c.ι.app j) (h j))
    (isColimitSieveChainCocone P hP Q hpred hcov) hc (regularizationMap c.pt) fun j ↦ ?_
  refine colimit.hom_ext fun s ↦ ?_
  change colimit.ι _ s ≫ colimit.pre Q (P j).ι ≫ regularizationMap c.pt =
    colimit.ι _ s ≫ sieveComparison (c.ι.app j) Q π ≫ c.ι.app j
  rw [colimit.ι_pre_assoc, ι_regularizationMap, ι_sieveComparison_comp]
  rfl

end Atoms.Homotopical
