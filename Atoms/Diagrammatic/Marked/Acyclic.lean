import Atoms.Diagrammatic.Marked.LocalizationLift
import Atoms.Diagrammatic.Marked.ModelStructure
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

namespace MarkedDiagSet

noncomputable def markedLoc (Y : MarkedDiagSet.{u}) : MarkedDiagSet.{u} :=
  pushout ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y)
    ((MarkedPresheaf.flat atomMarking).map (toLoc Y))

noncomputable def markedAtomToMarkedWalkingEquivalence (U : Atom) (hU : 0 < U.dimension) :
    markedAtom.{u} U hU ⟶ markedWalkingEquivalence U hU :=
  MarkedPresheaf.homMk (toWalkingEquivalence U hU) fun V x hx => by
    refine (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 ?_
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | hx
    · exact Or.inl (isDegenerate_app _ hx)
    · exact Or.inr ⟨x.down, hx, rfl⟩

theorem forget_map_markedAtomToMarkedWalkingEquivalence (U : Atom)
    (hU : 0 < U.dimension) :
    MarkedPresheaf.forget.map (markedAtomToMarkedWalkingEquivalence.{u} U hU) =
      toWalkingEquivalence U hU :=
  rfl

noncomputable def markedAtomToInvertorPair (U : Atom) (hU : 0 < U.dimension) :
    markedAtom.{u} U hU ⟶ markedAbove (invertorPair U hU) (U.dimension - 1) :=
  MarkedPresheaf.homMk (toInvertorPair U hU) fun V x hx => by
    refine (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 ?_
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | hx
    · exact Or.inl (isDegenerate_app _ hx)
    · refine Or.inr ?_
      rw [Atom.dimension_eq_of_iso (asIso (x.down : V ⟶ U))]
      omega

theorem forget_map_markedAtomToInvertorPair (U : Atom) (hU : 0 < U.dimension) :
    MarkedPresheaf.forget.map (markedAtomToInvertorPair.{u} U hU) = toInvertorPair U hU :=
  rfl

private theorem app_eq_map_yonedaEquiv {U V : Atom} {P : DiagSet.{u}}
    (φ : uliftYoneda.{u}.obj U ⟶ P) (e : V ⟶ U) :
    φ.app (op V) ⟨e⟩ = P.map e.op (uliftYonedaEquiv φ) := by
  rw [uliftYonedaEquiv_naturality]
  simp [uliftYonedaEquiv_apply]

noncomputable def markedWalkingEquivalenceHom (U : Atom) (hU : 0 < U.dimension)
    {Z : MarkedDiagSet.{u}} (g : walkingEquivalence U hU ⟶ Z.underlying)
    (hg : uliftYonedaEquiv (toWalkingEquivalence U hU ≫ g) ∈ Z.marked U) :
    markedWalkingEquivalence U hU ⟶ Z :=
  MarkedPresheaf.homMk g fun V x hx => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | ⟨e, he, rfl⟩
    · exact Z.mem_marked_of_isDegenerate (isDegenerate_app g hx)
    · exact (congrArg (· ∈ Z.marked V) (app_eq_map_yonedaEquiv
        (toWalkingEquivalence U hU ≫ g) e)).mpr ((Z.transport (asIso e) _).1 hg)

@[simp]
theorem forget_map_markedWalkingEquivalenceHom (U : Atom) (hU : 0 < U.dimension)
    {Z : MarkedDiagSet.{u}} (g : walkingEquivalence U hU ⟶ Z.underlying)
    (hg : uliftYonedaEquiv (toWalkingEquivalence U hU ≫ g) ∈ Z.marked U) :
    MarkedPresheaf.forget.map (markedWalkingEquivalenceHom U hU g hg) = g :=
  rfl

noncomputable def markedAtomHom (U : Atom) (hU : 0 < U.dimension) {Z : MarkedDiagSet.{u}}
    (x : Z.underlying.obj (op U)) (hx : x ∈ Z.marked U) : markedAtom U hU ⟶ Z :=
  MarkedPresheaf.homMk (uliftYonedaEquiv.symm x) fun V y hy => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | hy
    · exact Z.mem_marked_of_isDegenerate (isDegenerate_app _ hy)
    · exact (congrArg (· ∈ Z.marked V)
        (rfl : (uliftYonedaEquiv.symm x).app (op V) y = Z.underlying.map y.down.op x)).mpr
        ((Z.transport (asIso (y.down : V ⟶ U)) x).1 hx)

@[simp]
theorem forget_map_markedAtomHom (U : Atom) (hU : 0 < U.dimension) {Z : MarkedDiagSet.{u}}
    (x : Z.underlying.obj (op U)) (hx : x ∈ Z.marked U) :
    MarkedPresheaf.forget.map (markedAtomHom U hU x hx) = uliftYonedaEquiv.symm x :=
  rfl

@[simp]
theorem forget_map_counit_app (Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y) =
      𝟙 Y.underlying :=
  rfl

@[reassoc]
theorem forget_map_pushout_inl_markedLoc (Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.forget.map (pushout.inl _ _ : Y ⟶ markedLoc Y) =
      toLoc Y ≫ MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) := by
  have h := congrArg MarkedPresheaf.forget.map
    (pushout.condition (f := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y)
      (g := (MarkedPresheaf.flat atomMarking).map (toLoc Y)))
  rw [Functor.map_comp, Functor.map_comp] at h
  exact (Category.id_comp _).symm.trans h

end MarkedDiagSet

theorem coinductiveGenerators_le_trivialCofibrations (n : ℕ∞) :
    coinductiveGenerators.{u} n ≤
      (trivialCofibrations (MarkedDiagSet.Coinductive n)).inverseImage
        (MarkedDiagSet.toCoinductive n) := by
  intro X Y f hf
  exact ⟨coinductiveGenerators_le_monomorphisms n f hf,
    markedExactCylinder.anodyne_le_weakEquivalences _ (coinductiveGenerators_le_monomorphisms n) f
      (markedExactCylinder.le_anodyne _ f hf)⟩

theorem inductiveGenerators_le_trivialCofibrations (n : ℕ∞) :
    inductiveGenerators.{u} n ≤
      (trivialCofibrations (MarkedDiagSet.Inductive n)).inverseImage
        (MarkedDiagSet.toInductive n) := by
  intro X Y f hf
  exact ⟨inductiveGenerators_le_monomorphisms n f hf,
    markedExactCylinder.anodyne_le_weakEquivalences _ (inductiveGenerators_le_monomorphisms n) f
      (markedExactCylinder.le_anodyne _ f hf)⟩

theorem hasLiftingProperty_of_coinductiveGenerators (n : ℕ∞) {A B E F : MarkedDiagSet.{u}}
    {i : A ⟶ B} (hi : coinductiveGenerators n i) {p : E ⟶ F}
    (hp : fibrations (MarkedDiagSet.Coinductive n) ((MarkedDiagSet.toCoinductive n).map p)) :
    HasLiftingProperty i p :=
  ((trivialCofibrations_rlp (C := MarkedDiagSet.Coinductive n)).symm ▸ hp) _
    (coinductiveGenerators_le_trivialCofibrations n i hi)

theorem hasLiftingProperty_of_inductiveGenerators (n : ℕ∞) {A B E F : MarkedDiagSet.{u}}
    {i : A ⟶ B} (hi : inductiveGenerators n i) {p : E ⟶ F}
    (hp : fibrations (MarkedDiagSet.Inductive n) ((MarkedDiagSet.toInductive n).map p)) :
    HasLiftingProperty i p :=
  ((trivialCofibrations_rlp (C := MarkedDiagSet.Inductive n)).symm ▸ hp) _
    (inductiveGenerators_le_trivialCofibrations n i hi)

theorem yonedaEquiv_toWalkingEquivalence_comp_locCell_comp (Y : MarkedDiagSet.{u}) {U : Atom}
    (hU : 0 < U.dimension) {x : Y.underlying.obj (op U)} (hx : x ∈ Y.marked U) {P : DiagSet.{u}}
    (k : Loc.obj Y ⟶ P) :
    uliftYonedaEquiv (toWalkingEquivalence U hU ≫ locCell Y hU hx ≫ k) =
      (toLoc Y ≫ k).app (op U) x := by
  have h : uliftYonedaEquiv (toWalkingEquivalence U hU ≫ locCell Y hU hx ≫ k) =
      uliftYonedaEquiv (uliftYonedaEquiv.symm x ≫ toLoc Y ≫ k) :=
    congrArg uliftYonedaEquiv (toWalkingEquivalence_locCell_assoc Y hU hx k)
  rw [h, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

open MarkedDiagSet in
theorem hasLiftingProperty_pushout_inr_markedLoc (Y : MarkedDiagSet.{u}) {E B : MarkedDiagSet.{u}}
    (p : E ⟶ B) (hp : localizationGenerators.rlp p) :
    HasLiftingProperty
      (pushout.inr _ _ : (MarkedPresheaf.flat atomMarking).obj (Loc.obj Y) ⟶ markedLoc Y) p := by
  refine ⟨fun {t b} sq => ?_⟩
  have hw : MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p =
      MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
        MarkedPresheaf.forget.map b := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq.w]
  have hmarked : ∀ (U : Atom) (x : Y.underlying.obj (op U)), x ∈ Y.marked U →
      (toLoc Y ≫ MarkedPresheaf.forget.map t).app (op U) x ∈ E.marked U := by
    intro U x hx
    have hU : 0 < U.dimension := Y.markable U x hx
    let bot := markedWalkingEquivalenceHom U hU (locCell Y hU hx ≫
      MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
        MarkedPresheaf.forget.map b) (by
      rw [yonedaEquiv_toWalkingEquivalence_comp_locCell_comp]
      exact (congrArg (fun φ => φ.app (op U) x ∈ B.marked U)
        (forget_map_pushout_inl_markedLoc_assoc Y (MarkedPresheaf.forget.map b))).mp
        (MarkedPresheaf.map_mem_marked b (MarkedPresheaf.map_mem_marked _ hx)))
    let top := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ E).symm
      (locCell Y hU hx ≫ MarkedPresheaf.forget.map t)
    have := hp _ (MorphismProperty.ofHoms.mk (⟨U, hU⟩ : {U : Atom // 0 < U.dimension}))
    have sq' : CommSq top (flatToMarkedWalkingEquivalence U hU) p bot :=
      ⟨MarkedPresheaf.hom_ext (by
        rw [Functor.map_comp, Functor.map_comp]
        exact (Category.assoc _ _ _).trans ((congrArg (locCell Y hU hx ≫ ·) hw).trans
          (Category.id_comp _).symm))⟩
    have hl : MarkedPresheaf.forget.map sq'.lift = locCell Y hU hx ≫ MarkedPresheaf.forget.map t :=
      (Category.id_comp _).symm.trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq'.fac_left))
    have hm := MarkedPresheaf.map_mem_marked sq'.lift
      ((MarkedPresheaf.mem_marked_ofMarking _ _ U _).2
        (Or.inr ⟨𝟙 U, inferInstance, rfl⟩) :
        (toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩ ∈ (markedWalkingEquivalence U hU).marked U)
    have hv : (MarkedPresheaf.forget.map sq'.lift).app (op U)
        ((toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩) =
        (toLoc Y ≫ MarkedPresheaf.forget.map t).app (op U) x :=
      (congrArg (fun φ => (toWalkingEquivalence U hU ≫ φ).app (op U) ⟨𝟙 U⟩) hl).trans
        (yonedaEquiv_toWalkingEquivalence_comp_locCell_comp Y hU hx _)
    exact hv ▸ hm
  let g : Y ⟶ E := MarkedPresheaf.homMk (toLoc Y ≫ MarkedPresheaf.forget.map t) hmarked
  have hg : (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y ≫ g =
      (MarkedPresheaf.flat atomMarking).map (toLoc Y) ≫ t :=
    MarkedPresheaf.hom_ext (by
      have e₁ : MarkedPresheaf.forget.map
          ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y ≫ g) =
          𝟙 Y.underlying ≫ (toLoc Y ≫ MarkedPresheaf.forget.map t) :=
        Functor.map_comp _ _ _
      have e₂ : MarkedPresheaf.forget.map ((MarkedPresheaf.flat atomMarking).map (toLoc Y) ≫ t) =
          toLoc Y ≫ MarkedPresheaf.forget.map t :=
        Functor.map_comp _ _ _
      exact e₁.trans ((Category.id_comp _).trans e₂.symm))
  refine CommSq.HasLift.mk' ⟨pushout.desc g t hg, pushout.inr_desc _ _ _, ?_⟩
  refine pushout.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (pushout.inl_desc g t hg))).trans
      (MarkedPresheaf.hom_ext ?_)
    have e₁ : MarkedPresheaf.forget.map (g ≫ p) =
        toLoc Y ≫ MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p :=
      (Functor.map_comp _ _ _).trans (Category.assoc _ _ _)
    have e₂ : MarkedPresheaf.forget.map ((pushout.inl _ _ : Y ⟶ markedLoc Y) ≫ b) =
        toLoc Y ≫ MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
          MarkedPresheaf.forget.map b :=
      (Functor.map_comp _ _ _).trans (forget_map_pushout_inl_markedLoc_assoc Y _)
    exact e₁.trans ((congrArg (toLoc Y ≫ ·) hw).trans e₂.symm)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) (pushout.inr_desc g t hg)).trans
      sq.w)

open MarkedDiagSet in
theorem hasLiftingProperty_pushout_inl_markedLoc (Y : MarkedDiagSet.{u}) {E B : MarkedDiagSet.{u}}
    (p : E ⟶ B) (hp : ∀ (U : Atom) (hU : 0 < U.dimension),
      HasLiftingProperty (markedAtomToMarkedWalkingEquivalence U hU) p) :
    HasLiftingProperty (pushout.inl _ _ : Y ⟶ markedLoc Y) p := by
  refine ⟨fun {t b} sq => ?_⟩
  have hw : MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p =
      toLoc Y ≫ MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
        MarkedPresheaf.forget.map b :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg MarkedPresheaf.forget.map sq.w).trans
      ((Functor.map_comp _ _ _).trans (forget_map_pushout_inl_markedLoc_assoc Y _)))
  let bot : ∀ (U : Atom) (hU : 0 < U.dimension) (x : Y.underlying.obj (op U)),
      x ∈ Y.marked U → (markedWalkingEquivalence U hU ⟶ B) := fun U hU x hx =>
    markedWalkingEquivalenceHom U hU (locCell Y hU hx ≫
      MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
        MarkedPresheaf.forget.map b) (by
      rw [yonedaEquiv_toWalkingEquivalence_comp_locCell_comp]
      exact (congrArg (fun φ => φ.app (op U) x ∈ B.marked U)
        (forget_map_pushout_inl_markedLoc_assoc Y (MarkedPresheaf.forget.map b))).mp
        (MarkedPresheaf.map_mem_marked b (MarkedPresheaf.map_mem_marked _ hx)))
  have hsq : ∀ (U : Atom) (hU : 0 < U.dimension) (x : Y.underlying.obj (op U))
      (hx : x ∈ Y.marked U), CommSq (markedAtomHom U hU x hx ≫ t)
        (markedAtomToMarkedWalkingEquivalence U hU) p (bot U hU x hx) := by
    intro U hU x hx
    refine ⟨MarkedPresheaf.hom_ext ?_⟩
    have e₁ : MarkedPresheaf.forget.map ((markedAtomHom U hU x hx ≫ t) ≫ p) =
        uliftYonedaEquiv.symm x ≫ MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p :=
      (Functor.map_comp _ _ _).trans ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans
        (Category.assoc _ _ _))
    have e₂ : MarkedPresheaf.forget.map (markedAtomToMarkedWalkingEquivalence U hU ≫
        bot U hU x hx) = toWalkingEquivalence U hU ≫ locCell Y hU hx ≫
          MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
            MarkedPresheaf.forget.map b :=
      Functor.map_comp _ _ _
    exact e₁.trans ((congrArg (uliftYonedaEquiv.symm x ≫ ·) hw).trans
      ((toWalkingEquivalence_locCell_assoc Y hU hx _).symm.trans e₂.symm))
  let leg : ∀ (U : Atom) (hU : 0 < U.dimension) (x : Y.underlying.obj (op U)),
      x ∈ Y.marked U → ¬ IsDegenerate Y.underlying x → (walkingEquivalence U hU ⟶ E.underlying) :=
    fun U hU x hx _ =>
      have := hp U hU
      MarkedPresheaf.forget.map (hsq U hU x hx).lift
  have hleg : ∀ U hU x hx hnd, toWalkingEquivalence U hU ≫ leg U hU x hx hnd =
      uliftYonedaEquiv.symm x ≫ MarkedPresheaf.forget.map t := fun U hU x hx _ => by
    have := hp U hU
    exact (MarkedPresheaf.forget.map_comp _ _).symm.trans
      ((congrArg MarkedPresheaf.forget.map (hsq U hU x hx).fac_left).trans
        (MarkedPresheaf.forget.map_comp _ _))
  have hlegp : ∀ U hU x hx hnd, leg U hU x hx hnd ≫ MarkedPresheaf.forget.map p =
      locCell Y hU hx ≫ MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
        MarkedPresheaf.forget.map b := fun U hU x hx _ => by
    have := hp U hU
    exact (MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg MarkedPresheaf.forget.map (hsq U hU x hx).fac_right)
  obtain ⟨hu, hhu, hcell⟩ := exists_toLoc_comp_eq Y _ leg hleg
  let h := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ E).symm hu
  have hh : (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y ≫ t =
      (MarkedPresheaf.flat atomMarking).map (toLoc Y) ≫ h :=
    MarkedPresheaf.hom_ext (by
      have e₁ : MarkedPresheaf.forget.map
          ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y ≫ t) =
          𝟙 Y.underlying ≫ MarkedPresheaf.forget.map t :=
        Functor.map_comp _ _ _
      have e₂ : MarkedPresheaf.forget.map ((MarkedPresheaf.flat atomMarking).map (toLoc Y) ≫ h) =
          toLoc Y ≫ hu :=
        Functor.map_comp _ _ _
      exact e₁.trans ((Category.id_comp _).trans (hhu.symm.trans e₂.symm)))
  refine CommSq.HasLift.mk' ⟨pushout.desc t h hh, pushout.inl_desc _ _ _, ?_⟩
  refine pushout.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) (pushout.inl_desc t h hh)).trans
      sq.w)
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (pushout.inr_desc t h hh))).trans
      (MarkedPresheaf.hom_ext ?_)
    have e₁ : MarkedPresheaf.forget.map (h ≫ p) = hu ≫ MarkedPresheaf.forget.map p :=
      Functor.map_comp _ _ _
    have e₂ : MarkedPresheaf.forget.map ((pushout.inr _ _ : _ ⟶ markedLoc Y) ≫ b) =
        MarkedPresheaf.forget.map (pushout.inr _ _ : _ ⟶ markedLoc Y) ≫
          MarkedPresheaf.forget.map b :=
      Functor.map_comp _ _ _
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    refine loc_hom_ext ?_ fun U hU x hx hnd => ?_
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hhu).trans hw)
    · obtain ⟨V, hV, y, hy, hnd', e, rfl, hloc⟩ := hcell U hU x hx hnd
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hloc).trans ?_)
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hlegp V hV y hy hnd')).trans ?_)
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (locCell_map_iso Y hV hU e hy hx).symm)

theorem weakEquivalence_pushout_inr_markedLoc (n : ℕ∞) (Y : MarkedDiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (pushout.inr _ _ :
      (MarkedPresheaf.flat atomMarking).obj (Loc.obj Y) ⟶ MarkedDiagSet.markedLoc Y)) :=
  weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
    hasLiftingProperty_pushout_inr_markedLoc Y p fun _ _ _ hi =>
      hasLiftingProperty_of_coinductiveGenerators n (Or.inr hi) hp.mem

section Lemma416

open MarkedDiagSet

noncomputable def markedAtomToMarkedLocalization (U : Atom) (hU : 0 < U.dimension) :
    markedAtom.{u} U hU ⟶ (topInversionData U hU).markedLocalization :=
  MarkedPresheaf.homMk (toWalkingEquivalence U hU) fun V x hx => by
    refine (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 ?_
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | hx
    · exact Or.inl (isDegenerate_app _ hx)
    · exact Or.inr ⟨0, ⟨⟩, @asIso _ _ _ _ (x.down : V ⟶ U) hx,
        (congrArg ((toWalkingEquivalence U hU).app (op V))
          (congrArg ULift.up (Category.comp_id x.down).symm)).trans
          (NatTrans.naturality_apply (toWalkingEquivalence U hU) x.down.op
            (⟨𝟙 U⟩ : (ball U).obj (op U)))⟩

noncomputable def markedWalkingEquivalenceToMarkedLocalization (U : Atom)
    (hU : 0 < U.dimension) :
    markedWalkingEquivalence.{u} U hU ⟶ (topInversionData U hU).markedLocalization :=
  MarkedPresheaf.homMk (𝟙 _) fun V x hx => by
    refine (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 ?_
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hx | ⟨g, hg, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨0, ⟨⟩, @asIso _ _ _ _ g hg,
        (congrArg ((toWalkingEquivalence U hU).app (op V))
          (congrArg ULift.up (Category.comp_id g).symm)).trans
          (NatTrans.naturality_apply (toWalkingEquivalence U hU) g.op
            (⟨𝟙 U⟩ : (ball U).obj (op U)))⟩

theorem hasLiftingProperty_markedAtomToMarkedLocalization (U : Atom)
    (hU : 0 < U.dimension) {E B : MarkedDiagSet.{u}} (p : E ⟶ B)
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p) :
    HasLiftingProperty (markedAtomToMarkedLocalization U hU) p := by
  refine ⟨fun {t b} sq => ?_⟩
  have hb : (topInversionData U hU).toLocalization ≫ MarkedPresheaf.forget.map b =
      MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p :=
    (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map
      sq.w).symm.trans (MarkedPresheaf.forget.map_comp _ _))
  have hg : ∀ i, (MarkedPresheaf.forget.map t).app _ ((topInversionData U hU).cell i) ∈
      E.marked _ := fun _ => MarkedPresheaf.map_mem_marked t
    ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (inferInstance : IsIso (𝟙 U))))
  obtain ⟨g', h₁, h₂, h₃⟩ := (topInversionData U hU).exists_localization_lift p hp
    (MarkedPresheaf.forget.map t) (MarkedPresheaf.forget.map b) hb hg fun n j =>
      MarkedPresheaf.map_mem_marked b ((topInversionData U hU).stageι_app_cell_mem_marked n j)
  exact CommSq.HasLift.mk' ⟨(topInversionData U hU).markedLocalizationHom g' h₃,
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₁),
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₂)⟩

namespace InversionData

variable {X : DiagSet.{u}} (A : InversionData X)

noncomputable def flatToMarkedLocalization :
    (MarkedPresheaf.flat atomMarking).obj A.localization ⟶ A.markedLocalization :=
  MarkedPresheaf.homMk (𝟙 _) fun V _ hx => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
    (Or.inl ((mem_marked_flat_iff_isDegenerate _ V _).1 hx))

noncomputable def stageWalkingEquivalence (n : ℕ) (j : (A.stage n).2.ι) :
    walkingEquivalence ((A.stage n).2.shape j) ((A.stage n).2.dim_pos j) ⟶ A.localization :=
  Hom.localizationMapFrom (C := A) (n := n)
    { map := uliftYonedaEquiv.symm ((A.stage n).2.cell j)
      index := fun _ => j
      iso := fun _ => Iso.refl _
      map_app_cell := fun _ => rfl }

theorem toWalkingEquivalence_stageWalkingEquivalence (n : ℕ) (j : (A.stage n).2.ι) :
    toWalkingEquivalence _ _ ≫ A.stageWalkingEquivalence n j =
      uliftYonedaEquiv.symm ((A.stage n).2.cell j) ≫ A.stageι n :=
  Hom.toLocalization_localizationMapFrom _

theorem yonedaEquiv_toWalkingEquivalence_comp_stageWalkingEquivalence_comp (n : ℕ)
    (j : (A.stage n).2.ι) {P : DiagSet.{u}} (k : A.localization ⟶ P) :
    uliftYonedaEquiv (toWalkingEquivalence _ _ ≫ A.stageWalkingEquivalence n j ≫ k) =
      (A.stageι n ≫ k).app _ ((A.stage n).2.cell j) := by
  have h : uliftYonedaEquiv (toWalkingEquivalence _ _ ≫ A.stageWalkingEquivalence n j ≫ k) =
      uliftYonedaEquiv (uliftYonedaEquiv.symm ((A.stage n).2.cell j) ≫ A.stageι n ≫ k) :=
    congrArg uliftYonedaEquiv ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ k)
      (A.toWalkingEquivalence_stageWalkingEquivalence n j)).trans (Category.assoc _ _ _)))
  rw [h, uliftYonedaEquiv_comp]
  exact congrArg ((A.stageι n ≫ k).app _) (uliftYonedaEquiv.apply_symm_apply _)

theorem hasLiftingProperty_flatToMarkedLocalization {E B : MarkedDiagSet.{u}} (p : E ⟶ B)
    (hp : localizationGenerators.rlp p) :
    HasLiftingProperty A.flatToMarkedLocalization p := by
  refine ⟨fun {t b} sq => ?_⟩
  have hw : MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p =
      MarkedPresheaf.forget.map b :=
    (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map
      sq.w).trans ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)))
  have hmarked : ∀ n j, (A.stageι n ≫ MarkedPresheaf.forget.map t).app _
      ((A.stage n).2.cell j) ∈ E.marked _ := by
    intro n j
    have hV := (A.stage n).2.dim_pos j
    let w := A.stageWalkingEquivalence n j
    let bot := MarkedDiagSet.markedWalkingEquivalenceHom _ hV (w ≫ MarkedPresheaf.forget.map b)
      ((congrArg (· ∈ B.marked _)
        (A.yonedaEquiv_toWalkingEquivalence_comp_stageWalkingEquivalence_comp n j _)).mpr
          (MarkedPresheaf.map_mem_marked b (A.stageι_app_cell_mem_marked n j)))
    let top := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ E).symm
      (w ≫ MarkedPresheaf.forget.map t)
    have := hp _ (MorphismProperty.ofHoms.mk
      (⟨_, hV⟩ : {U : Atom // 0 < U.dimension}))
    have sq' : CommSq top (flatToMarkedWalkingEquivalence _ hV) p bot :=
      ⟨MarkedPresheaf.hom_ext (by
        rw [Functor.map_comp, Functor.map_comp]
        exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hw).trans
          (Category.id_comp _).symm))⟩
    have hl : MarkedPresheaf.forget.map sq'.lift = w ≫ MarkedPresheaf.forget.map t :=
      (Category.id_comp _).symm.trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map sq'.fac_left))
    have hm := MarkedPresheaf.map_mem_marked sq'.lift
      ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ⟨𝟙 _, inferInstance, rfl⟩) :
        (toWalkingEquivalence _ hV).app _ ⟨𝟙 _⟩ ∈ (markedWalkingEquivalence _ hV).marked _)
    have hv : (MarkedPresheaf.forget.map sq'.lift).app _
        ((toWalkingEquivalence _ hV).app _ ⟨𝟙 _⟩) =
        (A.stageι n ≫ MarkedPresheaf.forget.map t).app _ ((A.stage n).2.cell j) :=
      (congrArg (fun φ => (toWalkingEquivalence _ hV ≫ φ).app _ ⟨𝟙 _⟩) hl).trans
        (A.yonedaEquiv_toWalkingEquivalence_comp_stageWalkingEquivalence_comp n j _)
    exact hv ▸ hm
  exact CommSq.HasLift.mk' ⟨A.markedLocalizationHom (MarkedPresheaf.forget.map t) hmarked,
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _)),
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans hw)⟩

end InversionData

open MarkedDiagSet in
theorem weakEquivalence_markedAtomToMarkedWalkingEquivalence (n : ℕ∞) (U : Atom)
    (hU : 0 < U.dimension) :
    WeakEquivalence ((toCoinductive.{u} n).map (markedAtomToMarkedWalkingEquivalence U hU)) := by
  let F := toCoinductive n
  let fg : (MarkedPresheaf.flat atomMarking).obj (walkingEquivalence U hU) ⟶
      (topInversionData U hU).markedLocalization :=
    (topInversionData U hU).flatToMarkedLocalization
  have h₁ : WeakEquivalence (F.map fg) :=
    weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
      (topInversionData U hU).hasLiftingProperty_flatToMarkedLocalization p fun _ _ _ hi =>
        hasLiftingProperty_of_coinductiveGenerators n (Or.inr hi) hp.mem
  have h₂ : WeakEquivalence (F.map (flatToMarkedWalkingEquivalence U hU)) :=
    weakEquivalence_of_hasLiftingProperty _ fun _ _ _ _ _ hp =>
      hasLiftingProperty_of_coinductiveGenerators n
        (Or.inr (MorphismProperty.ofHoms.mk (⟨U, hU⟩ : {U : Atom // 0 < U.dimension}))) hp.mem
  have h₃ : WeakEquivalence (F.map (markedWalkingEquivalenceToMarkedLocalization U hU)) :=
    weakEquivalence_of_precomp_of_fac (f := F.map (flatToMarkedWalkingEquivalence U hU))
      (fg := F.map fg) (MarkedPresheaf.hom_ext rfl)
  have h₄ : WeakEquivalence (F.map (markedAtomToMarkedLocalization U hU)) :=
    weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
      hasLiftingProperty_markedAtomToMarkedLocalization U hU p fun m =>
        hasLiftingProperty_of_coinductiveGenerators n
          (Or.inl (Or.inl (MorphismProperty.ofHoms.mk m))) hp.mem
  exact weakEquivalence_of_postcomp_of_fac
    (g := F.map (markedWalkingEquivalenceToMarkedLocalization U hU))
    (fg := F.map (markedAtomToMarkedLocalization U hU)) (MarkedPresheaf.hom_ext rfl)

theorem weakEquivalence_pushout_inl_markedLoc (n : ℕ∞) (Y : MarkedDiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      (pushout.inl _ _ : Y ⟶ MarkedDiagSet.markedLoc Y)) := by
  refine weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
    hasLiftingProperty_pushout_inl_markedLoc Y p fun U hU => ?_
  have h : trivialCofibrations (MarkedDiagSet.Coinductive n)
      ((MarkedDiagSet.toCoinductive n).map
        (MarkedDiagSet.markedAtomToMarkedWalkingEquivalence U hU)) :=
    ⟨(MarkedPresheaf.mono_iff _).2 ((topInversionData U hU).mono_toLocalization),
      (weakEquivalence_iff _).1 (weakEquivalence_markedAtomToMarkedWalkingEquivalence n U hU)⟩
  exact ((trivialCofibrations_rlp (C := MarkedDiagSet.Coinductive n)).symm ▸ hp.mem) _ h

end Lemma416

section Lemma415

private theorem isDegenerate_or_isIso_of_dimension_le {U V : Atom} (x : V ⟶ U)
    (h : U.dimension ≤ V.dimension) : IsDegenerate (ball.{u} U) (ULift.up x) ∨ IsIso x := by
  by_cases ht : x V.top = U.top
  · have hcol := isCollapseHom_of_apply_eq_top x ht
    by_cases hd : V.dimension = U.dimension
    · exact Or.inr (isIso_of_isCollapseHom_of_dimension_eq x hcol hd)
    · exact Or.inl (isDegenerate_ball_of_dimension_lt (by omega) ⟨x⟩)
  · refine Or.inl ?_
    have hlt : grade ℕ (x V.top) < grade ℕ U.top :=
      grade_strictMono (lt_of_le_of_ne (U.le_top (x V.top)) ht)
    rw [← U.dimension_eq] at hlt
    refine ⟨Atom.ofClosure U (x V.top), principalLift U (x V.top) x
      (apply_mem_closure_apply_top x), ⟨Atom.closureIncl U (x V.top)⟩,
      isCollapseHom_of_apply_eq_top _ (principalLift_apply_top x), fun hiso => ?_,
      congrArg ULift.up (principalLift_comp_closureIncl _ _ _ _)⟩
    have h₁ := Atom.dimension_eq_of_iso (asIso (principalLift U (x V.top) x
      (apply_mem_closure_apply_top x)))
    rw [Atom.dimension_ofClosure] at h₁
    omega

open MarkedDiagSet in
theorem hasLiftingProperty_markedAtomToInvertorPair (U : Atom) (hU : 0 < U.dimension)
    {E B : MarkedDiagSet.{u}} (p : E ⟶ B)
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p) :
    HasLiftingProperty (markedAtomToInvertorPair U hU) p := by
  refine ⟨fun {t b} sq => ?_⟩
  let A := topInversionData U hU
  have hβ : A.stepIncl ≫ MarkedPresheaf.forget.map b =
      MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p :=
    (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map
      sq.w).symm.trans (MarkedPresheaf.forget.map_comp _ _))
  have hmarked : ∀ {V : Atom} (x : diagram A.step V), U.dimension ≤ V.dimension →
      (MarkedPresheaf.forget.map b).app _ x ∈ B.marked _ := fun x hx =>
    MarkedPresheaf.map_mem_marked b ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      (Or.inr (by omega)))
  have hg : ∀ i, (MarkedPresheaf.forget.map t).app _ (A.cell i) ∈ E.marked _ := fun _ =>
    MarkedPresheaf.map_mem_marked t
      ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (inferInstance : IsIso (𝟙 U))))
  obtain ⟨g', h₁, h₂, h₃, h₄⟩ := A.exists_step_lift p hp (MarkedPresheaf.forget.map t)
    (MarkedPresheaf.forget.map b) hβ hg fun j =>
      hmarked _ ((A.dimension_next_shape j).symm ▸ Nat.le_succ _)
  have hinv : ∀ j, g'.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) ∈
      E.marked _ := fun j =>
    h₄ j (hmarked _ (A.dimension_inverseExtension_shape j).ge)
  refine CommSq.HasLift.mk' ⟨MarkedPresheaf.homMk g' fun V x hx => ?_,
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₁),
    MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans h₂)⟩
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hx with hd | hdim
  · exact E.mem_marked_of_isDegenerate (isDegenerate_app g' hd)
  have hdim' : U.dimension - 1 < V.dimension := hdim
  clear hx hdim
  rcases A.invertorExtension.cell_cases x with ⟨x', rfl⟩ | hd | ⟨j, f, rfl⟩
  · rcases A.inverseExtension.cell_cases x' with ⟨x'', rfl⟩ | hd | ⟨j, f, rfl⟩
    · have e : g'.app _ (A.invertorExtension.incl.app _ (A.inverseExtension.incl.app _ x'')) =
          (MarkedPresheaf.forget.map t).app _ x'' :=
        congrArg (fun φ => φ.app _ x'') h₁
      refine (congrArg (· ∈ E.marked V) e).mpr (MarkedPresheaf.map_mem_marked t
        ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ?_))
      exact isDegenerate_or_isIso_of_dimension_le (V := V) x''.down (by omega)
    · exact E.mem_marked_of_isDegenerate (isDegenerate_app g' (isDegenerate_app _ hd))
    · refine (congrArg (fun y => g'.app _ y ∈ E.marked V)
        (NatTrans.naturality_apply A.invertorExtension.incl f.hom.op _)).mpr ?_
      exact (congrArg (· ∈ E.marked V) (NatTrans.naturality_apply g' f.hom.op _)).mpr
        ((E.transport f _).1 (hinv j))
  · exact E.mem_marked_of_isDegenerate (isDegenerate_app g' hd)
  · exact (congrArg (· ∈ E.marked V) (NatTrans.naturality_apply g' f.hom.op _)).mpr
      ((E.transport f _).1 (h₃ j))

theorem weakEquivalence_markedAtomToInvertorPair_coinductive (n : ℕ∞) (U : Atom)
    (hU : 0 < U.dimension) :
    WeakEquivalence
      ((MarkedDiagSet.toCoinductive.{u} n).map (MarkedDiagSet.markedAtomToInvertorPair U hU)) :=
  weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
    hasLiftingProperty_markedAtomToInvertorPair U hU p fun m =>
      hasLiftingProperty_of_coinductiveGenerators n
        (Or.inl (Or.inl (MorphismProperty.ofHoms.mk m))) hp.mem

theorem weakEquivalence_markedAtomToInvertorPair_inductive (n : ℕ∞) (U : Atom)
    (hU : 0 < U.dimension) :
    WeakEquivalence
      ((MarkedDiagSet.toInductive.{u} n).map (MarkedDiagSet.markedAtomToInvertorPair U hU)) :=
  weakEquivalence_of_hasLiftingProperty _ fun _ _ p _ _ hp =>
    hasLiftingProperty_markedAtomToInvertorPair U hU p fun m =>
      hasLiftingProperty_of_inductiveGenerators n
        (Or.inl (Or.inl (MorphismProperty.ofHoms.mk m))) hp.mem

end Lemma415

end Atoms.Diagrammatic
