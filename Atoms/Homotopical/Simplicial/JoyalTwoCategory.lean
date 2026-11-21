import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoCategoryIso
import Atoms.ForMathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Atoms.Homotopical.Simplicial.CartesianMonoidal

open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
  CartesianMonoidalCategory

universe u

namespace SSet.modelCategoryJoyal

open Atoms.Homotopical

private lemma isFibrant_cylinder (X : SSet.{u}) [X.Quasicategory] :
    joyalInterval.{u}.cylinder.IsFibrant innerHornInclusions X :=
  (ExactCylinder.modelCategory.isFibrant_iff _ _ _ X).1
    ((isFibrant_iff_quasicategory X).2 inferInstance)

private lemma joyalPoint_eq (b : Bool) :
    joyalPoint.{u} b = toUnit (⊤_ SSet.{u}) ≫ coherentIsoVertex b := by
  rw [joyalPoint, toUnit_unique (toUnit (⊤_ SSet.{u}))
    ((terminalIsoIsTerminal SSet.stdSimplex.isTerminalObj₀).hom ≫ toUnit Δ[0]), Category.assoc]
  congr 1
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  cases b <;> rfl

theorem joyalInterval_cylinder_endpoint_app (b : Bool) (X : SSet.{u}) :
    (joyalInterval.{u}.cylinder.endpoint b).app X = (λ_ X).inv ≫ coherentIsoVertex b ▷ X := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · have h : ((λ_ X).inv ≫ coherentIsoVertex b ▷ X) ≫ fst coherentIso X =
        toUnit X ≫ coherentIsoVertex b := by
      rw [Category.assoc, whiskerRight_fst, leftUnitor_inv_fst_assoc]
    have h' : terminal.from X ≫ joyalPoint b = toUnit X ≫ coherentIsoVertex b := by
      rw [joyalPoint_eq, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit X)]
    exact (segmentEndpoint_app_fst _ _ X).trans (h'.trans h.symm)
  · have h : ((λ_ X).inv ≫ coherentIsoVertex b ▷ X) ≫ snd coherentIso X = 𝟙 X := by
      rw [Category.assoc, whiskerRight_snd, leftUnitor_inv_snd]
    exact (segmentEndpoint_app_snd _ _ X).trans h.symm

private lemma elementaryHomotopy_iff {X Y : SSet.{u}} (f g : X ⟶ Y) :
    joyalInterval.{u}.cylinder.ElementaryHomotopy f g ↔ ∃ H : coherentIso.{u} ⊗ X ⟶ Y,
      (λ_ X).inv ≫ coherentIsoVertex false ▷ X ≫ H = f ∧
      (λ_ X).inv ≫ coherentIsoVertex true ▷ X ≫ H = g := by
  have e (b : Bool) (H : coherentIso.{u} ⊗ X ⟶ Y) :
      (joyalInterval.{u}.cylinder.endpoint b).app X ≫ H =
        (λ_ X).inv ≫ coherentIsoVertex b ▷ X ≫ H :=
    (congrArg (· ≫ H) (joyalInterval_cylinder_endpoint_app b X)).trans (Category.assoc _ _ _)
  exact ⟨fun ⟨H, h₀, h₁⟩ ↦ ⟨H, (e false H).symm.trans h₀, (e true H).symm.trans h₁⟩,
    fun ⟨H, h₀, h₁⟩ ↦ ⟨H, (e false H).trans h₀, (e true H).trans h₁⟩⟩

theorem QCat.nonempty_iso_iff_homotopic {A B : QCat.{u}} (f g : A ⟶ B) :
    Nonempty (f ≅ g) ↔ joyalInterval.{u}.cylinder.Homotopic f.hom g.hom := by
  rw [SSet.QCat.nonempty_iso_iff_exists_coherentIso,
    joyalInterval.{u}.cylinder.homotopic_iff_elementaryHomotopy_of_isFibrant _
      (isFibrant_cylinder B.obj), elementaryHomotopy_iff]

theorem weakEquivalence_iff_exists_equivalence {A B : QCat.{u}} (u : A ⟶ B) :
    WeakEquivalence u.hom ↔ ∃ e : Bicategory.Equivalence A B, e.hom = u := by
  refine ⟨fun hu ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · obtain ⟨v, h₁, h₂⟩ := joyalInterval.{u}.cylinder.exists_homotopy_inverse_of_weakEquivalences
      innerHornInclusions (isFibrant_cylinder A.obj) (isFibrant_cylinder B.obj) u.hom
      ((weakEquivalence_iff _).1 hu)
    obtain ⟨η⟩ := (QCat.nonempty_iso_iff_homotopic (u ≫ ObjectProperty.homMk v) (𝟙 A)).2 h₁
    obtain ⟨ε⟩ := (QCat.nonempty_iso_iff_homotopic (ObjectProperty.homMk v ≫ u) (𝟙 B)).2 h₂
    exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit η.symm ε, rfl⟩
  · subst he
    exact (weakEquivalence_iff _).2 (joyalInterval.{u}.cylinder.weakEquivalences_of_homotopic _
      e.hom.hom e.inv.hom ((QCat.nonempty_iso_iff_homotopic _ _).1 ⟨e.unit.symm⟩)
      ((QCat.nonempty_iso_iff_homotopic _ _).1 ⟨e.counit⟩))

private noncomputable def cylinderSwapIso (Y T : SSet.{u}) :
    coherentIso.{u} ⊗ (Y ⊗ T) ≅ Y ⊗ (coherentIso.{u} ⊗ T) :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _) T ≪≫ α_ _ _ _

private lemma vertex_comp_cylinderSwapIso (b : Bool) (Y T : SSet.{u}) :
    (λ_ (Y ⊗ T)).inv ≫ coherentIsoVertex b ▷ (Y ⊗ T) ≫ (cylinderSwapIso Y T).hom =
      Y ◁ ((λ_ T).inv ≫ coherentIsoVertex b ▷ T) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [cylinderSwapIso]
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;> simp [cylinderSwapIso]

private lemma elementaryHomotopy_uncurry {T Y Z : SSet.{u}} {t₁ t₂ : T ⟶ (ihom Y).obj Z}
    (h : joyalInterval.{u}.cylinder.ElementaryHomotopy t₁ t₂) :
    joyalInterval.{u}.cylinder.ElementaryHomotopy (uncurry t₁) (uncurry t₂) := by
  obtain ⟨K, rfl, rfl⟩ := (elementaryHomotopy_iff _ _).1 h
  refine (elementaryHomotopy_iff _ _).2 ⟨(cylinderSwapIso Y T).hom ≫ uncurry K, ?_, ?_⟩ <;>
    rw [← Category.assoc (λ_ T).inv, uncurry_natural_left, ← vertex_comp_cylinderSwapIso]
  all_goals simp only [Category.assoc]

private lemma elementaryHomotopy_curry {T Y Z : SSet.{u}} {f₁ f₂ : Y ⊗ T ⟶ Z}
    (h : joyalInterval.{u}.cylinder.ElementaryHomotopy f₁ f₂) :
    joyalInterval.{u}.cylinder.ElementaryHomotopy (curry f₁) (curry f₂) := by
  obtain ⟨H, rfl, rfl⟩ := (elementaryHomotopy_iff _ _).1 h
  refine (elementaryHomotopy_iff _ _).2 ⟨curry ((cylinderSwapIso Y T).inv ≫ H), ?_, ?_⟩ <;>
    rw [← Category.assoc (λ_ T).inv, ← curry_natural_left, ← vertex_comp_cylinderSwapIso]
  all_goals simp only [Category.assoc, Iso.hom_inv_id_assoc]

private lemma homotopic_uncurry_iff {T Y Z : SSet.{u}} (t₁ t₂ : T ⟶ (ihom Y).obj Z) :
    joyalInterval.{u}.cylinder.Homotopic (uncurry t₁) (uncurry t₂) ↔
      joyalInterval.{u}.cylinder.Homotopic t₁ t₂ := by
  refine ⟨fun h ↦ ?_, ExactCylinder.Homotopic.map _ uncurry fun _ _ ↦ elementaryHomotopy_uncurry⟩
  simpa only [curry_uncurry] using
    ExactCylinder.Homotopic.map _ curry (fun _ _ ↦ elementaryHomotopy_curry) h

private lemma homotopic_uncurry'_iff {Y Z : SSet.{u}} (t₁ t₂ : 𝟙_ SSet.{u} ⟶ (ihom Y).obj Z) :
    joyalInterval.{u}.cylinder.Homotopic (uncurry' t₁) (uncurry' t₂) ↔
      joyalInterval.{u}.cylinder.Homotopic t₁ t₂ := by
  rw [← homotopic_uncurry_iff]
  refine ⟨fun h ↦ ?_, joyalInterval.{u}.cylinder.homotopic_precomp (ρ_ Y).inv⟩
  simpa only [uncurry', Iso.hom_inv_id_assoc] using
    joyalInterval.{u}.cylinder.homotopic_precomp (ρ_ Y).hom h

private lemma uncurry'_comp_pre_app {X Y Z : SSet.{u}} (u : X ⟶ Y)
    (t : 𝟙_ SSet.{u} ⟶ (ihom Y).obj Z) :
    uncurry' (t ≫ (pre u).app Z) = u ≫ uncurry' t := by
  rw [uncurry', uncurry', uncurry_pre_app, rightUnitor_inv_naturality_assoc]

private lemma weakEquivalence_pre_app {X Y : SSet.{u}} (u : X ⟶ Y) [WeakEquivalence u]
    (Z : SSet.{u}) [Z.Quasicategory] : WeakEquivalence ((pre u).app Z) := by
  have hT (T : SSet.{u}) :
      Function.Bijective (joyalInterval.{u}.cylinder.precompClasses (u ▷ T) Z) := by
    have : WeakEquivalence (u ▷ T) := by
      simpa only [tensorHom_id] using weakEquivalence_tensorHom u (𝟙 T)
    exact (weakEquivalence_iff _).1 this Z (isFibrant_cylinder Z)
  have surj {T : SSet.{u}} (s : T ⟶ (ihom X).obj Z) : ∃ t : T ⟶ (ihom Y).obj Z,
      joyalInterval.{u}.cylinder.Homotopic (t ≫ (pre u).app Z) s := by
    obtain ⟨c, hc⟩ := (hT T).2 (Quotient.mk _ (uncurry s))
    induction c using Quotient.inductionOn with | h g => ?_
    refine ⟨curry g, (homotopic_uncurry_iff _ _).1 ?_⟩
    rw [uncurry_pre_app, uncurry_curry]
    exact Quotient.exact hc
  have inj {T : SSet.{u}} (t₁ t₂ : T ⟶ (ihom Y).obj Z)
      (h : joyalInterval.{u}.cylinder.Homotopic (t₁ ≫ (pre u).app Z) (t₂ ≫ (pre u).app Z)) :
      joyalInterval.{u}.cylinder.Homotopic t₁ t₂ := by
    rw [← homotopic_uncurry_iff, uncurry_pre_app, uncurry_pre_app] at h
    exact (homotopic_uncurry_iff _ _).1 (Quotient.exact
      (@(hT T).1 (Quotient.mk _ (uncurry t₁)) (Quotient.mk _ (uncurry t₂)) (Quotient.sound h)))
  obtain ⟨w, hw⟩ := surj (𝟙 _)
  have hw' : joyalInterval.{u}.cylinder.Homotopic ((pre u).app Z ≫ w) (𝟙 _) := inj _ _ (by
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
      joyalInterval.{u}.cylinder.homotopic_precomp ((pre u).app Z) hw)
  exact (weakEquivalence_iff _).2
    (joyalInterval.{u}.cylinder.weakEquivalences_of_homotopic _ _ w hw' hw)

private lemma weakEquivalence_of_weakEquivalence_pre_app {X Y : SSet.{u}} (u : X ⟶ Y)
    (h : ∀ (Z : SSet.{u}) [Z.Quasicategory], WeakEquivalence ((pre u).app Z)) :
    WeakEquivalence u := by
  refine (weakEquivalence_iff _).2 fun (Z : SSet.{u}) hZ ↦ ?_
  have : Z.Quasicategory := (isFibrant_iff_quasicategory Z).1
    ((ExactCylinder.modelCategory.isFibrant_iff _ _ _ Z).2 hZ)
  obtain ⟨w, hPw, hwP⟩ := joyalInterval.{u}.cylinder.exists_homotopy_inverse_of_weakEquivalences
    innerHornInclusions (isFibrant_cylinder _) (isFibrant_cylinder _) _
    ((weakEquivalence_iff _).1 (h Z))
  refine ⟨fun c₁ c₂ hc ↦ ?_, fun c ↦ ?_⟩
  · induction c₁ using Quotient.inductionOn with | h g₁ => ?_
    induction c₂ using Quotient.inductionOn with | h g₂ => ?_
    have h₁ : joyalInterval.{u}.cylinder.Homotopic (u ≫ g₁) (u ≫ g₂) := Quotient.exact hc
    rw [← uncurry'_curry' g₁, ← uncurry'_curry' g₂, ← uncurry'_comp_pre_app,
      ← uncurry'_comp_pre_app, homotopic_uncurry'_iff] at h₁
    refine Quotient.sound ((homotopic_uncurry'_iff (curry' g₁) (curry' g₂)).2 ?_)
    have hr (t : 𝟙_ SSet.{u} ⟶ (ihom Y).obj Z) :
        joyalInterval.{u}.cylinder.Homotopic ((t ≫ (pre u).app Z) ≫ w) t := by
      simpa only [Category.assoc, Category.comp_id] using
        joyalInterval.{u}.cylinder.homotopic_precomp t hPw
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hr _))
      (Relation.EqvGen.trans _ _ _ (joyalInterval.{u}.cylinder.homotopic_comp h₁ w) (hr _))
  · induction c using Quotient.inductionOn with | h f => ?_
    refine ⟨Quotient.mk _ (uncurry' (curry' f ≫ w)), Quotient.sound
      (?_ : joyalInterval.{u}.cylinder.Homotopic (u ≫ uncurry' (curry' f ≫ w)) f)⟩
    rw [← uncurry'_comp_pre_app, ← uncurry'_curry' f, homotopic_uncurry'_iff, uncurry'_curry']
    simpa only [Category.assoc, Category.comp_id] using
      joyalInterval.{u}.cylinder.homotopic_precomp (curry' f) hwP

theorem weakEquivalence_iff_forall_exists_equivalence_pre {X Y : SSet.{u}} (u : X ⟶ Y) :
    WeakEquivalence u ↔
      ∀ B : QCat.{u}, ∃ e : Bicategory.Equivalence (QCat.ihomObj Y B) (QCat.ihomObj X B),
        e.hom = QCat.pre u B := by
  refine ⟨fun _ B ↦ (weakEquivalence_iff_exists_equivalence (QCat.pre u B)).1
    (weakEquivalence_pre_app u B.obj), fun h ↦ weakEquivalence_of_weakEquivalence_pre_app u
      fun Z _ ↦ (weakEquivalence_iff_exists_equivalence (QCat.pre u ⟨Z, inferInstance⟩)).2
        (h ⟨Z, inferInstance⟩)⟩

theorem exists_equivalence_inv_eq_of_weakEquivalence {A B : QCat.{u}} (u : A ⟶ B)
    [WeakEquivalence u.hom] : ∃ e : Bicategory.Equivalence B A, e.inv = u := by
  obtain ⟨e, rfl⟩ := (weakEquivalence_iff_exists_equivalence u).1 inferInstance
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm, rfl⟩

open Bicategory in
theorem exists_adjunction_of_weakEquivalence {A B : QCat.{u}} (u : A ⟶ B)
    [WeakEquivalence u.hom] : ∃ v : B ⟶ A, Nonempty (u ⊣ v) := by
  obtain ⟨e, rfl⟩ := (weakEquivalence_iff_exists_equivalence u).1 inferInstance
  exact ⟨e.inv, ⟨e.toAdjunction⟩⟩

open Bicategory in
theorem exists_adjunction_of_weakEquivalence' {A B : QCat.{u}} (u : A ⟶ B)
    [WeakEquivalence u.hom] : ∃ v : B ⟶ A, Nonempty (v ⊣ u) := by
  obtain ⟨e, rfl⟩ := exists_equivalence_inv_eq_of_weakEquivalence u
  exact ⟨e.hom, ⟨e.toAdjunction⟩⟩

end SSet.modelCategoryJoyal
