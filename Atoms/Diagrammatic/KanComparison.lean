import Atoms.Diagrammatic.InfinityEquivalence
import Atoms.Diagrammatic.InftyZeroCategory
import Atoms.Diagrammatic.Joyal.Comparison
import Atoms.Diagrammatic.Localization.Comparison
import Atoms.Homotopical.Simplicial.JoyalKan

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial Opposite
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

theorem kanFibration_toSSet_map {X Y : DiagSet.{u}} (p : X ⟶ Y)
    (hp : hornInclusions.rlp p) : SSet.modelCategoryQuillen.J.rlp (DiagSet.toSSet.map p) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hi
  obtain ⟨m, ⟨k⟩⟩ := hi
  rw [← sSetDiagSetAdj.hasLiftingProperty_iff]
  exact (HasLiftingProperty.iff_of_arrow_iso_left (toDiagSetHornArrowIso m k) p).2
    (hp _ (ofHoms.mk _))

open SSet.modelCategoryQuillen in
theorem kanComplex_toSSet_obj {X : DiagSet.{u}} (hX : IsInftyCategory 0 X) :
    (DiagSet.toSSet.obj X).KanComplex := by
  refine (isFibrant_iff_of_isTerminal (DiagSet.toSSet.map (terminal.from X))
    (terminalIsTerminal.isTerminalObj DiagSet.toSSet _)).2 ?_
  exact (SSet.modelCategoryQuillen.fibration_iff _).2
    (kanFibration_toSSet_map _ ((isHornFibrant_iff_isInftyCategory_zero X).2 hX))

theorem isInftyCategory_zero_of_kanComplex_toSSet_obj {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) [(DiagSet.toSSet.obj X).KanComplex] :
    IsInftyCategory 0 X := by
  refine ⟨hX.1, fun U x hU => ?_⟩
  by_cases hd : U.dimension = 1
  · obtain ⟨φ⟩ := (nonempty_iso_atomGlobe_of_dimension_eq_one hd).map
      fun i => i.symm ≪≫ atomSimplexOneIsoGlobe.symm
    let a : (DiagSet.toSSet.obj X) _⦋1⦌ := X.map φ.inv.op x
    have ha : IsEquivalence X a := isEquivalence_of_invStruct hX (SSet.Edge.mk' a)
      (SSet.nonempty_invStruct_of_kanComplex _ a)
    exact (isEquivalence_map_iso_iff φ.symm x).1 ha
  · exact hX.2 U x (by
      have hpos := Nat.cast_pos.1 hU
      exact_mod_cast (show 1 < U.dimension by omega))

theorem kanComplex_toSSet_obj_iff {X : DiagSet.{u}} (hX : IsInftyCategory 1 X) :
    (DiagSet.toSSet.obj X).KanComplex ↔ IsInftyCategory 0 X :=
  ⟨fun h => @isInftyCategory_zero_of_kanComplex_toSSet_obj X hX h,
    kanComplex_toSSet_obj⟩

theorem weakEquivalences_infty_zero_eq_hornWeak :
    reversibleCylinder.{u}.weakEquivalences (inftyGenerators 0) = hornWeak := by
  refine ExactCylinder.weakEquivalences_eq_of_isFibrant_iff _ _ _ _ fun X => ?_
  exact (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators 0)
    (inftyGenerators_le_monomorphisms 0) X).symm.trans
    ((isFibrant_infty_iff 0 X).trans
      (isFibrant_hornInclusions_iff_isInftyCategory_zero X).symm)

theorem weakEquivalences_infty_one_le_hornWeak :
    reversibleCylinder.{u}.weakEquivalences (inftyGenerators 1) ≤ hornWeak := by
  rw [← weakEquivalences_infty_zero_eq_hornWeak]
  exact weakEquivalences_infty_antitone (by simp)

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem isQuillen_sSetDiagSetAdj_kan : sSetDiagSetAdj.{u}.IsQuillen := by
  refine sSetDiagSetAdj.isQuillen_of_fibrations_between_fibrant ?_ ?_
  · intro A B i hi
    have : Mono i := hi
    exact SSet.toDiagSet.map_mono i
  · intro X Y p hX hY hp
    exact (SSet.modelCategoryQuillen.fibration_iff _).2
      (kanFibration_toSSet_map p ((fibration_iff p).1 hp))

open SSet.modelCategoryJoyal in
private theorem exists_hornFibrant_homotopy_retract (K : SSet.{u}) [K.KanComplex] :
    ∃ Z : DiagSet.{u}, IsHornFibrant Z ∧
      ∃ (s : K ⟶ DiagSet.toSSet.obj Z) (r : DiagSet.toSSet.obj Z ⟶ K),
        joyalInterval.cylinder.Homotopic (s ≫ r) (𝟙 K) := by
  have : IsCofibrant K := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  let φ := factorizationData (trivialCofibrations (DiagSet.Infty 1))
    (fibrations (DiagSet.Infty 1)) (terminal.from (SSet.toDiagSetInfty.obj K))
  have : IsFibrant φ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    infer_instance
  let s : K ⟶ DiagSet.toSSet.obj φ.Z := DiagSet.Infty.sSetDiagSetAdj.homEquiv K φ.Z φ.i
  have hs : joyalInterval.{u}.cylinder.weakEquivalences SSet.innerHornInclusions s :=
    (weakEquivalence_iff s).1
      ((isQuillenEquivalence_sSetDiagSetAdj.weakEquivalence_iff φ.i).1 inferInstance)
  have hZ : joyalInterval.{u}.cylinder.IsFibrant SSet.innerHornInclusions
      (DiagSet.toSSet.obj φ.Z) :=
    (ExactCylinder.modelCategory.isFibrant_iff _ _ _ _).1
      ((isFibrant_iff_quasicategory _).2 (quasicategory_toSSet_obj φ.Z inferInstance))
  have : (DiagSet.toSSet.obj φ.Z).KanComplex := kanComplex_of_joyal_weakEquivalences hZ s hs
  obtain ⟨r, hsr, hrs⟩ := joyalInterval.cylinder.exists_homotopy_inverse_of_weakEquivalences
    SSet.innerHornInclusions (joyal_isFibrant_of_kanComplex K) hZ s hs
  exact ⟨φ.Z, (isHornFibrant_iff_isInftyCategory_zero _).2
    (isInftyCategory_zero_of_kanComplex_toSSet_obj (isInftyCategory_of_isFibrant 1 _
      inferInstance)), s, r, hsr⟩

open SSet.modelCategoryJoyal in
private theorem hornWeak_toDiagSet_map_joyal_contraction (K : SSet.{u}) :
    hornWeak (SSet.toDiagSet.map (joyalInterval.cylinder.contraction.app K)) := by
  have (W : SSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  have : WeakEquivalence (joyalInterval.cylinder.contraction.app K) :=
    (weakEquivalence_iff _).2 (joyalInterval.cylinder.contraction_mem_weakEquivalences _
      SSet.innerHornInclusions_le_monomorphisms K)
  exact weakEquivalences_infty_one_le_hornWeak _ ((weakEquivalence_iff _).1
    (isQuillen_sSetDiagSetAdj.weakEquivalence_map (joyalInterval.cylinder.contraction.app K)))

theorem kanWeak_of_hornWeak_toDiagSet_map {A B : SSet.{u}} (f : A ⟶ B)
    (hf : hornWeak (SSet.toDiagSet.map f)) : kanWeak f := by
  intro K hK
  have : SSet.KanComplex K := (isFibrant_bot_iff_kanComplex K).1 hK
  obtain ⟨Z, hZ, s, r, hsr⟩ := exists_hornFibrant_homotopy_retract K
  have h₀ := (isHornFibrant_iff_isInftyCategory_zero Z).1 hZ
  have : (DiagSet.toSSet.obj Z).KanComplex := kanComplex_toSSet_obj h₀
  have hR := joyal_isFibrant_of_kanComplex (DiagSet.toSSet.obj Z)
  have hG := (isFibrant_hornInclusions_iff Z).2 hZ
  let e (Y : SSet.{u}) :
      grayExactCylinder.HomotopyClasses (SSet.toDiagSet.obj Y) Z ≃
        joyalInterval.cylinder.HomotopyClasses Y (DiagSet.toSSet.obj Z) :=
    Quotient.congr (sSetDiagSetAdj.homEquiv Y Z) fun u v =>
      (ExactCylinder.homotopic_homEquiv_iff _ _ SSet.innerHornInclusions hornInclusions
        sSetDiagSetAdj (hornWeak_toDiagSet_map_joyal_contraction Y) hG hR u v).symm
  have he : e A ∘ grayExactCylinder.precompClasses (SSet.toDiagSet.map f) Z =
      joyalInterval.cylinder.precompClasses f (DiagSet.toSSet.obj Z) ∘ e B := by
    funext c
    induction c using Quotient.inductionOn with | h u => ?_
    exact congrArg (Quotient.mk _) (sSetDiagSetAdj.homEquiv_naturality_left f u)
  have hb : Function.Bijective
      (joyalInterval.cylinder.precompClasses f (DiagSet.toSSet.obj Z)) := by
    rw [← (e B).bijective.of_comp_iff, ← he]
    exact (e A).bijective.comp (hf Z hG)
  have hk := joyalInterval.cylinder.bijective_precompClasses_of_homotopy_retract f s r hsr hb
  let eK (Y : SSet.{u}) : joyalInterval.cylinder.HomotopyClasses Y K ≃
      simplicialCylinder.HomotopyClasses Y K :=
    Quotient.congr (Equiv.refl _) fun u v => ExactCylinder.homotopic_iff_of_isFibrant
      _ _ SSet.innerHornInclusions ⊥ (joyal_isFibrant_of_kanComplex K) hK u v
  have heK : eK A ∘ joyalInterval.cylinder.precompClasses f K =
      simplicialCylinder.precompClasses f K ∘ eK B := by
    funext c
    induction c using Quotient.inductionOn with | h u => rfl
  rw [← (eK B).bijective.of_comp_iff, ← heK]
  exact (eK A).bijective.comp hk

open DiagSet.modelCategoryCisinski in
theorem weakEquivalence_sSetDiagSetAdj_counit_app_kan (X : DiagSet.{u})
    (hX : IsHornFibrant X) : WeakEquivalence (sSetDiagSetAdj.{u}.counit.app X) := by
  have h₀ := (isHornFibrant_iff_isInftyCategory_zero X).1 hX
  have h₁ : IsInftyCategory 1 X := ⟨h₀.1, fun U x hU => h₀.2 U x (lt_trans (by simp) hU)⟩
  apply (weakEquivalence_iff _).2
  change infinityEquivalences (sSetDiagSetAdj.counit.app X)
  rw [← hornWeak_eq_infinityEquivalences]
  exact weakEquivalences_infty_one_le_hornWeak _ ((weakEquivalence_iff (C := DiagSet.Infty 1) _).1
    (weakEquivalence_sSetDiagSetAdj_counit_app X ((isFibrant_infty_iff 1 X).2 h₁)))

open SSet.modelCategoryQuillen DiagSet.modelCategoryCisinski in
theorem isQuillenEquivalence_sSetDiagSetAdj_kan : sSetDiagSetAdj.{u}.IsQuillenEquivalence := by
  have (W : SSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  refine isQuillen_sSetDiagSetAdj_kan.isQuillenEquivalence_iff.2 ⟨?_, ?_⟩
  · intro A B hA hB f hf
    exact (weakEquivalence_iff f).2 (kanWeak_of_hornWeak_toDiagSet_map f
      (hornWeak_eq_infinityEquivalences.symm ▸ (weakEquivalence_iff _).1 hf))
  · intro X hX B hB q hq hwq
    have := weakEquivalence_sSetDiagSetAdj_counit_app_kan X
      ((DiagSet.modelCategoryCisinski.isFibrant_iff X).1 hX)
    have := isQuillen_sSetDiagSetAdj_kan.weakEquivalence_map q
    infer_instance

end Atoms.Diagrammatic
