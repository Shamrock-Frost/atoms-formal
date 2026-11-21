import Atoms.Diagrammatic.Marked.Invertible
import Atoms.Diagrammatic.Marked.Lifting
import Atoms.Diagrammatic.Marked.ModelStructure

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Atoms.Diagrammatic.PastingDiagram
open Atoms.Homotopical (MarkedPresheaf)

universe u

namespace Atoms.Diagrammatic

def compositorHorns : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms fun U : {U : RoundShape // 0 < U.dimension} =>
    markedHornInclusion (compositorMarkedHorn U.1 U.2)

def invertorHorns : MorphismProperty MarkedDiagSet.{u} :=
  MorphismProperty.ofHoms fun p : {V : Atom // 0 < V.dimension} × Bool =>
    markedHornInclusion (invertorMarkedHorn p.1.1 p.2 p.1.2)

theorem compositorHorns_le_markedHorns : compositorHorns.{u} ≤ markedHorns := by
  rw [compositorHorns, ofHoms_le_iff]
  exact fun _ => MorphismProperty.ofHoms.mk _

theorem invertorHorns_le_markedHorns : invertorHorns.{u} ≤ markedHorns := by
  rw [invertorHorns, ofHoms_le_iff]
  exact fun _ => MorphismProperty.ofHoms.mk _

private theorem hasLiftingProperty_compositor_of_hasMarkedRLP {X : MarkedDiagSet.{u}}
    (hX : HasMarkedRLP compositorHorns X) (U : RoundShape) (hU : 0 < U.dimension) :
    HasLiftingProperty (markedHornInclusion (compositorMarkedHorn U hU)) (terminal.from X) :=
  hX _ (MorphismProperty.ofHoms.mk (⟨U, hU⟩ : {U : RoundShape // 0 < U.dimension}))

private theorem hasLiftingProperty_invertor_of_hasMarkedRLP {X : MarkedDiagSet.{u}}
    (hX : HasMarkedRLP invertorHorns X) (V : Atom) (ε : Bool) (hV : 0 < V.dimension) :
    HasLiftingProperty (markedHornInclusion (invertorMarkedHorn V ε hV)) (terminal.from X) :=
  hX _ (MorphismProperty.ofHoms.mk ((⟨V, hV⟩, ε) : {V : Atom // 0 < V.dimension} × Bool))

section InvertorPair

variable (U : Atom) (hU : 0 < U.dimension)

theorem isDegenerate_or_isIso_invertorPair {V : Atom}
    (hV : U.dimension ≤ V.dimension) (x : diagram.{u} (invertorPair U hU) V) :
    IsDegenerate _ x ∨ (∃ g : V ⟶ U, IsIso g ∧ (toInvertorPair U hU).app (op V) ⟨g⟩ = x) ∨
      (∃ (j : (topInversionData U hU).inverseExtension.ι)
        (g : V ⟶ (topInversionData U hU).inverseExtension.shape j), IsIso g ∧
        (invertorPair U hU).map g.op ((topInversionData U hU).invertorExtension.incl.app _
          ((topInversionData U hU).inverseExtension.cell j)) = x) ∨
      ∃ (j : (topInversionData U hU).next.ι) (g : V ⟶ (topInversionData U hU).next.shape j),
        IsIso g ∧ (invertorPair U hU).map g.op ((topInversionData U hU).next.cell j) = x := by
  let A := topInversionData U hU
  rcases A.invertorExtension.exists_incl_app_eq_or_exists_map_cell_eq x with
    ⟨y, rfl⟩ | ⟨j, g, hg, rfl⟩
  · rcases A.inverseExtension.exists_incl_app_eq_or_exists_map_cell_eq y with
      ⟨b, rfl⟩ | ⟨j, g, hg, rfl⟩
    · rcases isIso_or_isDegenerate_ball hV b with h | h
      · exact Or.inr (Or.inl ⟨b.down, h, rfl⟩)
      · exact Or.inl (isDegenerate_app (toInvertorPair U hU) h)
    · have hn : A.invertorExtension.incl.app (op V) (A.inverseExtension.extension.map g.op
          (A.inverseExtension.cell j)) = (invertorPair U hU).map g.op
            (A.invertorExtension.incl.app _ (A.inverseExtension.cell j)) :=
        NatTrans.naturality_apply A.invertorExtension.incl g.op _
      rcases isIso_or_isDegenerate_map_of_apply_top_eq g hg (A.inverseExtension.cell j) with
        h | h
      · exact Or.inr (Or.inr (Or.inl ⟨j, g, h, hn.symm⟩))
      · exact Or.inl (isDegenerate_app A.invertorExtension.incl h)
  · rcases isIso_or_isDegenerate_map_of_apply_top_eq g hg (A.invertorExtension.cell j) with
      h | h
    · exact Or.inr (Or.inr (Or.inr ⟨j, g, h, rfl⟩))
    · exact Or.inl h

theorem isEquivalence_app_invertorPair_of_lt {Y : DiagSet.{u}} (f : invertorPair U hU ⟶ Y)
    (hz : ∀ j, IsEquivalence Y (f.app _ ((topInversionData U hU).next.cell j))) {V : Atom}
    (hV : U.dimension < V.dimension) (x : diagram (invertorPair U hU) V) :
    IsEquivalence Y (f.app (op V) x) := by
  rcases isDegenerate_or_isIso_invertorPair U hU hV.le x with
    h | ⟨g, hg, rfl⟩ | ⟨j, g, hg, rfl⟩ | ⟨j, g, hg, rfl⟩
  · exact degenerate_isEquivalence Y _ (isDegenerate_app f h)
  · exact absurd (Atom.dimension_eq_of_iso (asIso g)) hV.ne'
  · exact absurd ((Atom.dimension_eq_of_iso (asIso g)).trans
      ((topInversionData U hU).dimension_inverseExtension_shape j)) hV.ne'
  · refine (congrArg (IsEquivalence Y) (NatTrans.naturality_apply f g.op _)).mpr ?_
    exact (isEquivalence_map_iso_iff (asIso g) _).2 (hz j)

theorem isEquivalence_app_invertorPair {Y : DiagSet.{u}} (f : invertorPair U hU ⟶ Y)
    (hz : ∀ j, IsEquivalence Y (f.app _ ((topInversionData U hU).next.cell j))) {V : Atom}
    (hV : U.dimension ≤ V.dimension) (x : diagram (invertorPair U hU) V) :
    IsEquivalence Y (f.app (op V) x) := by
  let A := topInversionData U hU
  obtain ⟨e, d, he, hd⟩ := A.exists_biInvData_step ⟨⟩
  let d₀ : BiInvData (Set.range d.invertor) e := { d with invertor_mem := fun α => ⟨α, rfl⟩ }
  have hsub : (fun d : RoundPastingDiagram _ => d.mapTo f) '' Set.range d.invertor ⊆
      equivalences Y := by
    rintro _ ⟨_, ⟨α, rfl⟩, rfl⟩
    exact mem_equivalences_of_equiv
      ((equiv_of_eq (ofCell_app f _)).trans ((hd α).2.mapTo f)) (hz (⟨⟩, α))
  let D := (d₀.mapTo f).mono hsub
  have hE : e.mapTo f ∈ equivalences Y :=
    (mem_equivalences_iff _).2 D.witness
  have hu : IsEquivalence Y (f.app (op U) ((toInvertorPair U hU).app (op U) ⟨𝟙 U⟩)) :=
    mem_equivalences_of_equiv ((he.mapTo f).trans (equiv_of_eq (ofCell_app f _).symm)) hE
  have hinv : ∀ α, IsEquivalence Y (f.app _
      (A.invertorExtension.incl.app _ (A.inverseExtension.cell (⟨⟩, α)))) := by
    intro α
    have hD : D.inverse α ∈ equivalences Y := by
      cases α
      exacts [D.leftInverse_mem hE, D.rightInverse_mem hE]
    exact mem_equivalences_of_equiv
      (((hd α).1.mapTo f).symm.trans (equiv_of_eq (ofCell_app f _).symm)) hD
  rcases isDegenerate_or_isIso_invertorPair U hU hV x with
    h | ⟨g, hg, rfl⟩ | ⟨⟨⟨⟩, α⟩, g, hg, rfl⟩ | ⟨j, g, hg, rfl⟩
  · exact degenerate_isEquivalence Y _ (isDegenerate_app f h)
  · have h : (toInvertorPair U hU).app (op V) ⟨g⟩ =
        (invertorPair U hU).map g.op ((toInvertorPair U hU).app (op U) ⟨𝟙 U⟩) :=
      (congrArg ((toInvertorPair U hU).app (op V))
        (congrArg ULift.up (Category.comp_id g).symm)).trans
        (NatTrans.naturality_apply (toInvertorPair U hU) g.op ⟨𝟙 U⟩)
    rw [h]
    refine (congrArg (IsEquivalence Y) (NatTrans.naturality_apply f g.op _)).mpr ?_
    exact (isEquivalence_map_iso_iff (asIso g) _).2 hu
  · refine (congrArg (IsEquivalence Y) (NatTrans.naturality_apply f g.op _)).mpr ?_
    exact (isEquivalence_map_iso_iff (asIso g) _).2 (hinv α)
  · refine (congrArg (IsEquivalence Y) (NatTrans.naturality_apply f g.op _)).mpr ?_
    exact (isEquivalence_map_iso_iff (asIso g) _).2 (hz j)

end InvertorPair

theorem hasMarkedRLP_of_natural {J : MorphismProperty MarkedDiagSet.{u}} {X : MarkedDiagSet.{u}}
    (hX : ∀ (U : Atom) (x : diagram X.underlying U),
      x ∈ X.marked U ↔ IsEquivalence X.underlying x)
    (hJ : HasMarkedRLP J (MarkedDiagSet.natural.obj X.underlying)) : HasMarkedRLP J X := by
  let φ : X ⟶ MarkedDiagSet.natural.obj X.underlying := MarkedPresheaf.homMk (𝟙 _)
    fun U x hx => (MarkedDiagSet.mem_marked_natural_iff _ _ _).2 ((hX U x).1 hx)
  let ψ : MarkedDiagSet.natural.obj X.underlying ⟶ X := MarkedPresheaf.homMk (𝟙 _)
    fun U x hx => (hX U x).2 ((MarkedDiagSet.mem_marked_natural_iff _ _ _).1 hx)
  refine hasMarkedRLP_iff.2 fun A B i hi q => ?_
  obtain ⟨F, hF⟩ := hasMarkedRLP_iff.1 hJ i hi (q ≫ φ)
  refine ⟨F ≫ ψ, ?_⟩
  rw [← Category.assoc, hF, Category.assoc]
  refine MarkedPresheaf.hom_ext ?_
  rw [Functor.map_comp, Functor.map_comp]
  exact (congrArg (MarkedPresheaf.forget.map q ≫ ·) (Category.comp_id (𝟙 X.underlying))).trans
    (Category.comp_id _)

theorem hasMarkedRLP_localizationGenerators_iff (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP markedHorns X) :
    HasMarkedRLP localizationGenerators X ↔
      ∀ (U : Atom) (x : diagram X.underlying U), x ∈ X.marked U ↔ IsEquivalence X.underlying x := by
  constructor
  · intro hL U x
    refine ⟨marked_subset_equivalences X hX U x, fun hx => ?_⟩
    have hU : 0 < U.dimension :=
      Nat.pos_of_ne_zero fun h0 => not_isEquivalence_of_dimension_eq_zero x h0 hx
    have hx' : (uliftYonedaEquiv.symm x).app (op U) ⟨𝟙 U⟩ = x :=
      (uliftYonedaEquiv_apply _).symm.trans (uliftYonedaEquiv.apply_symm_apply x)
    obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff U hU
      (hasWeakComposites_of_hasMarkedRLP X hX) x).2 hx
    let q := ((MarkedPresheaf.flatForgetAdjunction atomMarking).homEquiv _ X).symm g
    obtain ⟨F, hF⟩ := hasMarkedRLP_iff.1 hL _
      (MorphismProperty.ofHoms.mk (⟨U, hU⟩ : {U : Atom // 0 < U.dimension})) q
    have hFq : MarkedPresheaf.forget.map F = g :=
      (Category.id_comp _).symm.trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
        (congrArg MarkedPresheaf.forget.map hF))
    have htop : (toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩ ∈
        (MarkedDiagSet.markedWalkingEquivalence U hU).marked U :=
      (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr ⟨𝟙 U, inferInstance, rfl⟩)
    have hm := MarkedPresheaf.map_mem_marked F htop
    rw [hFq] at hm
    have hval : g.app (op U) ((toWalkingEquivalence U hU).app (op U) ⟨𝟙 U⟩) = x :=
      (congrArg (fun φ => φ.app (op U) ⟨𝟙 U⟩) hg).trans hx'
    exact (congrArg (· ∈ X.marked U) hval).mp hm
  · intro hM
    refine hasMarkedRLP_iff.2 fun A B i hi q => ?_
    cases hi with
    | mk U =>
      refine ⟨MarkedPresheaf.homMk (MarkedPresheaf.forget.map q) fun V y hy => ?_,
        MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _))⟩
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | ⟨g, hg, rfl⟩
      · exact MarkedPresheaf.map_mem_marked q
          ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).2 hy)
      · refine (hM V _).2 ?_
        have h₁ : IsEquivalence (walkingEquivalence U.1 U.2)
            ((toWalkingEquivalence U.1 U.2).app (op U.1) ⟨𝟙 U.1⟩) :=
          (topInversionData U.1 U.2).isEquivalence_toLocalization ⟨⟩
        have h₂ : (toWalkingEquivalence U.1 U.2).app (op V) ⟨g⟩ =
            (walkingEquivalence U.1 U.2).map g.op
              ((toWalkingEquivalence U.1 U.2).app (op U.1) ⟨𝟙 U.1⟩) :=
          (congrArg ((toWalkingEquivalence U.1 U.2).app (op V))
            (congrArg ULift.up (Category.comp_id g).symm)).trans
            (NatTrans.naturality_apply (toWalkingEquivalence U.1 U.2) g.op ⟨𝟙 U.1⟩)
        rw [h₂]
        refine (congrArg (IsEquivalence _)
          (NatTrans.naturality_apply (MarkedPresheaf.forget.map q) g.op _)).mpr ?_
        exact (isEquivalence_map_iso_iff (asIso g) _).2 (h₁.map _)

theorem hasMarkedRLP_invertorGenerators_natural (Y : DiagSet.{u}) :
    HasMarkedRLP invertorGenerators (MarkedDiagSet.natural.obj Y) := by
  refine hasMarkedRLP_iff.2 fun A B i hi q => ?_
  cases hi with
  | mk U =>
    let f : invertorPair U.1 U.2 ⟶ Y := MarkedPresheaf.forget.map q
    have hz : ∀ j, IsEquivalence Y (f.app _ ((topInversionData U.1 U.2).next.cell j)) :=
      fun j => (MarkedDiagSet.mem_marked_natural_iff _ _ _).1 (MarkedPresheaf.map_mem_marked q
        ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (by
          rw [(topInversionData U.1 U.2).dimension_next_shape j]
          exact Nat.lt_succ_self _))))
    refine ⟨MarkedPresheaf.homMk f fun V y hy => ?_,
      MarkedPresheaf.hom_ext ((MarkedPresheaf.forget.map_comp _ _).trans (Category.id_comp _))⟩
    refine (MarkedDiagSet.mem_marked_natural_iff _ _ _).2 ?_
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | hy
    · exact degenerate_isEquivalence Y _ (isDegenerate_app f hy)
    · exact isEquivalence_app_invertorPair U.1 U.2 f hz (by have := U.2; omega) y

private theorem mem_marked_of_isEquivalence_of_forall_lt (X : MarkedDiagSet.{u})
    (hW : HasWeakComposites X.underlying) (hI : HasMarkedRLP invertorGenerators X) {U : Atom}
    {x : diagram X.underlying U} (hx : IsEquivalence X.underlying x)
    (h : ∀ (V : Atom) (y : diagram X.underlying V), U.dimension < V.dimension →
      IsEquivalence X.underlying y → y ∈ X.marked V) : x ∈ X.marked U := by
  have hU : 0 < U.dimension :=
    Nat.pos_of_ne_zero fun h0 => not_isEquivalence_of_dimension_eq_zero x h0 hx
  have hx' : (uliftYonedaEquiv.symm x).app (op U) ⟨𝟙 U⟩ = x :=
    (uliftYonedaEquiv_apply _).symm.trans (uliftYonedaEquiv.apply_symm_apply x)
  obtain ⟨g, hg, hz⟩ := (topInversionData U hU).exists_stepIncl_comp_eq hW (uliftYonedaEquiv.symm x)
    fun _ => (congrArg (IsEquivalence _) hx').mpr hx
  let q : MarkedDiagSet.markedAbove (invertorPair U hU) U.dimension ⟶ X :=
    MarkedPresheaf.homMk g fun V y hy => by
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy with hy | hy
      · exact X.mem_marked_of_isDegenerate (isDegenerate_app g hy)
      · exact h V _ hy (isEquivalence_app_invertorPair_of_lt U hU g hz hy y)
  obtain ⟨F, hF⟩ := hasMarkedRLP_iff.1 hI _
    (MorphismProperty.ofHoms.mk (⟨U, hU⟩ : {U : Atom // 0 < U.dimension})) q
  have hFq : MarkedPresheaf.forget.map F = g :=
    (Category.id_comp _).symm.trans ((MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg MarkedPresheaf.forget.map hF))
  have hu : (toInvertorPair U hU).app (op U) ⟨𝟙 U⟩ ∈
      (MarkedDiagSet.markedAbove (invertorPair U hU) (U.dimension - 1)).marked U :=
    (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (by omega))
  have hm := MarkedPresheaf.map_mem_marked F hu
  rw [hFq] at hm
  have hval : g.app (op U) ((toInvertorPair U hU).app (op U) ⟨𝟙 U⟩) = x :=
    (congrArg (fun φ => φ.app (op U) ⟨𝟙 U⟩) hg).trans hx'
  exact (congrArg (· ∈ X.marked U) hval).mp hm

theorem mem_marked_of_isEquivalence (n : ℕ) (X : MarkedDiagSet.{u})
    (hW : HasWeakComposites X.underlying) (hJ : HasMarkedRLP (markingGeneratorsAbove n) X)
    (hI : HasMarkedRLP invertorGenerators X) (U : Atom) (x : diagram X.underlying U)
    (hx : IsEquivalence X.underlying x) : x ∈ X.marked U := by
  suffices H : ∀ (k : ℕ) (V : Atom) (y : diagram X.underlying V), n + 1 ≤ V.dimension + k →
      IsEquivalence X.underlying y → y ∈ X.marked V from H (n + 1) U x (by omega) hx
  intro k
  induction k with
  | zero =>
    intro V y hV _
    exact (hasMarkedRLP_markingGeneratorsAbove_iff n X).1 hJ V y (by exact_mod_cast hV)
  | succ k ih =>
    intro V y hV hy
    exact mem_marked_of_isEquivalence_of_forall_lt X hW hI hy fun W z hW' hz =>
      ih W z (by omega) hz

theorem hasMarkedRLP_coinductiveGenerators_natural (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) :
    HasMarkedRLP (coinductiveGenerators n) (MarkedDiagSet.natural.obj X) := by
  have hHJ := (isInftyCategory_iff_natural_hasMarkedRLP n X).1 hX
  exact (hasMarkedRLP_sup _ _ _).2 ⟨hHJ, (hasMarkedRLP_localizationGenerators_iff _
    ((hasMarkedRLP_sup _ _ _).1 hHJ).1).2 fun U x => MarkedDiagSet.mem_marked_natural_iff X U x⟩

theorem hasMarkedRLP_coinductiveGenerators_iff (n : ℕ∞) (X : MarkedDiagSet.{u}) :
    HasMarkedRLP (coinductiveGenerators n) X ↔ IsInftyCategory n X.underlying ∧
      ∀ (U : Atom) (x : diagram X.underlying U), x ∈ X.marked U ↔ IsEquivalence X.underlying x := by
  constructor
  · intro h
    obtain ⟨hHJ, hL⟩ := (hasMarkedRLP_sup _ _ _).1 h
    exact ⟨isInftyCategory_of_hasMarkedRLP n X hHJ, (hasMarkedRLP_localizationGenerators_iff X
      ((hasMarkedRLP_sup _ _ _).1 hHJ).1).1 hL⟩
  · rintro ⟨hC, hM⟩
    exact hasMarkedRLP_of_natural hM (hasMarkedRLP_coinductiveGenerators_natural n hC)

theorem hasMarkedRLP_inductiveGenerators_natural (n : ℕ∞) {X : DiagSet.{u}}
    (hX : IsInftyCategory n X) :
    HasMarkedRLP (inductiveGenerators n) (MarkedDiagSet.natural.obj X) :=
  (hasMarkedRLP_sup _ _ _).2 ⟨(isInftyCategory_iff_natural_hasMarkedRLP n X).1 hX,
    hasMarkedRLP_invertorGenerators_natural X⟩

theorem hasMarkedRLP_inductiveGenerators_iff (n : ℕ) (X : MarkedDiagSet.{u}) :
    HasMarkedRLP (inductiveGenerators n) X ↔ IsInftyCategory n X.underlying ∧
      ∀ (U : Atom) (x : diagram X.underlying U), x ∈ X.marked U ↔ IsEquivalence X.underlying x := by
  constructor
  · intro h
    obtain ⟨hHJ, hI⟩ := (hasMarkedRLP_sup _ _ _).1 h
    obtain ⟨hH, hJ⟩ := (hasMarkedRLP_sup _ _ _).1 hHJ
    exact ⟨isInftyCategory_of_hasMarkedRLP n X hHJ, fun U x =>
      ⟨marked_subset_equivalences X hH U x, mem_marked_of_isEquivalence n X
        (hasWeakComposites_of_hasMarkedRLP X hH) hJ hI U x⟩⟩
  · rintro ⟨hC, hM⟩
    exact hasMarkedRLP_of_natural hM (hasMarkedRLP_inductiveGenerators_natural n hC)

theorem hasMarkedRLP_coinductiveGenerators_of_hasMarkedRLP (n : ℕ) (X : MarkedDiagSet.{u})
    (hX : HasMarkedRLP
      (compositorHorns ⊔ invertorHorns ⊔ markingGeneratorsAbove n ⊔ invertorGenerators) X) :
    HasMarkedRLP (coinductiveGenerators n) X := by
  obtain ⟨h₁, hI⟩ := (hasMarkedRLP_sup _ _ _).1 hX
  obtain ⟨h₂, hJ⟩ := (hasMarkedRLP_sup _ _ _).1 h₁
  obtain ⟨hC, hV⟩ := (hasMarkedRLP_sup _ _ _).1 h₂
  have hV' := hasLiftingProperty_invertor_of_hasMarkedRLP hV
  have hW := hasWeakComposites_of_hasLiftingProperty X
    (hasLiftingProperty_compositor_of_hasMarkedRLP hC) hV'
  have hM : ∀ (U : Atom) (x : diagram X.underlying U),
      x ∈ X.marked U ↔ IsEquivalence X.underlying x := fun U x =>
    ⟨isEquivalence_of_mem_marked X hV' U x, mem_marked_of_isEquivalence n X hW hJ hI U x⟩
  exact (hasMarkedRLP_coinductiveGenerators_iff n X).2 ⟨⟨hW, fun U x hn =>
    (hM U x).1 ((hasMarkedRLP_markingGeneratorsAbove_iff n X).1 hJ U x hn)⟩, hM⟩

end Atoms.Diagrammatic
