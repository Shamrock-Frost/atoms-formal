import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.Diagrammatic.Marked.Acyclic
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

noncomputable def DiagSet.Infty.flat (n : ℕ∞) : DiagSet.Infty.{u} n ⥤ MarkedDiagSet.Coinductive n :=
  MarkedPresheaf.flat atomMarking

def DiagSet.Infty.forget (n : ℕ∞) : MarkedDiagSet.Coinductive.{u} n ⥤ DiagSet.Infty n :=
  MarkedPresheaf.forget

noncomputable def DiagSet.Infty.flatForgetAdjunction (n : ℕ∞) :
    DiagSet.Infty.flat.{u} n ⊣ DiagSet.Infty.forget n :=
  MarkedPresheaf.flatForgetAdjunction atomMarking

theorem flat_map_endpoint_comp_pushout_inr (ε : Bool) (Y : DiagSet.{u}) :
    (MarkedPresheaf.flat atomMarking).map ((reversibleCylinder.{u}.endpoint ε).app Y) ≫
        (pushout.inr _ _ : (MarkedPresheaf.flat atomMarking).obj (Loc.obj (markedCylinder.obj
          ((MarkedPresheaf.flat atomMarking).obj Y))) ⟶ MarkedDiagSet.markedLoc _) =
      (markedExactCylinder.{u}.endpoint ε).app ((MarkedPresheaf.flat atomMarking).obj Y) ≫
        pushout.inl _ _ := by
  let Z := (MarkedPresheaf.flat atomMarking).obj Y
  let ι := (markedExactCylinder.{u}.endpoint ε).app Z
  have h₁ : (reversibleCylinder.{u}.endpoint ε).app Y =
      MarkedPresheaf.forget.map ι ≫ toLoc (markedCylinder.obj Z) :=
    toLoc_naturality ι
  have h₂ : (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Z = 𝟙 Z :=
    MarkedPresheaf.hom_ext rfl
  have h₃ := ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.naturality ι).trans
    ((congrArg (· ≫ ι) h₂).trans (Category.id_comp ι))
  refine (congrArg (fun f => (MarkedPresheaf.flat atomMarking).map f ≫ pushout.inr _ _) h₁).trans ?_
  refine (congrArg (· ≫ pushout.inr _ _) ((MarkedPresheaf.flat atomMarking).map_comp
    (MarkedPresheaf.forget.map ι) (toLoc (markedCylinder.obj Z)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((MarkedPresheaf.flat atomMarking).map (MarkedPresheaf.forget.map ι) ≫ ·)
    pushout.condition.symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pushout.inl _ _) h₃)

theorem weakEquivalence_flat_map_endpoint (n : ℕ∞) (ε : Bool) (Y : DiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      ((MarkedPresheaf.flat atomMarking).map ((reversibleCylinder.{u}.endpoint ε).app Y))) := by
  have hι : weakEquivalences (MarkedDiagSet.Coinductive n) ((MarkedDiagSet.toCoinductive n).map
      ((markedExactCylinder.{u}.endpoint ε).app ((MarkedPresheaf.flat atomMarking).obj Y))) :=
    markedExactCylinder.{u}.anodyne_le_weakEquivalences _
      (coinductiveGenerators_le_monomorphisms n) _ (markedExactCylinder.{u}.anodyne_endpoint _ ε _)
  have hφ := (weakEquivalence_iff _).1 (weakEquivalence_pushout_inl_markedLoc n
    (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj Y)))
  have hψ := (weakEquivalence_iff _).1 (weakEquivalence_pushout_inr_markedLoc n
    (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj Y)))
  refine (weakEquivalence_iff _).2 ((weakEquivalences _).of_postcomp _ _ hψ ?_)
  exact (congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f)
    (flat_map_endpoint_comp_pushout_inr ε Y)).mpr ((weakEquivalences _).comp_mem _ _ hι hφ)

section Compositor

variable (U : RoundShape) (hU : 0 < U.dimension)

private theorem compositorHornIso_symm_comp_corestrict :
    (RDCpx.isoOfIso (P := (compositorMarkedHorn U hU).hornRDC) (Q := U.rdc)
        (compositorHornIso U hU).symm).hom ≫
      RDCpx.ofInclusion (P := U.rdc) (Q := (compositorMarkedHorn U hU).hornRDC)
        (codRestrict (toMergerInputIncl U hU) (compositorMarkedHorn U hU).hornSet
          (inputEmb_mem_horn U hU)) = 𝟙 _ := by
  ext a
  exact congrArg Subtype.val (ConcreteCategory.congr_hom (compositorHornIso U hU).inv_hom_id a)

private theorem corestrict_comp_compositorHornMap {Y : DiagSet.{u}} (v : realize.obj U.rdc ⟶ Y) :
    realize.map (RDCpx.ofInclusion (P := U.rdc) (Q := (compositorMarkedHorn U hU).hornRDC)
      (codRestrict (toMergerInputIncl U hU) (compositorMarkedHorn U hU).hornSet
        (inputEmb_mem_horn U hU))) ≫ compositorHornMap U hU v = v :=
  (realize.map_comp_assoc _ _ _).symm.trans ((congrArg (fun t => realize.map t ≫ v)
    (inputEmb_comp_compositorHornIso U hU)).trans
      ((congrArg (· ≫ v) (realize.map_id _)).trans (Category.id_comp _)))

noncomputable def flatToMarkedMergerAtom :
    (MarkedPresheaf.flat atomMarking).obj (realize.{u}.obj U.rdc) ⟶
      MarkedDiagSet.markedAtom (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU) :=
  MarkedPresheaf.homMk (toMergerInclusion U hU) fun V _ hx =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inl (isDegenerate_app _ ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V _).1 hx)))

theorem hasLiftingProperty_flatToMarkedMergerAtom {E B : MarkedDiagSet.{u}} (p : E ⟶ B)
    (hp : ∀ m : MarkedHornData, HasLiftingProperty (markedHornInclusion m) p) :
    HasLiftingProperty (flatToMarkedMergerAtom U hU) p := by
  refine ⟨fun {t b} sq => ?_⟩
  have hw : MarkedPresheaf.forget.map t ≫ MarkedPresheaf.forget.map p =
      toMergerInclusion U hU ≫ MarkedPresheaf.forget.map b :=
    (MarkedPresheaf.forget.map_comp _ _).symm.trans ((congrArg MarkedPresheaf.forget.map
      sq.w).trans (MarkedPresheaf.forget.map_comp _ _))
  have hzB : uliftYonedaEquiv (MarkedPresheaf.forget.map b) ∈ B.marked (toMergerAtom U hU) :=
    MarkedPresheaf.map_mem_marked b ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      (Or.inr (inferInstance : IsIso (𝟙 (toMergerAtom U hU)))))
  have hincl : ∀ {Y : DiagSet.{u}} (z : diagram Y (toMergerAtom U hU)),
      realize.map (compositorMarkedHorn U hU).hornIncl ≫ (ofCell z).map =
        compositorHornMap U hU (toMergerInclusion U hU ≫ uliftYonedaEquiv.symm z) := fun z => by
    have hcomp : RDCpx.ofInclusion (P := U.rdc) (Q := (compositorMarkedHorn U hU).hornRDC)
        (codRestrict (toMergerInputIncl U hU) (compositorMarkedHorn U hU).hornSet
          (inputEmb_mem_horn U hU)) ≫ (compositorMarkedHorn U hU).hornIncl =
        RDCpx.ofInclusion (P := U.rdc) (Q := (toMergerAtom U hU).toMoleculeShape.rdc)
          (toMergerInputIncl U hU) := by
      ext x
      rfl
    have h₁ : (compositorMarkedHorn U hU).hornIncl =
        (RDCpx.isoOfIso (P := (compositorMarkedHorn U hU).hornRDC) (Q := U.rdc)
          (compositorHornIso U hU).symm).hom ≫
            RDCpx.ofInclusion (P := U.rdc) (Q := (toMergerAtom U hU).toMoleculeShape.rdc)
              (toMergerInputIncl U hU) :=
      (Category.id_comp _).symm.trans ((congrArg (· ≫ (compositorMarkedHorn U hU).hornIncl)
        (compositorHornIso_symm_comp_corestrict U hU).symm).trans ((Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) hcomp)))
    refine (congrArg (fun f => realize.map f ≫ (ofCell z).map) h₁).trans
      ((realize.map_comp_assoc _ _ _).trans ?_)
    exact congrArg (realize.map _ ≫ ·) (Category.assoc _ _ _).symm
  have := hp (compositorMarkedHorn U hU)
  obtain ⟨z, ⟨hz, hzm, -⟩, hpz⟩ := exists_fills_over_of_hasLiftingProperty
    (compositorMarkedHorn U hU) p (compositorHornMap U hU (MarkedPresheaf.forget.map t))
    (fun a ha => absurd ha (Set.notMem_empty a)) (uliftYonedaEquiv (MarkedPresheaf.forget.map b))
    ⟨(hincl _).trans ((congrArg (fun g => compositorHornMap U hU (toMergerInclusion U hU ≫ g))
      (uliftYonedaEquiv.symm_apply_apply (MarkedPresheaf.forget.map b))).trans
        ((congrArg (compositorHornMap U hU) hw.symm).trans (Category.assoc _ _ _).symm)),
      hzB, fun hs => by
      obtain ⟨y, hy⟩ := (toMergerAtom U hU).isMolecule.nonempty_faces LowerSet.mem_top (by
          rw [← (toMergerAtom U hU).dimension_eq]
          exact pos_dimension_toMergerAtom U hU) false
      exact absurd (hs hy) (Set.notMem_empty y)⟩
  refine CommSq.HasLift.mk' ⟨MarkedDiagSet.markedAtomHom _ _ z hzm,
    MarkedPresheaf.hom_ext ?_, MarkedPresheaf.hom_ext ?_⟩
  · exact (corestrict_comp_compositorHornMap U hU _).symm.trans ((congrArg (_ ≫ ·)
      ((hincl z).symm.trans hz)).trans (corestrict_comp_compositorHornMap U hU _))
  · refine (MarkedPresheaf.forget.map_comp _ _).trans (uliftYonedaEquiv.injective ?_)
    refine (uliftYonedaEquiv_comp _ _).trans ?_
    exact (congrArg _ (uliftYonedaEquiv.apply_symm_apply z)).trans hpz

end Compositor

theorem trivialCofibrations_flat_map_of_inftyGenerators (n : ℕ∞) {X Y : DiagSet.{u}} (i : X ⟶ Y)
    (hi : inftyGenerators n i) :
    trivialCofibrations (MarkedDiagSet.Coinductive n)
      ((MarkedDiagSet.toCoinductive n).map ((MarkedPresheaf.flat atomMarking).map i)) := by
  let F := MarkedDiagSet.toCoinductive n
  refine ⟨(MarkedPresheaf.mono_iff _).2 (inftyGenerators_le_monomorphisms n i hi), ?_⟩
  have hloc : ∀ (V : Atom) (hV : 0 < V.dimension), weakEquivalences
      (MarkedDiagSet.Coinductive n) (F.map (MarkedDiagSet.flatToMarkedWalkingEquivalence V hV)) :=
    fun V hV => (weakEquivalence_iff _).1 (weakEquivalence_of_hasLiftingProperty _
      fun _ _ _ _ _ hp => hasLiftingProperty_of_coinductiveGenerators n
        (Or.inr (MorphismProperty.ofHoms.mk (⟨V, hV⟩ : {U : Atom // 0 < U.dimension})))
          hp.mem)
  rcases hi with hi | hi
  · obtain ⟨U⟩ := hi
    have h₁ : weakEquivalences (MarkedDiagSet.Coinductive n)
        (F.map (flatToMarkedMergerAtom U.1 U.2)) :=
      (weakEquivalence_iff _).1 (weakEquivalence_of_hasLiftingProperty _
        fun _ _ p _ _ hp => hasLiftingProperty_flatToMarkedMergerAtom
          U.1 U.2 p fun m => hasLiftingProperty_of_coinductiveGenerators n
            (Or.inl (Or.inl (MorphismProperty.ofHoms.mk m))) hp.mem)
    have h₂ := (weakEquivalence_iff _).1 (weakEquivalence_markedAtomToMarkedWalkingEquivalence n
      (toMergerAtom U.1 U.2) (pos_dimension_toMergerAtom U.1 U.2))
    refine (weakEquivalences _).of_postcomp _ _ (hloc _ (pos_dimension_toMergerAtom U.1 U.2)) ?_
    have e : F.map ((MarkedPresheaf.flat atomMarking).map (toMergerInclusion U.1 U.2 ≫
        toWalkingEquivalence _ (pos_dimension_toMergerAtom U.1 U.2))) ≫
          F.map (MarkedDiagSet.flatToMarkedWalkingEquivalence _
            (pos_dimension_toMergerAtom U.1 U.2)) =
        F.map (flatToMarkedMergerAtom U.1 U.2) ≫
          F.map (MarkedDiagSet.markedAtomToMarkedWalkingEquivalence _ _) :=
      MarkedPresheaf.hom_ext rfl
    rw [e]
    exact (weakEquivalences _).comp_mem _ _ h₁ h₂
  · obtain ⟨U⟩ := hi
    have hU := Nat.cast_pos.1 (lt_of_le_of_lt (zero_le (a := n)) U.2)
    have h₁ : weakEquivalences (MarkedDiagSet.Coinductive n)
        (F.map (MarkedDiagSet.markingInclusion U.1 hU)) :=
      (weakEquivalence_iff _).1 (weakEquivalence_of_hasLiftingProperty _
        fun _ _ _ _ _ hp => hasLiftingProperty_of_coinductiveGenerators n
          (Or.inl (Or.inr (MorphismProperty.ofHoms.mk U))) hp.mem)
    have h₂ := (weakEquivalence_iff _).1
      (weakEquivalence_markedAtomToMarkedWalkingEquivalence n U.1 hU)
    refine (weakEquivalences _).of_postcomp _ _ (hloc U.1 hU) ?_
    have e : F.map ((MarkedPresheaf.flat atomMarking).map (toWalkingEquivalence U.1 hU)) ≫
          F.map (MarkedDiagSet.flatToMarkedWalkingEquivalence U.1 hU) =
        F.map (MarkedDiagSet.markingInclusion U.1 hU) ≫
          F.map (MarkedDiagSet.markedAtomToMarkedWalkingEquivalence U.1 hU) :=
      MarkedPresheaf.hom_ext rfl
    rw [e]
    exact (weakEquivalences _).comp_mem _ _ h₁ h₂

theorem trivialCofibrations_flat_map_of_anodyne (n : ℕ∞) {X Y : DiagSet.{u}} (i : X ⟶ Y)
    (hi : reversibleCylinder.{u}.anodyne (inftyGenerators n) i) :
    trivialCofibrations (MarkedDiagSet.Coinductive n)
      ((MarkedDiagSet.toCoinductive n).map ((MarkedPresheaf.flat atomMarking).map i)) := by
  let F := MarkedDiagSet.toCoinductive n
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat atomMarking ⋙ F) :=
    (DiagSet.Infty.flatForgetAdjunction n).leftAdjoint_preservesColimits
  have : IsSaturated.{u} (trivialCofibrations (MarkedDiagSet.Coinductive n)) := by
    rw [← fibrations_llp]
    infer_instance
  have hend : ∀ (ε : Bool) (Z : DiagSet.{u}), trivialCofibrations (MarkedDiagSet.Coinductive n)
      (F.map ((MarkedPresheaf.flat atomMarking).map ((reversibleCylinder.{u}.endpoint ε).app Z))) :=
    fun ε Z => ⟨(MarkedPresheaf.mono_iff _).2 (reversibleCylinder.{u}.mono_endpoint ε Z),
      (weakEquivalence_iff _).1 (weakEquivalence_flat_map_endpoint n ε Z)⟩
  refine reversibleCylinder.{u}.anodyne_le (inftyGenerators n)
    ((trivialCofibrations (MarkedDiagSet.Coinductive n)).inverseImage
      (MarkedPresheaf.flat atomMarking ⋙ F))
    { isSaturated := inferInstance
      generators_le := fun _ _ j hj => trivialCofibrations_flat_map_of_inftyGenerators n j hj
      endpointBox_mem := fun ε {K Z} j hj => ?_
      bothBox_mem := fun {K Z} j hj hjP => ?_ } i hi
  · refine ⟨(MarkedPresheaf.mono_iff _).2 (reversibleCylinder.{u}.mono_endpointBox ε j hj), ?_⟩
    have hinr := (trivialCofibrations (MarkedDiagSet.Coinductive n)).of_isPushout
      ((IsPushout.of_hasPushout ((reversibleCylinder.{u}.endpoint ε).app K) j).flip.map
        (MarkedPresheaf.flat atomMarking)) (hend ε K)
    refine (weakEquivalences _).of_precomp _ _ hinr.2 ?_
    have e := ((MarkedPresheaf.flat atomMarking).map_comp _ _).symm.trans
      (congrArg (MarkedPresheaf.flat atomMarking).map (reversibleCylinder.{u}.inr_endpointBox ε j))
    exact (congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f) e).mpr (hend ε Z).2
  · refine ⟨(MarkedPresheaf.mono_iff _).2 (reversibleCylinder.{u}.mono_bothBox j hj), ?_⟩
    have hcop : trivialCofibrations (MarkedDiagSet.Coinductive n)
        (F.map ((MarkedPresheaf.flat atomMarking).map (coprod.map j j))) := by
      rw [← fibrations_llp]
      intro E B p hp
      have hjp : HasLiftingProperty j (MarkedPresheaf.forget.map p) :=
        ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff j p).1
          (((fibrations_llp (C := MarkedDiagSet.Coinductive n)).symm ▸ hjP) p hp)
      have hW : (MorphismProperty.ofHoms fun _ : Unit => MarkedPresheaf.forget.map p).llp
          (coprod.map j j) :=
        MorphismProperty.colimMap
          (W := (MorphismProperty.ofHoms fun _ : Unit => MarkedPresheaf.forget.map p).llp)
          (mapPair (F := pair K K) (G := pair Z Z) j j) fun ⟨k⟩ => by
            cases k <;> exact fun _ _ q hq => by cases hq; exact hjp
      exact ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff _ p).2
        (hW _ (MorphismProperty.ofHoms.mk ()))
    have hinl := (trivialCofibrations (MarkedDiagSet.Coinductive n)).of_isPushout
      ((IsPushout.of_hasPushout (reversibleCylinder.{u}.endpoints K) (coprod.map j j)).map
        (MarkedPresheaf.flat atomMarking)) hcop
    have hnat :
        (MarkedPresheaf.flat atomMarking).map ((reversibleCylinder.{u}.endpoint false).app K) ≫
          (MarkedPresheaf.flat atomMarking).map (reversibleCylinder.{u}.I.map j) =
        (MarkedPresheaf.flat atomMarking).map j ≫
          (MarkedPresheaf.flat atomMarking).map ((reversibleCylinder.{u}.endpoint false).app Z) :=
      ((MarkedPresheaf.flat atomMarking).map_comp _ _).symm.trans
        ((congrArg (MarkedPresheaf.flat atomMarking).map
          ((reversibleCylinder.{u}.endpoint false).naturality j).symm).trans
            ((MarkedPresheaf.flat atomMarking).map_comp _ _))
    have hI : weakEquivalences (MarkedDiagSet.Coinductive n)
        (F.map ((MarkedPresheaf.flat atomMarking).map (reversibleCylinder.{u}.I.map j))) :=
      (weakEquivalences _).of_precomp _ _ (hend false K).2
        ((congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f) hnat).mpr
          ((weakEquivalences _).comp_mem _ _ hjP.2 (hend false Z).2))
    refine (weakEquivalences _).of_precomp _ _ hinl.2 ?_
    have e := ((MarkedPresheaf.flat atomMarking).map_comp _ _).symm.trans
      (congrArg (MarkedPresheaf.flat atomMarking).map (reversibleCylinder.{u}.inl_bothBox j))
    exact (congrArg (fun f => weakEquivalences (MarkedDiagSet.Coinductive n) f) e).mpr hI

theorem naiveFibrations_forget_map (n : ℕ∞) {E B : MarkedDiagSet.{u}} (p : E ⟶ B)
    (hp : fibrations (MarkedDiagSet.Coinductive n) ((MarkedDiagSet.toCoinductive n).map p)) :
    reversibleCylinder.{u}.naiveFibrations (inftyGenerators n) (MarkedPresheaf.forget.map p) :=
  fun _ _ i hi => ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff
    i p).1 (((fibrations_llp (C := MarkedDiagSet.Coinductive n)).symm ▸
      trivialCofibrations_flat_map_of_anodyne n i hi) _ hp)

theorem isFibrant_forget_obj (n : ℕ∞) (Y : MarkedDiagSet.Coinductive.{u} n) (hY : IsFibrant Y) :
    reversibleCylinder.{u}.IsFibrant (inftyGenerators n) (MarkedPresheaf.forget.obj Y) := by
  have hT := naiveFibrations_forget_map n (terminal.from (Y : MarkedDiagSet.{u}))
    ((fibration_iff _).1 ((isFibrant_iff Y).1 hY))
  let e : Arrow.mk (MarkedPresheaf.forget.map (terminal.from (Y : MarkedDiagSet.{u}))) ≅
      Arrow.mk (terminal.from (MarkedPresheaf.forget.obj Y)) :=
    Arrow.isoMk (Iso.refl _) (PreservesTerminal.iso MarkedPresheaf.forget.{u, 0})
      (terminal.hom_ext _ _)
  exact fun _ _ i hi =>
    have := hT i hi
    HasLiftingProperty.of_arrow_iso_right i e

theorem isQuillen_flatForgetAdjunction (n : ℕ∞) :
    (DiagSet.Infty.flatForgetAdjunction.{u} n).IsQuillen := by
  refine (DiagSet.Infty.flatForgetAdjunction n).isQuillen_of_fibrations_between_fibrant
    (fun _ _ f hf => (MarkedPresheaf.mono_iff _).2 hf) (fun X Y p _ hY hp => ?_)
  exact (fibration_iff _).2 (reversibleCylinder.{u}.rlp_trivialCofibrations_of_rlp_anodyne
    (inftyGenerators n) (inftyGenerators_le_monomorphisms n) _
    (naiveFibrations_forget_map n p ((fibration_iff p).1 hp)) (isFibrant_forget_obj n Y hY))

end Atoms.Diagrammatic
