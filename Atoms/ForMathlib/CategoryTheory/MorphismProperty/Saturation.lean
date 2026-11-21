import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Basic
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits

namespace CategoryTheory.MorphismProperty

open Limits

universe w v u v' u'

variable {C : Type u} [Category.{v} C]

class IsCellularlyClosed (W : MorphismProperty C) : Prop where
  isStableUnderCobaseChange : W.IsStableUnderCobaseChange
  isStableUnderTransfiniteComposition :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w} W

attribute [instance] IsCellularlyClosed.isStableUnderCobaseChange
  IsCellularlyClosed.isStableUnderTransfiniteComposition

class IsSaturated (W : MorphismProperty C) : Prop extends IsCellularlyClosed.{w} W where
  isStableUnderRetracts : W.IsStableUnderRetracts

attribute [instance] IsSaturated.isStableUnderRetracts

instance isSaturated_llp (T : MorphismProperty C) : IsSaturated.{w} T.llp where
  isStableUnderCobaseChange := inferInstance
  isStableUnderRetracts := inferInstance
  isStableUnderTransfiniteComposition := inferInstance

theorem isSaturated_sInf (S : Set (MorphismProperty C)) (hS : ∀ P ∈ S, IsSaturated.{w} P) :
    IsSaturated.{w} (sInf S) where
  isStableUnderCobaseChange :=
    ⟨fun sq hf ↦ by
      rw [MorphismProperty.sInf_iff] at hf ⊢
      exact fun P hP ↦ (hS P hP).isStableUnderCobaseChange.of_isPushout sq (hf P hP)⟩
  isStableUnderRetracts :=
    ⟨fun hr hg ↦ by
      rw [MorphismProperty.sInf_iff] at hg ⊢
      exact fun P hP ↦ (hS P hP).isStableUnderRetracts.of_retract hr (hg P hP)⟩
  isStableUnderTransfiniteComposition :=
    ⟨fun J _ _ _ _ ↦ ⟨by
      intro X Y f hf
      rw [MorphismProperty.sInf_iff]
      intro P hP
      exact
        ((hS P hP).isStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape
          J).le f (MorphismProperty.transfiniteCompositionsOfShape_monotone J (sInf_le hP) f hf)⟩⟩

instance isSaturated_inf (W W' : MorphismProperty C) [IsSaturated.{w} W] [IsSaturated.{w} W'] :
    IsSaturated.{w} (W ⊓ W') := by
  rw [← sInf_pair]
  exact isSaturated_sInf _ (by rintro P (rfl | rfl) <;> infer_instance)

instance IsSaturated.inverseImage {D : Type u'} [Category.{v'} D] (K : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} K] (P : MorphismProperty D) [IsSaturated.{w} P] :
    IsSaturated.{w} (P.inverseImage K) where
  isStableUnderCobaseChange :=
    have := preservesSmallestColimits_of_preservesColimits K
    ⟨fun sq hf ↦ P.of_isPushout (sq.map K) hf⟩
  isStableUnderRetracts := inferInstance
  isStableUnderTransfiniteComposition :=
    ⟨fun J _ _ _ _ ↦
      have : PreservesWellOrderContinuousOfShape J K := ⟨fun _ _ ↦ inferInstance⟩
      ⟨fun _ _ f hf ↦ P.transfiniteCompositionsOfShape_le J _
        (transfiniteCompositionsOfShape_map_of_preserves J K f hf)⟩⟩

def saturation (W : MorphismProperty C) : MorphismProperty C :=
  sInf {P : MorphismProperty C | IsSaturated.{w} P ∧ W ≤ P}

theorem saturation_iff (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    saturation.{w} W f ↔ ∀ P : MorphismProperty C, IsSaturated.{w} P → W ≤ P → P f := by
  rw [saturation, MorphismProperty.sInf_iff]
  simp only [Set.mem_ofPred_eq, and_imp]

theorem le_saturation (W : MorphismProperty C) : W ≤ saturation.{w} W := by
  intro X Y f hf
  rw [saturation_iff]
  exact fun _ _ hWP ↦ hWP f hf

theorem saturation_le (W P : MorphismProperty C) [IsSaturated.{w} P] (h : W ≤ P) :
    saturation.{w} W ≤ P := by
  intro X Y f hf
  exact (saturation_iff W f).1 hf P inferInstance h

instance isSaturated_saturation (W : MorphismProperty C) :
    IsSaturated.{w} (saturation.{w} W) :=
  isSaturated_sInf _ fun _ hP ↦ hP.1

instance isStableUnderCobaseChange_monomorphisms_functor (J : Type u') [Category.{v'} J] :
    (monomorphisms (J ⥤ Type w)).IsStableUnderCobaseChange := by
  rw [← functorCategory_monomorphisms]
  infer_instance

instance isStableUnderTransfiniteComposition_monomorphisms_functor (J : Type u')
    [Category.{v'} J] : (monomorphisms (J ⥤ Type w)).IsStableUnderTransfiniteComposition.{w} :=
  ⟨fun _ _ _ _ _ ↦ inferInstance⟩

instance isStableUnderFilteredColimits_monomorphisms_functor (J : Type u') [Category.{v'} J] :
    (monomorphisms (J ⥤ Type w)).IsStableUnderFilteredColimits.{w, w} where
  isStableUnderColimitsOfShape K _ _ := by
    rw [← functorCategory_monomorphisms]
    infer_instance

instance isSaturated_monomorphisms [(monomorphisms C).IsStableUnderCobaseChange]
    [(monomorphisms C).IsStableUnderTransfiniteComposition.{w}] :
    IsSaturated.{w} (monomorphisms C) where
  isStableUnderCobaseChange := inferInstance
  isStableUnderRetracts := inferInstance
  isStableUnderTransfiniteComposition := inferInstance

section CellularModel

variable (C)

class HasCellularModel where
  cellularModel : MorphismProperty C
  isSmall_cellularModel : cellularModel.IsSmall.{v}
  saturation_cellularModel : saturation.{v} cellularModel = monomorphisms C

attribute [instance] HasCellularModel.isSmall_cellularModel

variable {C} [HasCellularModel C]

theorem cellularModel_le_monomorphisms :
    HasCellularModel.cellularModel (C := C) ≤ monomorphisms C :=
  HasCellularModel.saturation_cellularModel (C := C) ▸ le_saturation _

instance (priority := 100) HasCellularModel.isSaturated_monomorphisms :
    IsSaturated.{v} (monomorphisms C) :=
  HasCellularModel.saturation_cellularModel (C := C) ▸ isSaturated_saturation _

end CellularModel

def arrowImage (Φ : ∀ {K X : C}, (K ⟶ X) → Arrow C) (W : MorphismProperty C) :
    MorphismProperty C :=
  fun _ _ g ↦ ∃ (K X : C) (t : K ⟶ X), W t ∧ Φ t = Arrow.mk g

theorem arrowImage_mem (Φ : ∀ {K X : C}, (K ⟶ X) → Arrow C) {W : MorphismProperty C}
    {K X : C} {t : K ⟶ X} (ht : W t) : arrowImage Φ W (Φ t).hom :=
  ⟨K, X, t, ht, Arrow.mk_eq _⟩

theorem arrowImage_le (Φ : ∀ {K X : C}, (K ⟶ X) → Arrow C) {W P : MorphismProperty C}
    [P.RespectsIso] (h : ∀ (K X : C) (t : K ⟶ X), W t → P (Φ t).hom) : arrowImage Φ W ≤ P := by
  rintro _ _ g ⟨K, X, t, ht, e⟩
  exact (P.arrow_mk_iso_iff (eqToIso (Arrow.mk_eq (Φ t) ▸ e))).1 (h K X t ht)

theorem arrowImage_ofHoms (Φ : ∀ {K X : C}, (K ⟶ X) → Arrow C) {ι : Type*} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) : arrowImage Φ (ofHoms f) = ofHoms fun i ↦ (Φ (f i)).hom := by
  ext _ _ g
  rw [ofHoms_iff]
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, e⟩
    exact ⟨i, by rw [← e, Arrow.mk_eq]⟩
  · rintro ⟨i, e⟩
    exact ⟨_, _, f i, ⟨i⟩, by rw [e, Arrow.mk_eq]⟩

instance isSmall_arrowImage (Φ : ∀ {K X : C}, (K ⟶ X) → Arrow C) (W : MorphismProperty C)
    [IsSmall.{w} W] : IsSmall.{w} (arrowImage Φ W) := by
  obtain ⟨ι, A, B, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{w} W).1 inferInstance
  rw [arrowImage_ofHoms]
  infer_instance

section Transfer

variable {D : Type u'} [Category.{v} D]

def functorImage (F : C ⥤ D) (W : MorphismProperty C) : MorphismProperty D :=
  fun _ _ g ↦ ∃ (K X : C) (t : K ⟶ X), W t ∧ F.mapArrow.obj (Arrow.mk t) = Arrow.mk g

instance isSmall_functorImage (F : C ⥤ D) (W : MorphismProperty C) [W.IsSmall.{w}] :
    (functorImage F W).IsSmall.{w} where
  small_toSet := by
    refine small_of_surjective (f := fun t : W.toSet ↦
      (⟨F.mapArrow.obj t.1, ⟨_, _, t.1.hom, t.2, rfl⟩⟩ : (functorImage F W).toSet)) ?_
    rintro ⟨g, K, X, t, ht, e⟩
    exact ⟨⟨Arrow.mk t, ht⟩, Subtype.ext e⟩

@[instance_reducible]
def HasCellularModel.ofAdjunction [HasCellularModel C] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Full] [R.Faithful] [L.PreservesMonomorphisms] [R.PreservesMonomorphisms]
    [IsSaturated.{v} (monomorphisms D)] : HasCellularModel D where
  cellularModel := functorImage L (HasCellularModel.cellularModel (C := C))
  isSmall_cellularModel := inferInstance
  saturation_cellularModel := by
    refine le_antisymm (saturation_le _ _ ?_) fun X Y m hm ↦ ?_
    · rintro _ _ g ⟨K, X, t, ht, e⟩
      have : Mono t := cellularModel_le_monomorphisms t ht
      exact ((monomorphisms D).arrow_mk_iso_iff (eqToIso e)).1
        (inferInstanceAs (Mono (L.map t)))
    · have : Mono m := hm
      have : PreservesColimitsOfSize.{v, v} L := adj.leftAdjoint_preservesColimits
      have hRm : saturation.{v} (HasCellularModel.cellularModel (C := C)) (R.map m) := by
        rw [HasCellularModel.saturation_cellularModel]
        exact inferInstanceAs (Mono (R.map m))
      have hW : saturation.{v} (HasCellularModel.cellularModel (C := C)) ≤
          (saturation.{v} (functorImage L (HasCellularModel.cellularModel (C := C)))).inverseImage
            L :=
        saturation_le _ _ fun _ _ t ht ↦ le_saturation _ _ ⟨_, _, t, ht, rfl⟩
      have hLRm := hW _ hRm
      have h : L.map (R.map m) ≫ adj.counit.app Y = adj.counit.app X ≫ m :=
        adj.counit.naturality m
      have e : m = inv (adj.counit.app X) ≫ L.map (R.map m) ≫ adj.counit.app Y := by
        rw [h, IsIso.inv_hom_id_assoc]
      rw [e]
      exact comp_mem _ _ _ (isomorphisms_le_of_containsIdentities _ _ inferInstance)
        (comp_mem _ _ _ hLRm (isomorphisms_le_of_containsIdentities _ _ inferInstance))

theorem inverseImage_saturation_functor (E : C ≌ D) (W : MorphismProperty D) :
    (saturation.{w} W).inverseImage E.functor = saturation.{w} (functorImage E.inverse W) := by
  refine le_antisymm (fun X Y f hf ↦ ?_) (saturation_le _ _ ?_)
  · have hle :
      saturation.{w} W ≤ (saturation.{w} (functorImage E.inverse W)).inverseImage E.inverse :=
      saturation_le _ _ fun K L t ht ↦ le_saturation _ _ ⟨K, L, t, ht, rfl⟩
    exact (map_functor_map_inverse_iff E.symm _ f).1 (hle _ hf)
  · rintro _ _ g ⟨K, L, t, ht, e⟩
    refine (arrow_mk_iso_iff _ (eqToIso e)).1 ?_
    exact (map_functor_map_inverse_iff E _ t).2 (le_saturation W t ht)

end Transfer

end CategoryTheory.MorphismProperty
