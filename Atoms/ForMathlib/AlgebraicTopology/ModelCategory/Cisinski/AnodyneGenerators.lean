import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Anodyne
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Leibniz
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra

universe w v u

section Doubling

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasBinaryProducts C]

noncomputable abbrev doubleFunctor : C ⥤ C where
  obj X := X ⨿ X
  map f := coprod.map f f

noncomputable abbrev squareFunctor : C ⥤ C where
  obj X := X ⨯ X
  map f := prod.map f f

noncomputable def doubleAdjunction : doubleFunctor (C := C) ⊣ squareFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun f := prod.lift (coprod.inl ≫ f) (coprod.inr ≫ f)
          invFun g := coprod.desc (g ≫ prod.fst) (g ≫ prod.snd)
          left_inv f := by
            apply coprod.hom_ext
            · rw [coprod.inl_desc]; exact prod.lift_fst _ _
            · rw [coprod.inr_desc]; exact prod.lift_snd _ _
          right_inv g := by
            apply prod.hom_ext
            · rw [prod.lift_fst]; exact coprod.inl_desc _ _
            · rw [prod.lift_snd]; exact coprod.inr_desc _ _ }
      homEquiv_naturality_left_symm _ _ := by apply coprod.hom_ext <;> simp
      homEquiv_naturality_right _ _ := by apply prod.hom_ext <;> simp }

end Doubling

namespace ExactCylinder

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

@[simps]
noncomputable def endpointsNatTrans (𝕀 : ExactCylinder.{v} C) :
    doubleFunctor ⟶ 𝕀.I where
  app := 𝕀.endpoints
  naturality _ _ f := (𝕀.endpoints_naturality f).symm

variable [HasPushouts C] [HasCellularModel C]

def anodyneGeneratorsStage (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty
    C) :
    ℕ → MorphismProperty C
  | 0 => S ⊔ ⨆ ε : Bool, arrowImage (fun i ↦ Arrow.mk (𝕀.endpointBox ε i))
    (HasCellularModel.cellularModel (C := C))
  | n + 1 => arrowImage (fun i ↦ Arrow.mk (𝕀.bothBox i)) (𝕀.anodyneGeneratorsStage S n)

def anodyneGenerators (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C) :
    MorphismProperty C :=
  ⨆ n, 𝕀.anodyneGeneratorsStage S n

variable (𝕀 : ExactCylinder.{v} C) (S : MorphismProperty C)

theorem anodyneGeneratorsStage_le (n : ℕ) :
    𝕀.anodyneGeneratorsStage S n ≤ 𝕀.anodyneGenerators S :=
  le_iSup (𝕀.anodyneGeneratorsStage S) n

theorem isSmall_anodyneGeneratorsStage [S.IsSmall.{v}] (n : ℕ) :
    (𝕀.anodyneGeneratorsStage S n).IsSmall.{v} := by
  induction n with
  | zero =>
    have (ε : Bool) := isSmall_arrowImage.{v} (fun i ↦ Arrow.mk (𝕀.endpointBox ε i))
      (HasCellularModel.cellularModel (C := C))
    exact isSmall_sup _ _
  | succ n ih => exact isSmall_arrowImage _ _

theorem isSmall_anodyneGenerators [S.IsSmall.{v}] : (𝕀.anodyneGenerators S).IsSmall.{v} := by
  have := 𝕀.isSmall_anodyneGeneratorsStage S
  exact inferInstanceAs (⨆ n, 𝕀.anodyneGeneratorsStage S n).IsSmall.{v}

theorem anodyneGeneratorsStage_le_monomorphisms [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C]
    (hS : S ≤ MorphismProperty.monomorphisms C) (n : ℕ) :
    𝕀.anodyneGeneratorsStage S n ≤ MorphismProperty.monomorphisms C := by
  induction n with
  | zero =>
    refine sup_le hS (iSup_le fun ε ↦ arrowImage_le _ fun K X t ht ↦ ?_)
    exact 𝕀.mono_endpointBox ε t (cellularModel_le_monomorphisms t ht)
  | succ n ih => exact arrowImage_le _ fun K X t ht ↦ 𝕀.mono_bothBox t (ih t ht)

theorem anodyneGenerators_le_monomorphisms [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.anodyneGenerators S ≤ MorphismProperty.monomorphisms C :=
  iSup_le (𝕀.anodyneGeneratorsStage_le_monomorphisms S hS)

omit [HasCellularModel C] in
theorem isSaturated_endpointBox_preimage [HasColimitsOfSize.{v, v} C] (ε : Bool)
    (P : MorphismProperty C)
    [IsSaturated.{v} P] : IsSaturated.{v} (NatTrans.leibnizPreimage (𝕀.endpoint ε) P) := by
  exact NatTrans.isSaturated_leibnizPreimage _ P

omit [HasCellularModel C] in
theorem isSaturated_bothBox_preimage [HasColimitsOfSize.{v, v} C] [HasBinaryProducts C]
    (P : MorphismProperty C)
    [IsSaturated.{v} P] : IsSaturated.{v} (NatTrans.leibnizPreimage 𝕀.endpointsNatTrans P) := by
  have : PreservesColimitsOfSize.{v, v} (doubleFunctor (C := C)) :=
    doubleAdjunction.leftAdjoint_preservesColimits
  exact NatTrans.isSaturated_leibnizPreimage _ P

theorem isAnodyneClass_saturation_anodyneGenerators [HasColimitsOfSize.{v, v} C]
    [HasBinaryProducts C] :
    IsAnodyneClass 𝕀 S (saturation.{v} (𝕀.anodyneGenerators S)) where
  isSaturated := inferInstance
  generators_le := (le_sup_left.trans (𝕀.anodyneGeneratorsStage_le S 0)).trans
    (le_saturation _)
  endpointBox_mem ε {_ _} i hi := by
    have := 𝕀.isSaturated_endpointBox_preimage ε (saturation.{v} (𝕀.anodyneGenerators S))
    refine saturation_le.{v} (HasCellularModel.cellularModel (C := C))
      (NatTrans.leibnizPreimage (𝕀.endpoint ε) (saturation.{v} (𝕀.anodyneGenerators S)))
      (fun K X t ht ↦ ?_) i
      ((HasCellularModel.saturation_cellularModel (C := C)).symm ▸ hi : _)
    refine le_saturation _ _ (𝕀.anodyneGeneratorsStage_le S 0 _ (Or.inr ?_))
    exact (MorphismProperty.iSup_iff _ _).2 ⟨ε, arrowImage_mem _ ht⟩
  bothBox_mem {_ _} i _ hi := by
    have := 𝕀.isSaturated_bothBox_preimage (saturation.{v} (𝕀.anodyneGenerators S))
    refine saturation_le.{v} (𝕀.anodyneGenerators S)
      (NatTrans.leibnizPreimage 𝕀.endpointsNatTrans (saturation.{v} (𝕀.anodyneGenerators S)))
      (fun K X t ht ↦ ?_) i hi
    obtain ⟨n, hn⟩ := (MorphismProperty.iSup_iff _ _).1 ht
    exact le_saturation _ _ (𝕀.anodyneGeneratorsStage_le S (n + 1) _ (arrowImage_mem _ hn))

theorem anodyneGeneratorsStage_le_anodyne [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C]
    (hS : S ≤ MorphismProperty.monomorphisms C) (n : ℕ) :
    𝕀.anodyneGeneratorsStage S n ≤ 𝕀.anodyne S := by
  have h := 𝕀.isAnodyneClass_anodyne S
  induction n with
  | zero =>
    refine sup_le (𝕀.le_anodyne S) (iSup_le fun ε ↦ arrowImage_le _ fun K X t ht ↦ ?_)
    exact h.endpointBox_mem ε t (cellularModel_le_monomorphisms t ht)
  | succ n ih =>
    exact arrowImage_le _ fun K X t ht ↦
      h.bothBox_mem t (𝕀.anodyneGeneratorsStage_le_monomorphisms S hS n t ht) (ih t ht)

theorem anodyne_eq_saturation_anodyneGenerators [HasPullbacks C] [FinitaryPreExtensive C]
    [HasEffectiveUnions C] [HasColimitsOfSize.{v, v} C]
    [HasBinaryProducts C]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.anodyne S = saturation.{v} (𝕀.anodyneGenerators S) :=
  le_antisymm (𝕀.anodyne_le S _ (𝕀.isAnodyneClass_saturation_anodyneGenerators S))
    (saturation_le _ _ (iSup_le (𝕀.anodyneGeneratorsStage_le_anodyne S hS)))

theorem anodyne_eq_llp_rlp [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [HasColimitsOfSize.{v, v} C]
    [HasBinaryProducts C] [IsLocallyPresentable.{v} C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.anodyne S = (𝕀.anodyneGenerators S).rlp.llp := by
  have := 𝕀.isSmall_anodyneGenerators S
  rw [𝕀.anodyne_eq_saturation_anodyneGenerators S hS, saturation_eq_llp_rlp]

theorem naiveFibrations_eq_rlp_anodyneGenerators [HasPullbacks C]
    [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [HasColimitsOfSize.{v, v} C] [HasBinaryProducts C]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    𝕀.naiveFibrations S = (𝕀.anodyneGenerators S).rlp := by
  rw [naiveFibrations, 𝕀.anodyne_eq_saturation_anodyneGenerators S hS, rlp_saturation]

theorem hasFunctorialFactorization_anodyne [HasPullbacks C]
    [FinitaryPreExtensive C] [HasEffectiveUnions C]
    [HasColimitsOfSize.{v, v} C] [HasBinaryProducts C] [IsLocallyPresentable.{v} C] [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms C) :
    HasFunctorialFactorization (𝕀.anodyne S) (𝕀.naiveFibrations S) := by
  have := 𝕀.isSmall_anodyneGenerators S
  rw [naiveFibrations, 𝕀.anodyne_eq_saturation_anodyneGenerators S hS, rlp_saturation]
  exact hasFunctorialFactorization_saturation _

end ExactCylinder

end HomotopicalAlgebra
