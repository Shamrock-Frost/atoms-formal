import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Monoidal
import Atoms.Homotopical.Localizer.WeakClass

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))

theorem map_mem_of_endpoint_mem (C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hC : C ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) [C.IsStableUnderComposition]
    (hcancel : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (u : X ⟶ Y) (w : Y ⟶ Z),
      Mono w → C u → C (u ≫ w) → C w)
    (hend : ∀ (ε : Bool) (X : Aᵒᵖ ⥤ Type (max w v)), C ((𝕀.endpoint ε).app X))
    {K X : Aᵒᵖ ⥤ Type (max w v)} {u : K ⟶ X} (hu : C u) : C (𝕀.I.map u) := by
  have : Mono u := hC u hu
  refine hcancel _ _ (𝕀.I.map_mono u) (hend false K) ?_
  rw [𝕀.endpoint_naturality]
  exact C.comp_mem _ _ hu (hend false X)

theorem anodyneGenerators_le_of_endpoint_mem (S C : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    (hC : C ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) [C.IsStableUnderCobaseChange]
    [C.IsStableUnderComposition] [C.RespectsIso]
    (hcancel : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type (max w v)⦄ (u : X ⟶ Y) (w : Y ⟶ Z),
      Mono w → C u → C (u ≫ w) → C w)
    (hend : ∀ (ε : Bool) (X : Aᵒᵖ ⥤ Type (max w v)), C ((𝕀.endpoint ε).app X)) (hS : S ≤ C) :
    𝕀.anodyneGenerators S ≤ C := by
  refine iSup_le fun n ↦ ?_
  induction n with
  | zero =>
    refine sup_le hS (iSup_le fun ε ↦ arrowImage_le _ fun K X t ht ↦ ?_)
    have hinr : C (pushout.inr ((𝕀.endpoint ε).app K) t) :=
      C.of_isPushout (IsPushout.of_hasPushout _ _).flip (hend ε K)
    refine hcancel _ (𝕀.endpointBox ε t)
      (𝕀.mono_endpointBox ε t (cellularGenerators_le_monomorphisms A t ht)) hinr ?_
    have e : pushout.inr _ _ ≫ 𝕀.endpointBox ε t = (𝕀.endpoint ε).app X :=
      pushout.inr_desc (𝕀.I.map t) ((𝕀.endpoint ε).app X) (𝕀.endpoint_naturality ε t)
    exact (congrArg (fun f : X ⟶ 𝕀.I.obj X ↦ C f) e).mpr (hend ε X)
  | succ n ih =>
    refine arrowImage_le _ fun K X u hu ↦ ?_
    have hu' : C u := ih u hu
    have hinl : C (pushout.inl (𝕀.endpoints K) (coprod.map u u)) :=
      C.of_isPushout (IsPushout.of_hasPushout _ _)
        (coprod_map_mem_of_isStableUnderCobaseChange C hu')
    refine hcancel _ (𝕀.bothBox u) (𝕀.mono_bothBox u (hC u hu')) hinl ?_
    convert 𝕀.map_mem_of_endpoint_mem C hC hcancel hend hu' using 1
    exact pushout.inl_desc (𝕀.I.map u) (𝕀.endpoints X) (𝕀.endpoints_naturality u)

end HomotopicalAlgebra.ExactCylinder

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

theorem IsALocalizer.endpoint_mem_iff_contraction_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))}
    [hV : IsALocalizer V] (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v))) (ε : Bool)
    (X : Aᵒᵖ ⥤ Type (max w v)) :
    V ((𝕀.endpoint ε).app X) ↔ V (𝕀.contraction.app X) := by
  have hid : V ((𝕀.endpoint ε).app X ≫ 𝕀.contraction.app X) := by
    rw [𝕀.endpoint_app_contraction_app]
    exact hV.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  exact ⟨fun h ↦ V.of_precomp _ _ h hid, fun h ↦ V.of_postcomp _ _ h hid⟩

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))

theorem weakEquivalences_le_of_endpoint_mem (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    [S.IsSmall.{max w v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [IsALocalizer V] (hSV : S ≤ V)
    (hend : ∀ (ε : Bool) (X : Aᵒᵖ ⥤ Type (max w v)), V ((𝕀.endpoint ε).app X)) :
    𝕀.weakEquivalences S ≤ V := by
  have hΛ : 𝕀.anodyneGenerators S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ⊓ V :=
    𝕀.anodyneGenerators_le_of_endpoint_mem S _ inf_le_left
      (fun ⦃_ _ _⦄ u w hw hu huw ↦ ⟨hw, V.of_precomp u w hu.2 huw.2⟩)
      (fun ε X ↦ ⟨𝕀.mono_endpoint ε X, hend ε X⟩) (fun _ _ f hf ↦ ⟨hS f hf, hSV f hf⟩)
  rw [𝕀.weakEquivalences_eq_generatedALocalizer S hS]
  exact generatedALocalizer_le (hΛ.trans inf_le_right)

theorem contraction_mem_weakEquivalences (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    [S.IsSmall.{max w v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    ∀ X : Aᵒᵖ ⥤ Type (max w v), 𝕀.weakEquivalences S (𝕀.contraction.app X) := fun X ↦
  ((𝕀.isALocalizer_weakEquivalences S hS).endpoint_mem_iff_contraction_mem 𝕀 false X).1
    (𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_endpoint S false X))

theorem isAnodyneClass_trivialCofibrations (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)))
    [S.IsSmall.{max w v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    IsAnodyneClass 𝕀 S (𝕀.trivialCofibrations S) where
  isSaturated := 𝕀.isSaturated_trivialCofibrations S hS
  generators_le _ _ f hf :=
    ⟨hS f hf, 𝕀.anodyne_le_weakEquivalences S hS f (𝕀.le_anodyne S f hf)⟩
  endpointBox_mem ε _ _ i hi := ⟨𝕀.mono_endpointBox ε i hi,
    𝕀.anodyne_le_weakEquivalences S hS _ ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε i hi)⟩
  bothBox_mem _ _ hC := 𝕀.trivialCofibrations_bothBox S hS _ hC

end HomotopicalAlgebra.ExactCylinder
