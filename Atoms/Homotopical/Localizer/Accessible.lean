import Atoms.Homotopical.Localizer.EndpointClosure
import Atoms.Homotopical.Cylinder.Lawvere

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

theorem IsAccessibleALocalizer.exists_monomorphisms
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer.{w, v} V] :
    ∃ S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)), S.IsSmall.{max w v} ∧
      S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ∧ generatedALocalizer S = V := by
  obtain ⟨T, hTsmall, rfl⟩ := hV
  let F := fun {K X : Aᵒᵖ ⥤ Type (max w v)} (f : K ⟶ X) ↦
    factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp f
  let S := arrowImage (fun f ↦ Arrow.mk (F f).i) T
  refine ⟨S, isSmall_arrowImage _ T, arrowImage_le _ fun _ _ t _ ↦ (F t).hi,
    le_antisymm (generatedALocalizer_le ?_) (generatedALocalizer_le ?_)⟩
  · refine arrowImage_le _ fun _ _ t ht ↦ ?_
    refine (generatedALocalizer T).of_postcomp (F t).i (F t).p
      ((isALocalizer_generatedALocalizer T).rlp_monomorphisms_le _ (F t).hp) ?_
    rw [(F t).fac]
    exact le_generatedALocalizer T t ht
  · intro _ _ t ht
    rw [← (F t).fac]
    exact (generatedALocalizer S).comp_mem _ _
      (le_generatedALocalizer S _ (arrowImage_mem (fun f ↦ Arrow.mk (F f).i) ht))
      ((isALocalizer_generatedALocalizer S).rlp_monomorphisms_le _ (F t).hp)

theorem IsALocalizer.lawvereCylinder_endpoint_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsALocalizer V] (ε : Bool) (X : Aᵒᵖ ⥤ Type v) :
    V (((lawvereCylinder A).endpoint ε).app X) :=
  (hV.endpoint_mem_iff_contraction_mem (lawvereCylinder A) ε X).2
    (hV.rlp_monomorphisms_le _ (rlp_monomorphisms_lawvereCylinder_contraction A X))

theorem lawvereCylinder_weakEquivalences_eq (S : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [S.IsSmall.{v}] (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    (lawvereCylinder A).weakEquivalences S = generatedALocalizer S := by
  have := (lawvereCylinder A).isALocalizer_weakEquivalences S hS
  exact le_antisymm
    ((lawvereCylinder A).weakEquivalences_le_of_endpoint_mem S hS (le_generatedALocalizer S)
      IsALocalizer.lawvereCylinder_endpoint_mem)
    (generatedALocalizer_le (((lawvereCylinder A).le_anodyne S).trans
      ((lawvereCylinder A).anodyne_le_weakEquivalences S hS)))

theorem IsAccessibleALocalizer.exists_lawvereCylinder {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] :
    ∃ S : MorphismProperty (Aᵒᵖ ⥤ Type v), S.IsSmall.{v} ∧
      S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ∧
      (lawvereCylinder A).weakEquivalences S = V := by
  obtain ⟨S, hS, hmono, rfl⟩ := hV.exists_monomorphisms
  exact ⟨S, hS, hmono, lawvereCylinder_weakEquivalences_eq S hmono⟩

theorem rlp_monomorphisms_le_of_cylinderCompatibleWith (V : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [V.ContainsIdentities] [V.HasTwoOutOfThreeProperty] [V.IsStableUnderRetracts]
    (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (h : CylinderCompatibleWith (Aᵒᵖ ⥤ Type v) V 𝕀) :
    (monomorphisms (Aᵒᵖ ⥤ Type v)).rlp ≤ V := by
  intro X Y p hp
  obtain ⟨s, hsp⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨k, h₀, h₁, -⟩ := 𝕀.exists_homotopy_of_rlp_monomorphisms p hp s hsp
  have hε : ∀ ε, V ((𝕀.endpoint ε).app X) := fun ε =>
    V.of_postcomp _ _ (h X) (by rw [𝕀.endpoint_app_contraction_app]; exact V.id_mem X)
  have hk : V k := V.of_precomp _ _ (hε false) (h₀ ▸ V.id_mem X)
  have hps : V (p ≫ s) := h₁ ▸ V.comp_mem _ _ (hε true) hk
  refine V.of_retract ?_ hps
  exact
    { i := Arrow.homMk' (𝟙 X) s
      r := Arrow.homMk' (𝟙 X) p (by simp [hsp])
      retract := by ext <;> simp [hsp] }

theorem _root_.HomotopicalAlgebra.ExactCylinder.weakEquivalences_eq_of_contraction_mem
    (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    (hI : CylinderCompatibleWith (Aᵒᵖ ⥤ Type (max w v)) (generatedALocalizer S) 𝕀) :
    𝕀.weakEquivalences S = generatedALocalizer S := by
  refine le_antisymm (𝕀.weakEquivalences_le_of_endpoint_mem S hS (le_generatedALocalizer S)
    fun ε X ↦ (IsALocalizer.endpoint_mem_iff_contraction_mem 𝕀 ε X).2 (hI X)) ?_
  have := 𝕀.isALocalizer_weakEquivalences S hS
  exact generatedALocalizer_le ((𝕀.le_anodyne S).trans (𝕀.anodyne_le_weakEquivalences S hS))

theorem IsAccessibleALocalizer.exists_weakEquivalences_eq
    {V : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))} [hV : IsAccessibleALocalizer.{w, v} V]
    (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (hI : CylinderCompatibleWith (Aᵒᵖ ⥤ Type (max w v)) V 𝕀) :
    ∃ S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)), S.IsSmall.{max w v} ∧
      S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) ∧ 𝕀.weakEquivalences S = V := by
  obtain ⟨S, hsmall, hS, rfl⟩ := hV.exists_monomorphisms
  exact ⟨S, hsmall, hS, 𝕀.weakEquivalences_eq_of_contraction_mem S hS hI⟩

theorem IsAccessibleALocalizer.iff_exists_cylinder (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    IsAccessibleALocalizer V ↔
      ∃ (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
        (Aᵒᵖ ⥤ Type v)), S.IsSmall.{v} ∧
        S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ∧ 𝕀.weakEquivalences S = V := by
  refine ⟨fun hV ↦ ?_, ?_⟩
  · obtain ⟨S, hsmall, hS, h⟩ := hV.exists_lawvereCylinder
    exact ⟨lawvereCylinder A, S, hsmall, hS, h⟩
  · rintro ⟨𝕀, S, hsmall, hS, rfl⟩
    exact 𝕀.isAccessibleALocalizer_weakEquivalences S hS

end Atoms.Homotopical
