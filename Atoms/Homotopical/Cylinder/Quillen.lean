import Atoms.Homotopical.Cylinder.Induced
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A B : Type v} [SmallCategory A] [SmallCategory B] {u : A ⥤ B}
  {𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)} {𝕁 : ExactCylinder.{v} (Bᵒᵖ ⥤ Type v)}

namespace CylinderCompatible

variable (c : CylinderCompatible u 𝕀 𝕁) [c.lan.PreservesMonomorphisms]

theorem anodyne_le_inverseImage_trivialCofibrations {S : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    {T : MorphismProperty (Bᵒᵖ ⥤ Type v)} [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan) :
    𝕀.anodyne S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan := by
  have := 𝕁.isSaturated_trivialCofibrations T hT
  have := 𝕁.isALocalizer_weakEquivalences T hT
  have : PreservesColimitsOfSize.{v, v} c.lan := c.adj.leftAdjoint_preservesColimits
  have hJ := 𝕁.isAnodyneClass_trivialCofibrations T hT
  exact 𝕀.anodyne_le S _
    { isSaturated := IsSaturated.inverseImage c.lan _
      generators_le := hST
      endpointBox_mem := fun ε _ _ i hi ↦ by
        have : Mono i := hi
        exact ((𝕁.trivialCofibrations T).arrow_mk_iso_iff (c.endpointBoxArrowIso ε i)).2
          (hJ.endpointBox_mem ε _ (c.lan.map_mono i))
      bothBox_mem := fun i hi h ↦ by
        have : Mono i := hi
        exact ((𝕁.trivialCofibrations T).arrow_mk_iso_iff (c.bothBoxArrowIso i)).2
          (hJ.bothBox_mem _ (c.lan.map_mono i) h) }

theorem isFibrant_op_comp {S : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    {T : MorphismProperty (Bᵒᵖ ⥤ Type v)} [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan) {Z : Bᵒᵖ ⥤ Type v}
    (hZ : 𝕁.IsFibrant T Z) : 𝕀.IsFibrant S (u.op ⋙ Z) := by
  intro K L a ha
  have h := (𝕁.rlp_trivialCofibrations_terminal_from_iff T hT Z).2 hZ _
    (c.anodyne_le_inverseImage_trivialCofibrations hT hST a ha)
  have h' := (c.adj.hasLiftingProperty_iff a (terminal.from Z)).1 h
  have hterm : IsTerminal (u.op ⋙ ⊤_ (Bᵒᵖ ⥤ Type v)) :=
    IsTerminal.isTerminalObj ((Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type v)).obj u.op) _
      terminalIsTerminal
  let e : Arrow.mk (((Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type v)).obj u.op).map (terminal.from Z)) ≅
      Arrow.mk (terminal.from (u.op ⋙ Z)) :=
    Arrow.isoMk (Iso.refl _) (hterm.uniqueUpToIso terminalIsTerminal)
      (terminalIsTerminal.hom_ext _ _)
  exact (HasLiftingProperty.iff_of_arrow_iso_right a e).1 h'

omit [c.lan.PreservesMonomorphisms] in
private theorem map_contraction_mem_weakEquivalences {T : MorphismProperty (Bᵒᵖ ⥤ Type v)}
    [T.IsSmall.{v}] (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (Y : Aᵒᵖ ⥤ Type v) : 𝕁.weakEquivalences T (c.lan.map (𝕀.contraction.app Y)) := by
  rw [← c.contraction_comp Y]
  exact (𝕁.weakEquivalences T).comp_mem _ _
    (𝕁.isomorphisms_le_weakEquivalences T _ (MorphismProperty.isomorphisms.infer_property _))
    (𝕁.contraction_mem_weakEquivalences T hT _)

theorem weakEquivalences_le_inverseImage {S : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    {T : MorphismProperty (Bᵒᵖ ⥤ Type v)} [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan) :
    𝕀.weakEquivalences S ≤ (𝕁.weakEquivalences T).inverseImage c.lan :=
  ExactCylinder.map_mem_weakEquivalences 𝕀 𝕁 S T c.adj
    (c.map_contraction_mem_weakEquivalences hT) fun _ hZ ↦ c.isFibrant_op_comp hT hST hZ

theorem isQuillen (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (T : MorphismProperty (Bᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan) :
    letI := 𝕀.modelCategory S hS
    letI := 𝕁.modelCategory T hT
    c.adj.IsQuillen :=
  ExactCylinder.isQuillen_of_map_contraction 𝕀 𝕁 S T (𝕀.trivialCofibrationsSetGenerated S hS)
    (𝕁.trivialCofibrationsSetGenerated T hT) c.adj (c.map_contraction_mem_weakEquivalences hT)
    fun _ hZ ↦ c.isFibrant_op_comp hT hST hZ

theorem isQuillenEquivalence_iff (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (T : MorphismProperty (Bᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan) :
    letI := 𝕀.modelCategory S hS
    letI := 𝕁.modelCategory T hT
    c.adj.IsQuillenEquivalence ↔
      (𝕁.weakEquivalences T).inverseImage c.lan ≤ 𝕀.weakEquivalences S ∧
        ∀ Z : Bᵒᵖ ⥤ Type v, 𝕁.IsFibrant T Z → 𝕁.weakEquivalences T (c.adj.counit.app Z) := by
  let := 𝕀.modelCategory S hS
  let := 𝕁.modelCategory T hT
  have (X : Aᵒᵖ ⥤ Type v) : IsCofibrant X := by
    rw [isCofibrant_iff, cofibration_iff]
    exact MorphismProperty.monomorphisms.infer_property _
  rw [(c.isQuillen S hS T hT hST).isQuillenEquivalence_iff_of_isCofibrant]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun _ _ f hf ↦ (weakEquivalence_iff f).1 (h₁ f ((weakEquivalence_iff _).2 hf)),
      fun Z hZ ↦ ?_⟩
    have : IsFibrant Z := (ExactCylinder.modelCategory.isFibrant_iff 𝕁 T hT Z).2 hZ
    exact (weakEquivalence_iff _).1 (h₂ Z)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun f hf ↦ (weakEquivalence_iff f).2 (h₁ f ((weakEquivalence_iff _).1 hf)),
      fun Z hZ ↦ (weakEquivalence_iff _).2 (h₂ Z ?_)⟩
    exact (ExactCylinder.modelCategory.isFibrant_iff 𝕁 T hT Z).1 hZ

theorem isLocalization_of_counit (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (T : MorphismProperty (Bᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan)
    (hreflect : (𝕁.weakEquivalences T).inverseImage c.lan ≤ 𝕀.weakEquivalences S)
    (hε : ∀ Z : Bᵒᵖ ⥤ Type v, 𝕁.IsFibrant T Z → 𝕁.weakEquivalences T (c.adj.counit.app Z)) :
    (c.lan ⋙ (𝕁.weakEquivalences T).Q).IsLocalization (𝕀.weakEquivalences S) := by
  let := 𝕀.modelCategory S hS
  let := 𝕁.modelCategory T hT
  have hQ : c.adj.IsQuillenEquivalence :=
    (c.isQuillenEquivalence_iff S hS T hT hST).2 ⟨hreflect, hε⟩
  have (X : Aᵒᵖ ⥤ Type v) : IsCofibrant X := by
    rw [isCofibrant_iff, cofibration_iff]
    exact MorphismProperty.monomorphisms.infer_property _
  have : HasFunctorialFactorization (trivialCofibrations (Bᵒᵖ ⥤ Type v))
      (fibrations (Bᵒᵖ ⥤ Type v)) :=
    𝕁.hasFunctorialFactorization_trivialCofibrations T (𝕁.trivialCofibrationsSetGenerated T hT)
  exact hQ.isLocalization

theorem isLocalization_of_unit (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (T : MorphismProperty (Bᵒᵖ ⥤ Type v)) [T.IsSmall.{v}]
    (hT : T ≤ MorphismProperty.monomorphisms (Bᵒᵖ ⥤ Type v))
    (hST : S ≤ (𝕁.trivialCofibrations T).inverseImage c.lan)
    (hres : 𝕁.weakEquivalences T ≤ (𝕀.weakEquivalences S).inverseImage
      ((Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type v)).obj u.op))
    (hreflect : ∀ ⦃Z Z' : Bᵒᵖ ⥤ Type v⦄ (g : Z ⟶ Z'), 𝕁.IsFibrant T Z → 𝕁.IsFibrant T Z' →
      𝕀.weakEquivalences S (Functor.whiskerLeft u.op g) → 𝕁.weakEquivalences T g)
    (hη : ∀ X : Aᵒᵖ ⥤ Type v, 𝕀.weakEquivalences S (c.adj.unit.app X)) :
    (c.lan ⋙ (𝕁.weakEquivalences T).Q).IsLocalization (𝕀.weakEquivalences S) := by
  have := 𝕀.isALocalizer_weakEquivalences S hS
  have := 𝕁.isALocalizer_weakEquivalences T hT
  refine c.isLocalization_of_counit S hS T hT hST (fun X X' f hf ↦ ?_) fun Z hZ ↦ ?_
  · have h₁ := (𝕀.weakEquivalences S).comp_mem _ _ (hη X) (hres _ hf)
    have hnat : f ≫ c.adj.unit.app X' = c.adj.unit.app X ≫
        ((Functor.whiskeringLeft Aᵒᵖ Bᵒᵖ (Type v)).obj u.op).map (c.lan.map f) :=
      c.adj.unit.naturality f
    rw [← hnat] at h₁
    exact (𝕀.weakEquivalences S).of_postcomp f _ (hη X') h₁
  · obtain ⟨R, j, hj, hR⟩ := 𝕁.exists_anodyne_isFibrant T hT (c.lan.obj (u.op ⋙ Z))
    obtain ⟨r, hr⟩ := 𝕁.exists_fac_of_isFibrant T hZ hj (c.adj.counit.app Z)
    have hjW := 𝕁.anodyne_le_weakEquivalences T hT j hj
    have hε : 𝕀.weakEquivalences S (Functor.whiskerLeft u.op (c.adj.counit.app Z)) := by
      have htri : c.adj.unit.app (u.op ⋙ Z) ≫ Functor.whiskerLeft u.op (c.adj.counit.app Z) =
          𝟙 _ := c.adj.right_triangle_components Z
      refine (𝕀.weakEquivalences S).of_precomp (c.adj.unit.app (u.op ⋙ Z)) _ (hη _) ?_
      rw [htri]
      exact (𝕀.weakEquivalences S).id_mem _
    rw [← hr] at hε ⊢
    have hr' : 𝕀.weakEquivalences S (Functor.whiskerLeft u.op r) :=
      (𝕀.weakEquivalences S).of_precomp _ _ (hres _ hjW) hε
    exact (𝕁.weakEquivalences T).comp_mem _ _ hjW (hreflect r hR hZ hr')

end CylinderCompatible

end Atoms.Homotopical
