import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.LeftProper

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ExactCylinder

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] (𝕀 : ExactCylinder.{v} C)
  {Γ : C ⥤ C} (adj : 𝕀.I ⊣ Γ)

def pathEndpoint (ε : Bool) : Γ ⟶ 𝟭 C :=
  conjugateEquiv adj Adjunction.id (𝕀.endpoint ε)

def pathConstant : 𝟭 C ⟶ Γ :=
  conjugateEquiv Adjunction.id adj 𝕀.contraction

@[reassoc]
theorem pathConstant_comp_pathEndpoint (ε : Bool) :
    𝕀.pathConstant adj ≫ 𝕀.pathEndpoint adj ε = 𝟙 (𝟭 C) := by
  rw [pathConstant, pathEndpoint, conjugateEquiv_comp, 𝕀.endpoint_contraction ε, conjugateEquiv_id]

@[reassoc]
theorem pathConstant_app_comp_pathEndpoint_app (ε : Bool) (X : C) :
    (𝕀.pathConstant adj).app X ≫ (𝕀.pathEndpoint adj ε).app X = 𝟙 X :=
  NatTrans.congr_app (𝕀.pathConstant_comp_pathEndpoint adj ε) X

theorem comp_pathEndpoint_app (ε : Bool) {A X : C} (f : A ⟶ Γ.obj X) :
    f ≫ (𝕀.pathEndpoint adj ε).app X = (𝕀.endpoint ε).app A ≫ (adj.homEquiv A X).symm f := by
  rw [pathEndpoint, conjugateEquiv_adjunction_id, Adjunction.homEquiv_counit,
    𝕀.endpoint_naturality_assoc]

noncomputable def pathEndpoints [HasBinaryProducts C] (X : C) : Γ.obj X ⟶ X ⨯ X :=
  prod.lift ((𝕀.pathEndpoint adj false).app X) ((𝕀.pathEndpoint adj true).app X)

variable [HasPushouts C] [HasTerminal C] (S : MorphismProperty C)

theorem rlp_monomorphisms_pathEndpoint_app {X : C} (hX : 𝕀.IsFibrant S X) (ε : Bool) :
    (monomorphisms C).rlp ((𝕀.pathEndpoint adj ε).app X) := by
  intro K L i hi
  have : Mono i := hi
  refine ⟨fun {a b} sq => ?_⟩
  have w : (𝕀.endpoint ε).app K ≫ (adj.homEquiv K X).symm a = i ≫ b := by
    rw [← comp_pathEndpoint_app, sq.w]
  obtain ⟨H, hH⟩ := 𝕀.exists_fac_of_isFibrant S hX
    ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem ε i this) (pushout.desc _ b w)
  refine CommSq.HasLift.mk' ⟨adj.homEquiv L X H, ?_, ?_⟩
  · rw [← adj.homEquiv_naturality_left, 𝕀.map_comp_eq_of_endpointBox_comp_eq ε i hH,
      Equiv.apply_symm_apply]
  · rw [comp_pathEndpoint_app, Equiv.symm_apply_apply,
      𝕀.endpoint_comp_eq_of_endpointBox_comp_eq ε i hH]

theorem naiveFibrations_pathEndpoints [HasBinaryProducts C] [HasPullbacks C]
    [FinitaryPreExtensive C] [HasEffectiveUnions C] [IsSaturated.{v} (monomorphisms C)]
    (hS : S ≤ monomorphisms C) {X : C} (hX : 𝕀.IsFibrant S X) :
    𝕀.naiveFibrations S (𝕀.pathEndpoints adj X) := by
  intro K L j hj
  have : Mono j := 𝕀.anodyne_le_monomorphisms S hS j hj
  refine ⟨fun {a b} sq => ?_⟩
  have hε (ε : Bool) : (𝕀.endpoint ε).app K ≫ (adj.homEquiv K X).symm a =
      j ≫ b ≫ cond ε prod.snd prod.fst := by
    rw [← comp_pathEndpoint_app, ← Category.assoc, ← sq.w, Category.assoc]
    cases ε
    · exact congrArg (a ≫ ·) (prod.lift_fst _ _).symm
    · exact congrArg (a ≫ ·) (prod.lift_snd _ _).symm
  have w : 𝕀.endpoints K ≫ (adj.homEquiv K X).symm a =
      coprod.map j j ≫ coprod.desc (b ≫ prod.fst) (b ≫ prod.snd) := by
    refine coprod.hom_ext ?_ ?_
    · rw [inl_endpoints_assoc, coprod.inl_map_assoc, coprod.inl_desc]
      exact hε false
    · rw [inr_endpoints_assoc, coprod.inr_map_assoc, coprod.inr_desc]
      exact hε true
  obtain ⟨H, hH⟩ := 𝕀.exists_fac_of_isFibrant S hX
    ((𝕀.isAnodyneClass_anodyne S).bothBox_mem j this hj) (pushout.desc _ _ w)
  have hH' := 𝕀.endpoints_comp_eq_of_bothBox_comp_eq j hH
  refine CommSq.HasLift.mk' ⟨adj.homEquiv L X H, ?_, ?_⟩
  · rw [← adj.homEquiv_naturality_left, 𝕀.map_comp_eq_of_bothBox_comp_eq j hH,
      Equiv.apply_symm_apply]
  · refine prod.hom_ext ?_ ?_
    · rw [pathEndpoints, Category.assoc, prod.lift_fst, comp_pathEndpoint_app,
        Equiv.symm_apply_apply, ← 𝕀.inl_endpoints, Category.assoc, hH', coprod.inl_desc]
    · rw [pathEndpoints, Category.assoc, prod.lift_snd, comp_pathEndpoint_app,
        Equiv.symm_apply_apply, ← 𝕀.inr_endpoints, Category.assoc, hH', coprod.inr_desc]

theorem isFibrant_prod [HasBinaryProducts C] {X Y : C} (hX : 𝕀.IsFibrant S X)
    (hY : 𝕀.IsFibrant S Y) : 𝕀.IsFibrant S (X ⨯ Y) := by
  intro K L j hj
  refine ⟨fun {a _} _ => ?_⟩
  obtain ⟨l, hl⟩ := 𝕀.exists_fac_of_isFibrant S hX hj (a ≫ prod.fst)
  obtain ⟨l', hl'⟩ := 𝕀.exists_fac_of_isFibrant S hY hj (a ≫ prod.snd)
  refine CommSq.HasLift.mk' ⟨prod.lift l l', ?_, terminal.hom_ext _ _⟩
  exact prod.hom_ext (by rw [Category.assoc, prod.lift_fst, hl])
    (by rw [Category.assoc, prod.lift_snd, hl'])

variable [HasInitial C] [HasPullbacks C] [FinitaryPreExtensive C] [HasEffectiveUnions C]
  [IsSaturated.{v} (monomorphisms C)]

theorem weakEquivalences_contraction_app (hS : S ≤ monomorphisms C) (X : C) :
    𝕀.weakEquivalences S (𝕀.contraction.app X) := by
  refine (𝕀.weakEquivalences S).of_precomp ((𝕀.endpoint false).app X) _
    (𝕀.anodyne_le_weakEquivalences S hS _ (𝕀.anodyne_endpoint_app false X)) ?_
  rw [endpoint_app_contraction_app]
  exact 𝕀.isomorphisms_le_weakEquivalences S _ ((isomorphisms C).id_mem X)

theorem weakEquivalences_map (hS : S ≤ monomorphisms C) {K L : C} {j : K ⟶ L}
    (hj : 𝕀.weakEquivalences S j) : 𝕀.weakEquivalences S (𝕀.I.map j) := by
  refine (𝕀.weakEquivalences S).of_postcomp _ (𝕀.contraction.app L)
    (𝕀.weakEquivalences_contraction_app S hS L) ?_
  rw [𝕀.map_contraction_app]
  exact (𝕀.weakEquivalences S).comp_mem _ _ (𝕀.weakEquivalences_contraction_app S hS K) hj

include adj in
theorem fibrations_map (hS : S ≤ monomorphisms C) {X Y : C} {p : X ⟶ Y}
    (hp : 𝕀.fibrations S p) : 𝕀.fibrations S (Γ.map p) := by
  intro K L j hj
  have : Mono j := hj.1
  have := hp (𝕀.I.map j) ⟨monomorphisms.infer_property _, 𝕀.weakEquivalences_map S hS hj.2⟩
  exact (adj.hasLiftingProperty_iff j p).1 this

include adj in
theorem fibrations_terminal_from_obj (hS : S ≤ monomorphisms C) {X : C}
    (hX : 𝕀.fibrations S (terminal.from X)) : 𝕀.fibrations S (terminal.from (Γ.obj X)) := by
  have : PreservesLimitsOfSize.{0, 0} Γ := adj.rightAdjoint_preservesLimits
  let e := (terminalIsTerminal.isTerminalObj Γ (⊤_ C)).uniqueUpToIso terminalIsTerminal
  have h : terminal.from (Γ.obj X) = Γ.map (terminal.from X) ≫ e.hom := terminal.hom_ext _ _
  intro K L j hj
  have := 𝕀.fibrations_map adj S hS hX j hj
  rw [h]
  infer_instance

end HomotopicalAlgebra.ExactCylinder
