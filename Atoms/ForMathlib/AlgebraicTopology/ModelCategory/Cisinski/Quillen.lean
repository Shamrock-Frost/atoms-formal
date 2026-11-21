import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.ModelStructure
import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace HomotopicalAlgebra.ExactCylinder

universe w w' v v' u u'

section

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  (𝕀 : ExactCylinder.{w} C) (S : MorphismProperty C)

theorem homotopic_iff_nonempty_leftHomotopy {Z : C} (hZ : 𝕀.IsFibrant S Z) {X : C}
    (P : Precylinder X) [Mono P.i] (hP : 𝕀.weakEquivalences S P.π) (u v : X ⟶ Z) :
    𝕀.Homotopic u v ↔ Nonempty (P.LeftHomotopy u v) := by
  refine ⟨fun huv ↦ ?_, fun ⟨h⟩ ↦ ?_⟩
  · obtain ⟨k, hk₀, hk₁⟩ := (𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hZ u v).1 huv
    obtain ⟨ψ, hψl, hψr⟩ := 𝕀.exists_map_coprod_comp X
    have hc : (𝕀.endpoint false).app (X ⨿ X) ≫ ψ ≫ coprod.desc (𝕀.contraction.app X ≫ u) k =
        P.i ≫ P.π ≫ u := by
      refine coprod.hom_ext ?_ ?_
      · rw [← 𝕀.endpoint_naturality_assoc, reassoc_of% hψl, coprod.inl_desc,
          𝕀.endpoint_app_contraction_app_assoc, P.inl_i_assoc, P.i₀_π_assoc]
      · rw [← 𝕀.endpoint_naturality_assoc, reassoc_of% hψr, coprod.inr_desc, hk₀,
          P.inr_i_assoc, P.i₁_π_assoc]
    obtain ⟨L, hL⟩ := 𝕀.exists_fac_of_isFibrant S hZ
      ((𝕀.isAnodyneClass_anodyne S).endpointBox_mem false P.i inferInstance)
      (pushout.desc _ _ hc)
    have hL₁ := 𝕀.map_comp_eq_of_endpointBox_comp_eq false P.i hL
    refine ⟨{ h := (𝕀.endpoint true).app P.I ≫ L, h₀ := ?_, h₁ := ?_ }⟩
    · rw [← P.inl_i, Category.assoc, ← 𝕀.endpoint_naturality_assoc, hL₁,
        ← 𝕀.endpoint_naturality_assoc, reassoc_of% hψl, coprod.inl_desc,
        𝕀.endpoint_app_contraction_app_assoc]
    · rw [← P.inr_i, Category.assoc, ← 𝕀.endpoint_naturality_assoc, hL₁,
        ← 𝕀.endpoint_naturality_assoc, reassoc_of% hψr, coprod.inr_desc, hk₁]
  · obtain ⟨c, hc⟩ := (hP Z hZ).2 (Quotient.mk _ h.h)
    induction c using Quotient.inductionOn with | h c => ?_
    have hh : 𝕀.Homotopic (P.π ≫ c) h.h := Quotient.exact hc
    have h₀ := 𝕀.homotopic_precomp P.i₀ hh
    have h₁ := 𝕀.homotopic_precomp P.i₁ hh
    rw [P.i₀_π_assoc, h.h₀] at h₀
    rw [P.i₁_π_assoc, h.h₁] at h₁
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h₀) h₁

end

section

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasTerminal C] [HasInitial C] [HasStrictInitialObjects C]
  [HasFactorization (monomorphisms C) (monomorphisms C).rlp]

theorem homotopic_iff_of_isFibrant (𝕀 : ExactCylinder.{w} C) (𝕁 : ExactCylinder.{w'} C)
    (S T : MorphismProperty C) {Z : C} (hZ : 𝕀.IsFibrant S Z) (hZ' : 𝕁.IsFibrant T Z)
    {X : C} (f g : X ⟶ Z) : 𝕀.Homotopic f g ↔ 𝕁.Homotopic f g := by
  let φ := factorizationData (monomorphisms C) (monomorphisms C).rlp
    (coprod.desc (𝟙 X) (𝟙 X))
  let P : Precylinder X :=
    { I := φ.Z
      i₀ := coprod.inl ≫ φ.i
      i₁ := coprod.inr ≫ φ.i
      π := φ.p
      i₀_π := by rw [Category.assoc, φ.fac, coprod.inl_desc]
      i₁_π := by rw [Category.assoc, φ.fac, coprod.inr_desc] }
  have hi : P.i = φ.i := by
    apply coprod.hom_ext
    · exact coprod.inl_desc _ _
    · exact coprod.inr_desc _ _
  have : Mono P.i := by
    rw [hi]
    exact φ.hi
  exact (𝕀.homotopic_iff_nonempty_leftHomotopy S hZ P
    (𝕀.weakEquivalences_of_rlp_monomorphisms S φ.p φ.hp) f g).trans
    (𝕁.homotopic_iff_nonempty_leftHomotopy T hZ' P
      (𝕁.weakEquivalences_of_rlp_monomorphisms T φ.p φ.hp) f g).symm

theorem weakEquivalences_le_of_isFibrant (𝕀 : ExactCylinder.{w} C)
    (𝕁 : ExactCylinder.{w'} C) (S T : MorphismProperty C)
    (h : ∀ Z : C, 𝕁.IsFibrant T Z → 𝕀.IsFibrant S Z) :
    𝕀.weakEquivalences S ≤ 𝕁.weakEquivalences T := by
  intro A B f hf Z hZ
  let e (X : C) : 𝕀.HomotopyClasses X Z ≃ 𝕁.HomotopyClasses X Z :=
    Quotient.congr (Equiv.refl _) fun u v =>
      homotopic_iff_of_isFibrant 𝕀 𝕁 S T (h Z hZ) hZ u v
  have he : e A ∘ 𝕀.precompClasses f Z = 𝕁.precompClasses f Z ∘ e B := by
    funext c
    induction c using Quotient.inductionOn with | h u => rfl
  rw [← (e B).bijective.of_comp_iff, ← he]
  exact (e A).bijective.comp (hf Z (h Z hZ))

theorem weakEquivalences_eq_of_isFibrant_iff (𝕀 : ExactCylinder.{w} C)
    (𝕁 : ExactCylinder.{w'} C) (S T : MorphismProperty C)
    (h : ∀ Z : C, 𝕀.IsFibrant S Z ↔ 𝕁.IsFibrant T Z) :
    𝕀.weakEquivalences S = 𝕁.weakEquivalences T :=
  le_antisymm (weakEquivalences_le_of_isFibrant 𝕀 𝕁 S T fun Z => (h Z).2)
    (weakEquivalences_le_of_isFibrant 𝕁 𝕀 T S fun Z => (h Z).1)

end

section

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  {D : Type u'} [Category.{v'} D] [HasBinaryCoproducts D] [HasPushouts D] [HasTerminal D]

theorem homotopic_homEquiv_iff (𝕀 : ExactCylinder.{w} C) (𝕁 : ExactCylinder.{w'} D)
    (S : MorphismProperty C) (T : MorphismProperty D) {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.PreservesMonomorphisms] {Y : C}
    (hY : 𝕁.weakEquivalences T (F.map (𝕀.contraction.app Y))) {Z : D}
    (hZ : 𝕁.IsFibrant T Z) (hGZ : 𝕀.IsFibrant S (G.obj Z)) (u v : F.obj Y ⟶ Z) :
    𝕀.Homotopic (adj.homEquiv Y Z u) (adj.homEquiv Y Z v) ↔ 𝕁.Homotopic u v := by
  let P : Precylinder (F.obj Y) := Precylinder.map
    { I := 𝕀.I.obj Y
      i₀ := (𝕀.endpoint false).app Y
      i₁ := (𝕀.endpoint true).app Y
      π := 𝕀.contraction.app Y
      i₀_π := 𝕀.endpoint_app_contraction_app false Y
      i₁_π := 𝕀.endpoint_app_contraction_app true Y } F
  have := adj.isLeftAdjoint
  have hPi : coprod.desc (F.map ((𝕀.endpoint false).app Y) : F.obj Y ⟶ _)
      (F.map ((𝕀.endpoint true).app Y) : F.obj Y ⟶ _) =
      coprodComparison F Y Y ≫ F.map (𝕀.endpoints Y) := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc, coprodComparison_inl_assoc, ← F.map_comp, inl_endpoints]
    · rw [coprod.inr_desc, coprodComparison_inr_assoc, ← F.map_comp, inr_endpoints]
  have : Mono P.i := by
    have : Mono (coprod.desc (F.map ((𝕀.endpoint false).app Y) : F.obj Y ⟶ _)
        (F.map ((𝕀.endpoint true).app Y) : F.obj Y ⟶ _)) := by
      rw [hPi]
      infer_instance
    exact this
  rw [𝕁.homotopic_iff_nonempty_leftHomotopy T hZ P hY,
    𝕀.homotopic_iff_elementaryHomotopy_of_isFibrant S hGZ]
  constructor
  · rintro ⟨k, hk₀, hk₁⟩
    refine ⟨{ h := (adj.homEquiv _ _).symm k, h₀ := ?_, h₁ := ?_ }⟩
    · exact (adj.homEquiv_naturality_left_symm _ k).symm.trans
        ((congrArg _ hk₀).trans ((adj.homEquiv _ _).symm_apply_apply u))
    · exact (adj.homEquiv_naturality_left_symm _ k).symm.trans
        ((congrArg _ hk₁).trans ((adj.homEquiv _ _).symm_apply_apply v))
  · rintro ⟨h⟩
    exact ⟨adj.homEquiv _ _ h.h, (adj.homEquiv_naturality_left _ h.h).symm.trans
        (congrArg _ h.h₀), (adj.homEquiv_naturality_left _ h.h).symm.trans (congrArg _ h.h₁)⟩

theorem map_mem_weakEquivalences (𝕀 : ExactCylinder.{w} C) (𝕁 : ExactCylinder.{w'} D)
    (S : MorphismProperty C) (T : MorphismProperty D) {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.PreservesMonomorphisms]
    (hcyl : ∀ Y : C, 𝕁.weakEquivalences T (F.map (𝕀.contraction.app Y)))
    (hG : ∀ Z : D, 𝕁.IsFibrant T Z → 𝕀.IsFibrant S (G.obj Z)) :
    𝕀.weakEquivalences S ≤ (𝕁.weakEquivalences T).inverseImage F := by
  intro A B w hw Z hZ
  let e : ∀ Y : C, 𝕁.HomotopyClasses (F.obj Y) Z ≃ 𝕀.HomotopyClasses Y (G.obj Z) := fun Y ↦
    Quotient.congr (adj.homEquiv Y Z) fun u v ↦
      (𝕀.homotopic_homEquiv_iff 𝕁 S T adj (hcyl Y) hZ (hG Z hZ) u v).symm
  have he : e A ∘ 𝕁.precompClasses (F.map w) Z = 𝕀.precompClasses w (G.obj Z) ∘ e B := by
    funext c
    induction c using Quotient.inductionOn with | h u => ?_
    exact congrArg (Quotient.mk _) (adj.homEquiv_naturality_left w u)
  rw [← (e A).bijective.of_comp_iff', he]
  exact (hw _ (hG Z hZ)).comp (e B).bijective

end

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  {D : Type u'} [Category.{v} D] [HasBinaryCoproducts D] [HasPushouts D] [HasTerminal D]

theorem isQuillen_of_map_contraction [HasFiniteLimits C] [HasInitial C]
    [HasStrictInitialObjects C] [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C]
    [HasCellularModel C]
    [HasFiniteLimits D] [HasInitial D] [HasStrictInitialObjects D] [HasColimitsOfSize.{v, v} D]
    [IsLocallyPresentable.{v} D] [HasCellularModel D]
    (𝕀 : ExactCylinder.{v} C) (𝕁 : ExactCylinder.{v} D)
    (S : MorphismProperty C) (T : MorphismProperty D)
    (hS : 𝕀.TrivialCofibrationsSetGenerated S) (hT : 𝕁.TrivialCofibrationsSetGenerated T)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesMonomorphisms]
    (hcyl : ∀ Y : C, 𝕁.weakEquivalences T (F.map (𝕀.contraction.app Y)))
    (hG : ∀ Z : D, 𝕁.IsFibrant T Z → 𝕀.IsFibrant S (G.obj Z)) :
    letI := 𝕀.modelCategoryOfSetGenerated S hS
    letI := 𝕁.modelCategoryOfSetGenerated T hT
    adj.IsQuillen :=
  letI := 𝕀.modelCategoryOfSetGenerated S hS
  letI := 𝕁.modelCategoryOfSetGenerated T hT
  have hmono : monomorphisms C ≤ (monomorphisms D).inverseImage F :=
    fun _ _ f (_ : Mono f) ↦ F.map_mono f
  { cofibrations_le := hmono
    trivialCofibrations_le := fun _ _ f hf ↦
      ⟨hmono f hf.1, map_mem_weakEquivalences 𝕀 𝕁 S T adj hcyl hG f hf.2⟩ }

end HomotopicalAlgebra.ExactCylinder
