import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Anodyne
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra

universe w v u

variable {C : Type u} [Category.{v} C]

instance hasFunctorialFactorization_monomorphisms [HasCellularModel C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] :
    HasFunctorialFactorization (MorphismProperty.monomorphisms C)
      (MorphismProperty.monomorphisms C).rlp := by
  rw [← HasCellularModel.saturation_cellularModel (C := C), rlp_saturation]
  exact hasFunctorialFactorization_saturation (HasCellularModel.cellularModel (C := C))

namespace ExactCylinder

variable [HasBinaryCoproducts C] (𝕀 : ExactCylinder.{w} C)

theorem elementaryHomotopy_comp {X Y T : C} {f g : X ⟶ Y}
    (h : 𝕀.ElementaryHomotopy f g) (l : Y ⟶ T) : 𝕀.ElementaryHomotopy (f ≫ l) (g ≫ l) := by
  obtain ⟨k, h₀, h₁⟩ := h
  exact ⟨k ≫ l, by rw [← Category.assoc, h₀], by rw [← Category.assoc, h₁]⟩

theorem homotopic_comp {X Y T : C} {f g : X ⟶ Y}
    (h : 𝕀.Homotopic f g) (l : Y ⟶ T) : 𝕀.Homotopic (f ≫ l) (g ≫ l) :=
  Homotopic.map 𝕀 (· ≫ l) (fun _ _ h ↦ 𝕀.elementaryHomotopy_comp h l) h

theorem precompClasses_eq_of_homotopic {X Y : C} {f g : X ⟶ Y}
    (h : 𝕀.Homotopic f g) (T : C) :
    𝕀.precompClasses f T = 𝕀.precompClasses g T := by
  funext c
  induction c using Quotient.inductionOn with
  | h l => exact Quotient.sound (𝕀.homotopic_comp h l)

theorem precompClasses_eq_id_of_homotopic {X : C} {f : X ⟶ X}
    (h : 𝕀.Homotopic f (𝟙 X)) (T : C) : 𝕀.precompClasses f T = id := by
  rw [𝕀.precompClasses_eq_of_homotopic h T, precompClasses_id]

theorem bijective_precompClasses_of_homotopy_retract {A B X Y : C} (f : A ⟶ B)
    (s : X ⟶ Y) (r : Y ⟶ X) (h : 𝕀.Homotopic (s ≫ r) (𝟙 X))
    (hf : Function.Bijective (𝕀.precompClasses f Y)) :
    Function.Bijective (𝕀.precompClasses f X) := by
  let post {Z T U : C} (g : T ⟶ U) : 𝕀.HomotopyClasses Z T → 𝕀.HomotopyClasses Z U :=
    Quotient.map (· ≫ g) fun _ _ hg => 𝕀.homotopic_comp hg g
  have ret (Z : C) (c : 𝕀.HomotopyClasses Z X) : post r (post s c) = c := by
    induction c using Quotient.inductionOn with | h k => ?_
    apply Quotient.sound
    change 𝕀.Homotopic ((k ≫ s) ≫ r) k
    simpa only [Category.assoc, Category.comp_id] using 𝕀.homotopic_precomp k h
  have nat {T U : C} (g : T ⟶ U) (c : 𝕀.HomotopyClasses B T) :
      post g (𝕀.precompClasses f T c) = 𝕀.precompClasses f U (post g c) := by
    induction c using Quotient.inductionOn with | h k => ?_
    exact congrArg (Quotient.mk _) (Category.assoc f k g)
  refine ⟨fun c d hcd => ?_, fun c => ?_⟩
  · have hsd : post s c = post s d := hf.1 (by rw [← nat, ← nat, hcd])
    have hr := congrArg (post r) hsd
    simpa only [ret] using hr
  · obtain ⟨d, hd⟩ := hf.2 (post s c)
    exact ⟨post r d, by rw [← nat, hd, ret]⟩

variable [HasPushouts C] [HasTerminal C] (S : MorphismProperty C)

theorem weakEquivalences_of_homotopic {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : 𝕀.Homotopic (f ≫ g) (𝟙 X)) (hgf : 𝕀.Homotopic (g ≫ f) (𝟙 Y)) :
    𝕀.weakEquivalences S f := by
  intro T _
  have h₁ := 𝕀.precompClasses_eq_id_of_homotopic hfg T
  have h₂ := 𝕀.precompClasses_eq_id_of_homotopic hgf T
  rw [precompClasses_comp] at h₁ h₂
  exact Function.bijective_iff_has_inverse.2
    ⟨𝕀.precompClasses g T, congrFun h₂, congrFun h₁⟩

theorem weakEquivalences_of_rlp_monomorphisms [HasInitial C] [HasStrictInitialObjects C] {X Y : C}
    (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) : 𝕀.weakEquivalences S p := by
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨k, hk₀, hk₁, -⟩ := 𝕀.exists_homotopy_of_rlp_monomorphisms p hp s hs
  refine 𝕀.weakEquivalences_of_homotopic S p s ?_ ?_
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨k, hk₀, hk₁⟩)
  · rw [hs]
    exact Relation.EqvGen.refl _

theorem hasFactorization_monomorphisms_rlp_inf_weakEquivalences [HasInitial C]
    [HasStrictInitialObjects C] [HasCellularModel C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] :
    HasFactorization (MorphismProperty.monomorphisms C)
      (𝕀.fibrations S ⊓
        𝕀.weakEquivalences S) where
  nonempty_mapFactorizationData f := by
    let h := factorizationData (MorphismProperty.monomorphisms C)
      (MorphismProperty.monomorphisms C).rlp f
    exact ⟨⟨h.Z, h.i, h.p, h.fac, h.hi, antitone_rlp inf_le_left _ h.hp,
      𝕀.weakEquivalences_of_rlp_monomorphisms S _ h.hp⟩⟩

theorem rlp_inf_weakEquivalences_le_rlp_monomorphisms [HasInitial C] [HasStrictInitialObjects C]
    [HasCellularModel C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] :
    𝕀.fibrations S ⊓
        𝕀.weakEquivalences S ≤ (MorphismProperty.monomorphisms C).rlp := by
  intro X Y p ⟨hF, hW⟩
  let h := factorizationData (MorphismProperty.monomorphisms C)
    (MorphismProperty.monomorphisms C).rlp p
  have hq : 𝕀.weakEquivalences S h.p := 𝕀.weakEquivalences_of_rlp_monomorphisms S _ h.hp
  have hi : 𝕀.weakEquivalences S h.i :=
    MorphismProperty.of_postcomp _ h.i h.p hq (by rw [h.fac]; exact hW)
  have := hF h.i ⟨h.hi, hi⟩
  exact (rlp_isStableUnderRetracts _).of_retract
    (RetractArrow.ofRightLiftingProperty h.fac) h.hp

theorem rlp_monomorphisms_eq [HasInitial C] [HasStrictInitialObjects C] [HasCellularModel C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] :
    (MorphismProperty.monomorphisms C).rlp =
      𝕀.fibrations S ⊓
        𝕀.weakEquivalences S := by
  have := 𝕀.hasFactorization_monomorphisms_rlp_inf_weakEquivalences S
  exact rlp_eq_of_le_rlp_of_hasFactorization_of_isStableUnderRetracts
    (𝕀.rlp_inf_weakEquivalences_le_rlp_monomorphisms S)

theorem trivialFibrationIffRlpMono [HasInitial C] [HasStrictInitialObjects C] [HasCellularModel C]
    [HasColimitsOfSize.{v, v} C] [IsLocallyPresentable.{v} C] :
    ∀ ⦃X Y : C⦄ (p : X ⟶ Y),
      (𝕀.weakEquivalences S p ∧
          𝕀.fibrations S p) ↔
        (MorphismProperty.monomorphisms C).rlp p := by
  intro X Y p
  rw [𝕀.rlp_monomorphisms_eq S]
  exact and_comm

end ExactCylinder

end HomotopicalAlgebra
