import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Equivalence
import Atoms.Homotopical.Cylinder.Induced

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe w v

variable {A : Type v} [SmallCategory A]

def IsComplete (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) : Prop :=
  𝕀.trivialCofibrations S ≤ 𝕀.anodyne S

theorem isComplete_tfae (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))) :
    List.TFAE
      [𝕀.IsComplete S,
        𝕀.naiveFibrations S ≤ 𝕀.fibrations S,
        𝕀.naiveFibrations S ⊓ 𝕀.weakEquivalences S ≤
          (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v))).rlp,
        ∀ ⦃X Y : Aᵒᵖ ⥤ Type (max w v)⦄ (p : X ⟶ Y), 𝕀.naiveFibrations S p →
          ∃ (Z : Aᵒᵖ ⥤ Type (max w v)) (j : X ⟶ Z) (q : Z ⟶ Y), 𝕀.anodyne S j ∧
            𝕀.fibrations S q ∧
              j ≫ q = p] := by
  have := 𝕀.hasFunctorialFactorization_anodyne S hS
  tfae_have 1 → 2 := fun h ↦ antitone_rlp h
  tfae_have 2 → 3 := fun h _ _ p hp ↦
    𝕀.rlp_inf_weakEquivalences_le_rlp_monomorphisms S p ⟨h p hp.1, hp.2⟩
  tfae_have 3 → 4 := by
    intro h X Y p _
    have := 𝕀.hasFunctorialFactorization_trivialCofibrations S
      (𝕀.trivialCofibrationsSetGenerated S hS)
    let F := factorizationData (𝕀.trivialCofibrations S) (𝕀.fibrations S) p
    let G := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) F.i
    have hGp : 𝕀.weakEquivalences S G.p :=
      MorphismProperty.of_precomp _ G.i G.p (𝕀.anodyne_le_weakEquivalences S hS _ G.hi)
        (by rw [G.fac]; exact F.hi.2)
    refine ⟨G.Z, G.i, G.p ≫ F.p, G.hi, ?_, by rw [← Category.assoc, G.fac, F.fac]⟩
    exact MorphismProperty.comp_mem _ _ _
      (antitone_rlp inf_le_left _ (h G.p ⟨G.hp, hGp⟩)) F.hp
  tfae_have 4 → 1 := by
    intro h X Y i hi
    let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) i
    obtain ⟨Z, k, r, hk, hr, hkr⟩ := h F.p F.hp
    have := hr i hi
    have hfac : (F.i ≫ k) ≫ r = i := by rw [Category.assoc, hkr, F.fac]
    exact (𝕀.anodyne S).of_retract (RetractArrow.ofLeftLiftingProperty hfac)
      (MorphismProperty.comp_mem _ _ _ F.hi hk)
  tfae_finish

instance overWeakEquivalences_hasTwoOutOfThreeProperty (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.overWeakEquivalences S X).HasTwoOutOfThreeProperty :=
  inferInstanceAs (((𝕀.over X).weakEquivalences
    (sliceGenerators (𝕀.anodyneGenerators S) X)).HasTwoOutOfThreeProperty)

instance respectsIso_overWeakEquivalences (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) :
    (𝕀.overWeakEquivalences S X).RespectsIso :=
  inferInstanceAs (((𝕀.over X).weakEquivalences
    (sliceGenerators (𝕀.anodyneGenerators S) X)).RespectsIso)

def absoluteWeakEquivalences (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty
    (Aᵒᵖ ⥤ Type v)) :
    MorphismProperty (Aᵒᵖ ⥤ Type v) :=
  fun _ L f ↦ ∀ (X : Aᵒᵖ ⥤ Type v) (l : L ⟶ X), 𝕀.overWeakEquivalences S X (sliceHom f l)

end HomotopicalAlgebra.ExactCylinder

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

def sliceForgetπArrowIso {X L : Aᵒᵖ ⥤ Type v} (l : L ⟶ X) :
    Arrow.mk ((sliceForgetπ X).app
        ((overEquivPresheafCostructuredArrow X).functor.obj (Over.mk l))) ≅ Arrow.mk l :=
  Arrow.isoMk
    ((Over.forget X).mapIso ((overEquivPresheafCostructuredArrow X).unitIso.app
      (Over.mk l))).symm (Iso.refl X)
    ((Over.w ((overEquivPresheafCostructuredArrow X).unitIso.app (Over.mk l)).inv).trans
      (Category.comp_id _).symm)

end Atoms.Homotopical

namespace HomotopicalAlgebra.ExactCylinder

open Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

variable (𝕀 : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v)) (S : MorphismProperty (Aᵒᵖ ⥤ Type v))

theorem overWeakEquivalences_sliceHom_comp_iff {X K L M : Aᵒᵖ ⥤ Type v} (f : K ⟶ L)
    (g : L ⟶ M) (h : M ⟶ X) :
    𝕀.overWeakEquivalences S X (sliceHom (f ≫ g) h) ↔
      𝕀.overWeakEquivalences S X (sliceHom f (g ≫ h) ≫ sliceHom g h) := by
  rw [sliceHom_comp]
  exact MorphismProperty.cancel_left_of_respectsIso _ _ _

theorem isFibrant_over_of_rlp_anodyne [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) {X L : Aᵒᵖ ⥤ Type v}
    (l : L ⟶ X) (hl : 𝕀.naiveFibrations S l) :
    (𝕀.over X).IsFibrant (sliceGenerators (𝕀.anodyneGenerators S) X)
      ((overEquivPresheafCostructuredArrow X).functor.obj (Over.mk l)) :=
  (𝕀.isFibrant_over_iff S hS X _).2
    (((𝕀.naiveFibrations S).arrow_mk_iso_iff (sliceForgetπArrowIso l)).2 hl)

theorem anodyne_le_absoluteWeakEquivalences [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    𝕀.anodyne S ≤ 𝕀.absoluteWeakEquivalences S := by
  intro K L f hf X l
  have := 𝕀.isSmall_anodyneGenerators S
  have hT := sliceGenerators_le_monomorphisms _ (𝕀.anodyneGenerators_le_monomorphisms S hS) X
  refine (𝕀.over X).anodyne_le_weakEquivalences _ hT _ ?_
  rw [𝕀.anodyne_over_eq S hS X]
  exact ((𝕀.anodyne S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso f l)).2 hf

theorem absoluteWeakEquivalences_le_weakEquivalences [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    𝕀.absoluteWeakEquivalences S ≤ 𝕀.weakEquivalences S := by
  intro K L f hf
  exact ((𝕀.weakEquivalences S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso f (𝟙 L))).1
    (𝕀.overWeakEquivalences_le S hS L _ (hf L (𝟙 L)))

theorem rlp_monomorphisms_le_absoluteWeakEquivalences :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp ≤ 𝕀.absoluteWeakEquivalences S := by
  intro Y Z p hp X l
  have h : (MorphismProperty.monomorphisms _).rlp (sliceHom p l) := by
    rw [monomorphisms_eq_inverseImage_sliceForget,
      rlp_inverseImage_sliceForget_of_respectsIso]
    exact ((MorphismProperty.monomorphisms _).rlp.arrow_mk_iso_iff
      (sliceForgetMapSliceHomIso p l)).2 hp
  exact (𝕀.over X).weakEquivalences_of_rlp_monomorphisms _ _ h

theorem anodyne_eq_monomorphisms_inf_absoluteWeakEquivalences [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    𝕀.anodyne S =
      MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ 𝕀.absoluteWeakEquivalences S := by
  refine le_antisymm (le_inf (𝕀.anodyne_le_monomorphisms S hS)
    (𝕀.anodyne_le_absoluteWeakEquivalences S hS)) ?_
  rintro K L f ⟨hf, hfa⟩
  have := 𝕀.isSmall_anodyneGenerators S
  have hT := sliceGenerators_le_monomorphisms _ (𝕀.anodyneGenerators_le_monomorphisms S hS) L
  have hmono : Mono (sliceHom f (𝟙 L)) := by
    rw [← (sliceForget L).mono_map_iff_mono]
    exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
      (sliceForgetMapSliceHomIso f (𝟙 L))).2 hf
  have h := ((𝕀.over L).anodyne_iff_weakEquivalences_of_isFibrant _ hT _ hmono
    (𝕀.isFibrant_over_of_rlp_anodyne S hS (𝟙 L) (MorphismProperty.id_mem _ _))).2
    (hfa L (𝟙 L))
  rw [𝕀.anodyne_over_eq S hS L] at h
  exact ((𝕀.anodyne S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso f (𝟙 L))).1 h

theorem rlp_monomorphisms_eq_rlp_anodyne_inf_absoluteWeakEquivalences [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp =
      𝕀.naiveFibrations S ⊓ 𝕀.absoluteWeakEquivalences S := by
  refine le_antisymm (le_inf (antitone_rlp (𝕀.anodyne_le_monomorphisms S hS))
    (𝕀.rlp_monomorphisms_le_absoluteWeakEquivalences S)) ?_
  rintro Y Z p ⟨hp, hpa⟩
  have hnaive : ((𝕀.over Z).anodyne (sliceGenerators (𝕀.anodyneGenerators S) Z)).rlp
      (sliceHom p (𝟙 Z)) := by
    rw [𝕀.rlp_anodyne_over_eq S hS Z]
    exact ((𝕀.naiveFibrations S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso p (𝟙 Z))).2 hp
  have h := ((𝕀.over Z).weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne _ _ hnaive
    (𝕀.isFibrant_over_of_rlp_anodyne S hS (𝟙 Z) (MorphismProperty.id_mem _ _))).1
    (hpa Z (𝟙 Z))
  rw [monomorphisms_eq_inverseImage_sliceForget,
    rlp_inverseImage_sliceForget_of_respectsIso] at h
  exact ((MorphismProperty.monomorphisms _).rlp.arrow_mk_iso_iff
    (sliceForgetMapSliceHomIso p (𝟙 Z))).1 h

instance absoluteWeakEquivalences_isStableUnderComposition :
    (𝕀.absoluteWeakEquivalences S).IsStableUnderComposition where
  comp_mem f g hf hg := fun T h ↦ (𝕀.overWeakEquivalences_sliceHom_comp_iff S f g h).2
    (MorphismProperty.comp_mem _ _ _ (hf T (g ≫ h)) (hg T h))

instance absoluteWeakEquivalences_hasOfPrecompProperty :
    (𝕀.absoluteWeakEquivalences S).HasOfPrecompProperty (𝕀.absoluteWeakEquivalences S) where
  of_precomp f g hf hfg := fun T h ↦ MorphismProperty.of_precomp _ _ _ (hf T (g ≫ h))
    ((𝕀.overWeakEquivalences_sliceHom_comp_iff S f g h).1 (hfg T h))

theorem absoluteWeakEquivalences_iff [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) {X Y : Aᵒᵖ ⥤ Type v}
    (f : X ⟶ Y) :
    𝕀.absoluteWeakEquivalences S f ↔
      ∃ (Z : Aᵒᵖ ⥤ Type v) (i : X ⟶ Z) (p : Z ⟶ Y), 𝕀.anodyne S i ∧
        (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp p ∧ i ≫ p = f := by
  constructor
  · intro hf
    have := 𝕀.hasFunctorialFactorization_anodyne S hS
    let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) f
    have hp : 𝕀.absoluteWeakEquivalences S F.p :=
      (𝕀.absoluteWeakEquivalences S).of_precomp F.i F.p
        (𝕀.anodyne_le_absoluteWeakEquivalences S hS _ F.hi) (by rw [F.fac]; exact hf)
    refine ⟨F.Z, F.i, F.p, F.hi, ?_, F.fac⟩
    rw [𝕀.rlp_monomorphisms_eq_rlp_anodyne_inf_absoluteWeakEquivalences S hS]
    exact ⟨F.hp, hp⟩
  · rintro ⟨Z, i, p, hi, hp, rfl⟩
    exact (𝕀.absoluteWeakEquivalences S).comp_mem i p
      (𝕀.anodyne_le_absoluteWeakEquivalences S hS _ hi)
      (𝕀.rlp_monomorphisms_le_absoluteWeakEquivalences S _ hp)

theorem absoluteWeakEquivalences_le_of [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (C : MorphismProperty (Aᵒᵖ ⥤ Type v))
    (hcomp : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type v⦄ (f : X ⟶ Y) (g : Y ⟶ Z), C f → C g → C (f ≫ g))
    (hcancel : ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type v⦄ (f : X ⟶ Y) (g : Y ⟶ Z), C f → C (f ≫ g) → C g)
    (hAn : 𝕀.anodyne S ≤ C) : 𝕀.absoluteWeakEquivalences S ≤ C := by
  intro X Y f hf
  obtain ⟨Z, i, p, hi, hp, rfl⟩ := (𝕀.absoluteWeakEquivalences_iff S hS f).1 hf
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms p hp
  obtain ⟨d, -⟩ := 𝕀.exists_deformation_retract_of_rlp_monomorphisms p hp s hs
  have hsa : 𝕀.anodyne S s := 𝕀.anodyne_of_deformation_retract S hS s d
  refine hcomp _ _ (hAn _ hi) (hcancel s p (hAn _ hsa) ?_)
  rw [hs]
  exact hAn _ (MorphismProperty.id_mem _ _)

private theorem anodyne_of_comp_aux [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    {X Y Z : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : 𝕀.anodyne S f)
    (hfg : 𝕀.anodyne S (f ≫ g)) (hg : Mono g) : 𝕀.anodyne S g := by
  rw [𝕀.anodyne_eq_monomorphisms_inf_absoluteWeakEquivalences S hS]
  exact ⟨hg, (𝕀.absoluteWeakEquivalences S).of_precomp f g
    (𝕀.anodyne_le_absoluteWeakEquivalences S hS _ hf)
    (𝕀.anodyne_le_absoluteWeakEquivalences S hS _ hfg)⟩

theorem isComplete_tfae_absolute [S.IsSmall.{v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)) :
    List.TFAE
      [𝕀.IsComplete S,
        ∀ X : Aᵒᵖ ⥤ Type v,
          𝕀.overWeakEquivalences S X = (𝕀.weakEquivalences S).inverseImage (sliceForget X),
        𝕀.weakEquivalences S ≤ 𝕀.absoluteWeakEquivalences S,
        ∀ ⦃X Y Z : Aᵒᵖ ⥤ Type v⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
          𝕀.absoluteWeakEquivalences S g → 𝕀.absoluteWeakEquivalences S (f ≫ g) →
            𝕀.absoluteWeakEquivalences S f] := by
  have := 𝕀.hasFunctorialFactorization_anodyne S hS
  tfae_have 1 → 3 := by
    intro h X Y f hf
    let F := factorizationData (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
      (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp f
    have hi : 𝕀.weakEquivalences S F.i :=
      MorphismProperty.of_postcomp _ F.i F.p (𝕀.weakEquivalences_of_rlp_monomorphisms S _ F.hp)
        (by rw [F.fac]; exact hf)
    exact (𝕀.absoluteWeakEquivalences_iff S hS f).2 ⟨F.Z, F.i, F.p, h _ ⟨F.hi, hi⟩, F.hp, F.fac⟩
  tfae_have 3 → 1 := by
    rintro h X Y i ⟨hi, hW⟩
    rw [𝕀.anodyne_eq_monomorphisms_inf_absoluteWeakEquivalences S hS]
    exact ⟨hi, h _ hW⟩
  tfae_have 2 → 3 := by
    intro h X Y f hf T l
    rw [h T]
    exact ((𝕀.weakEquivalences S).arrow_mk_iso_iff (sliceForgetMapSliceHomIso f l)).2 hf
  tfae_have 3 → 2 := by
    intro h X
    refine le_antisymm (𝕀.overWeakEquivalences_le S hS X) ?_
    intro Y Z g hg
    exact ((𝕀.overWeakEquivalences S X).arrow_mk_iso_iff (sliceHomSliceForgetIso g)).1
      (h _ hg X ((sliceForgetπ X).app Z))
  tfae_have 3 → 4 := by
    intro h X Y Z f g hg hfg
    exact h _ (MorphismProperty.of_postcomp _ f g
      (𝕀.absoluteWeakEquivalences_le_weakEquivalences S hS _ hg)
      (𝕀.absoluteWeakEquivalences_le_weakEquivalences S hS _ hfg))
  tfae_have 4 → 3 := by
    intro h X Y f hf
    obtain ⟨Y', j, hj, hY'⟩ := 𝕀.exists_anodyne_isFibrant S hS Y
    let F := factorizationData (𝕀.anodyne S) (𝕀.naiveFibrations S) (f ≫ j)
    have hp : 𝕀.weakEquivalences S F.p :=
      MorphismProperty.of_precomp _ F.i F.p (𝕀.anodyne_le_weakEquivalences S hS _ F.hi)
        (by
          rw [F.fac]
          exact MorphismProperty.comp_mem _ _ _ hf (𝕀.anodyne_le_weakEquivalences S hS _ hj))
    have hp' := (𝕀.weakEquivalences_iff_rlp_monomorphisms_of_rlp_anodyne S F.p F.hp hY').1 hp
    exact h f j (𝕀.anodyne_le_absoluteWeakEquivalences S hS _ hj)
      ((𝕀.absoluteWeakEquivalences_iff S hS _).2 ⟨F.Z, F.i, F.p, F.hi, hp', F.fac⟩)
  tfae_finish

end HomotopicalAlgebra.ExactCylinder

namespace HomotopicalAlgebra.ExactCylinder

universe w v

theorem anodyne_of_comp {A : Type v} [SmallCategory A]
    (𝕀 : ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)))
    (S : MorphismProperty (Aᵒᵖ ⥤ Type (max w v))) [S.IsSmall.{max w v}]
    (hS : S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)))
    {X Y Z : Aᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : 𝕀.anodyne S f)
    (hfg : 𝕀.anodyne S (f ≫ g)) (hg : Mono g) : 𝕀.anodyne S g := by
  let e : (Aᵒᵖ ⥤ Type (max w v)) ≌ ((AsSmall.{max w v} A)ᵒᵖ ⥤ Type (max w v)) :=
    (AsSmall.equiv : A ≌ AsSmall.{max w v} A).op.congrLeft
  rw [← anodyne_transport_map_iff 𝕀 e] at hf hfg ⊢
  rw [Functor.map_comp] at hfg
  have hS' : functorImage e.functor S ≤ MorphismProperty.monomorphisms _ := by
    rintro _ _ _ ⟨K, L, t, ht, h⟩
    have : Mono t := hS t ht
    exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (eqToIso h)).1
      (e.functor.map_mono t)
  exact anodyne_of_comp_aux (𝕀.transport e) (functorImage e.functor S) hS' _ _ hf hfg
    (e.functor.map_mono g)

end HomotopicalAlgebra.ExactCylinder
