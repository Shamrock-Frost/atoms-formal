import Atoms.Homotopical.Localizer.Accessible
import Atoms.TestCategory.LocalTestCriterion

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite

namespace Atoms.TestCategory

open Homotopical (SeparatingInterval)

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

theorem aspherical_costructuredArrow_elementsSnd {Y : Aᵒᵖ ⥤ Type u}
    (hY : 𝒲.LocallyAspherical A Y) (X : Aᵒᵖ ⥤ Type u) (c : (X.Elements)ᵒᵖ) :
    𝒲.Aspherical (Cat.of (CostructuredArrow (elementsSnd Y X) c)) :=
  𝒲.aspherical_of_equivalence
    (A := (elementsFunctor A).obj (FunctorToTypes.prod (yoneda.obj (unop c.unop.1)) Y))
    (costructuredArrowElementsSndEquivalence Y X c).symm
    ((𝒲.pshAspherical_iff_of_iso A (FunctorToTypes.binaryProductIso _ _)).1 (hY _))

theorem wPsh_snd_of_locallyAspherical {Y : Aᵒᵖ ⥤ Type u} (hY : 𝒲.LocallyAspherical A Y)
    (X : Aᵒᵖ ⥤ Type u) : 𝒲.wPsh A (CartesianMonoidalCategory.snd Y X) :=
  𝒲.quillenA _ (𝟙 _) fun c =>
    𝒲.W_of_aspherical_of_hasTerminal _ (𝒲.aspherical_costructuredArrow_elementsSnd A hY X c)

theorem wPsh_whiskerLeft_of_locallyAspherical {Y : Aᵒᵖ ⥤ Type u}
    (hY : 𝒲.LocallyAspherical A Y) {X X' : Aᵒᵖ ⥤ Type u} {f : X ⟶ X'} (hf : 𝒲.wPsh A f) :
    𝒲.wPsh A (Y ◁ f) := by
  have sq : (Y ◁ f) ≫ CartesianMonoidalCategory.snd Y X' =
      CartesianMonoidalCategory.snd Y X ≫ f :=
    CartesianMonoidalCategory.whiskerLeft_snd _ _
  refine (𝒲.wPsh A).of_postcomp _ _ (𝒲.wPsh_snd_of_locallyAspherical A hY X') ?_
  rw [sq]
  exact (𝒲.wPsh A).comp_mem _ _ (𝒲.wPsh_snd_of_locallyAspherical A hY X) hf

theorem wPsh_of_homotopic_id {C : Type u} [SmallCategory C] (𝒲 : BasicLocalizer.{u})
    {J Q : Cᵒᵖ ⥤ Type u} (hJ : 𝒲.LocallyAspherical C J) (i₀ i₁ : Q ⟶ J ⊗ Q)
    (h₀ : i₀ ≫ CartesianMonoidalCategory.snd J Q = 𝟙 Q)
    (h₁ : i₁ ≫ CartesianMonoidalCategory.snd J Q = 𝟙 Q)
    (h : J ⊗ Q ⟶ Q) (e : Q ⟶ Q)
    (he : i₀ ≫ h = e) (h1 : i₁ ≫ h = 𝟙 Q) : 𝒲.wPsh C e := by
  let V := 𝒲.wPsh C
  have hv : V (CartesianMonoidalCategory.snd J Q) :=
    𝒲.wPsh_snd_of_locallyAspherical C hJ Q
  have hid : V (𝟙 Q) :=
    isomorphisms_le_of_containsIdentities (𝒲.wPsh C) _ (isomorphisms.infer_property _)
  have hi₀ : V i₀ := V.of_postcomp _ _ hv (h₀ ▸ hid)
  have hi₁ : V i₁ := V.of_postcomp _ _ hv (h₁ ▸ hid)
  have hh : V h := V.of_precomp _ _ hi₁ (h1 ▸ hid)
  exact he ▸ V.comp_mem _ _ hi₀ hh

theorem wPsh_of_retraction {C : Type u} [SmallCategory C] (𝒲 : BasicLocalizer.{u})
    {P Q : Cᵒᵖ ⥤ Type u} (s : P ⟶ Q) (r : Q ⟶ P) (hsr : s ≫ r = 𝟙 P)
    (h : 𝒲.wPsh C (r ≫ s)) : 𝒲.wPsh C s := by
  let R : RetractArrow s (r ≫ s) :=
    { i := Arrow.homMk s (𝟙 Q) (by
        change s ≫ (r ≫ s) = s ≫ 𝟙 Q
        rw [← Category.assoc, hsr, Category.id_comp, Category.comp_id])
      r := Arrow.homMk r (𝟙 Q) (by simp)
      retract := Arrow.hom_ext _ _ hsr (by simp) }
  exact (𝒲.wPsh C).of_retract R h

theorem rlp_monomorphisms_le_wPsh_of_separatingInterval (J : SeparatingInterval.{u, u} A)
    (hJ : 𝒲.LocallyAspherical A J.interval) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A :=
  Homotopical.rlp_monomorphisms_le_of_cylinderCompatibleWith (𝒲.wPsh A)
    J.cylinder (fun X => 𝒲.wPsh_snd_of_locallyAspherical A hJ X)

theorem isLocalTest_of_separatingInterval (J : SeparatingInterval.{u, u} A)
    (hJ : 𝒲.LocallyAspherical A J.interval) : 𝒲.IsLocalTest A :=
  𝒲.isLocalTest_of_rlp_le A (𝒲.rlp_monomorphisms_le_wPsh_of_separatingInterval A J hJ)

theorem isTest_of_separatingInterval (J : SeparatingInterval.{u, u} A)
    (hJ : 𝒲.LocallyAspherical A J.interval) (hA : 𝒲.Aspherical (Cat.of A)) :
    𝒲.IsTest A :=
  𝒲.isTest_of_rlp_le A hA (𝒲.rlp_monomorphisms_le_wPsh_of_separatingInterval A J hJ)

end BasicLocalizer

end Atoms.TestCategory
