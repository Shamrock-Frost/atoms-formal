import Atoms.Homotopical.Regular.Rigid
import Atoms.TestCategory.LocalTestCriterion
import Atoms.TestCategory.Presheaf.PrelocalizerChain
import Atoms.TestCategory.Presheaf.PrelocalizerPushout

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.TestCategory

open Homotopical (rlp_monomorphisms_le_of_cylinderCompatibleWith)

universe u

section Representable

variable (𝒲 : BasicLocalizer.{u}) {A : Type u} [SmallCategory A] {B : Type u} [SmallCategory B]

namespace BasicLocalizer

theorem isMonoSaturatedClass_wPsh_app (Φ Ψ : (Aᵒᵖ ⥤ Type u) ⥤ (Bᵒᵖ ⥤ Type u))
    [PreservesColimitsOfSize.{u, u} Φ] [PreservesColimitsOfSize.{u, u} Ψ]
    (hΦ : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), Mono f → Mono (Φ.map f))
    (hΨ : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), Mono f → Mono (Ψ.map f)) (α : Φ ⟶ Ψ) :
    Homotopical.IsMonoSaturatedClass (fun X => 𝒲.wPsh B (α.app X)) where
  of_isPushout {X₀ X₁ X₂ X₃ f₁ f₂ g₁ g₂} h hf h₀ h₁ h₂ := by
    have := preservesSmallestColimits_of_preservesColimits Φ
    have := preservesSmallestColimits_of_preservesColimits Ψ
    have := hΦ f₁ hf
    have := hΨ f₁ hf
    exact 𝒲.wPsh_of_isPushout B (Φ.map_isPushout h) (Ψ.map_isPushout h)
      (α.app X₀) (α.app X₁) (α.app X₂) (α.app X₃) (α.naturality f₁) (α.naturality f₂)
      (α.naturality g₁) (α.naturality g₂) h₀ h₁ h₂
  of_isColimit J _ _ F hF {c} hc hP :=
    𝒲.wPsh_of_isColimit B (X := F ⋙ Φ) (Y := F ⋙ Ψ)
      (fun i j h => hΦ _ (hF i j h)) (fun i j h => hΨ _ (hF i j h))
      (Functor.whiskerLeft F α) hP (isColimitOfPreserves Φ hc) (isColimitOfPreserves Ψ hc)
      (α.app c.pt) (fun j => α.naturality (c.ι.app j))

theorem wPsh_app_of_forall_yoneda [Homotopical.EZCategory A]
    [Homotopical.HasTrivialAutomorphisms A] (Φ Ψ : (Aᵒᵖ ⥤ Type u) ⥤ (Bᵒᵖ ⥤ Type u))
    [PreservesColimitsOfSize.{u, u} Φ] [PreservesColimitsOfSize.{u, u} Ψ]
    (hΦ : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), Mono f → Mono (Φ.map f))
    (hΨ : ∀ {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y), Mono f → Mono (Ψ.map f)) (α : Φ ⟶ Ψ)
    (h : ∀ a : A, 𝒲.wPsh B (α.app (yoneda.obj a))) (X : Aᵒᵖ ⥤ Type u) :
    𝒲.wPsh B (α.app X) :=
  (𝒲.isMonoSaturatedClass_wPsh_app Φ Ψ hΦ hΨ α).of_representable h X

end BasicLocalizer

end Representable

section Cylinder

variable (𝒲 : BasicLocalizer.{u}) {A : Type u} [SmallCategory A] [Homotopical.EZCategory A]

namespace BasicLocalizer

theorem cylinderCompatibleWith_of_forall_yoneda [Homotopical.HasTrivialAutomorphisms A]
    (𝕀 : HomotopicalAlgebra.ExactCylinder.{u} (Aᵒᵖ ⥤ Type u))
    (h : ∀ a : A, 𝒲.wPsh A (𝕀.contraction.app (yoneda.obj a))) :
    CylinderCompatibleWith (Aᵒᵖ ⥤ Type u) (𝒲.wPsh A) 𝕀 := by
  exact 𝒲.wPsh_app_of_forall_yoneda 𝕀.I (𝟭 _) (fun f _ ↦ 𝕀.I.map_mono f) (fun _ hf => hf)
    𝕀.contraction h

theorem isLocalTest_of_forall_yoneda [Homotopical.HasTrivialAutomorphisms A]
    (𝕀 : HomotopicalAlgebra.ExactCylinder.{u} (Aᵒᵖ ⥤ Type u))
    (h : ∀ a : A, 𝒲.wPsh A (𝕀.contraction.app (yoneda.obj a))) :
    𝒲.IsLocalTest A :=
  𝒲.isLocalTest_of_rlp_le A (rlp_monomorphisms_le_of_cylinderCompatibleWith (𝒲.wPsh A) 𝕀
    (𝒲.cylinderCompatibleWith_of_forall_yoneda 𝕀 h))

theorem isTest_of_forall_yoneda [Homotopical.HasTrivialAutomorphisms A]
    (hA : 𝒲.Aspherical (Cat.of A)) (𝕀 : HomotopicalAlgebra.ExactCylinder.{u} (Aᵒᵖ ⥤ Type u))
    (h : ∀ a : A, 𝒲.wPsh A (𝕀.contraction.app (yoneda.obj a))) :
    𝒲.IsTest A :=
  𝒲.isTest_of_rlp_le A hA (rlp_monomorphisms_le_of_cylinderCompatibleWith (𝒲.wPsh A) 𝕀
    (𝒲.cylinderCompatibleWith_of_forall_yoneda 𝕀 h))

end BasicLocalizer

end Cylinder

end Atoms.TestCategory
