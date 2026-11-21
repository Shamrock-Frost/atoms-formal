import Atoms.Homotopical.Cylinder.Segment
import Atoms.Homotopical.Marked.Basic

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra

namespace Atoms.Homotopical

namespace SeparatingInterval

universe w v

variable {A : Type v} [SmallCategory A] (J : SeparatingInterval.{w, v} A) (D : MarkingData A)

noncomputable def sharpEndpoint (ε : Bool) :
    𝟭 (MarkedPresheaf.{w} D) ⟶ prod.functor.obj ((MarkedPresheaf.sharp D).obj J.interval) where
  app X := (prod.lift ((MarkedPresheaf.isTerminalSharpTerminal D).from X ≫
    (MarkedPresheaf.sharp D).map (J.pt ε)) (𝟙 X) :
      X ⟶ (MarkedPresheaf.sharp D).obj J.interval ⨯ X)
  naturality X Y f := by
    change f ≫ prod.lift _ (𝟙 Y) = prod.lift _ (𝟙 X) ≫ prod.map (𝟙 _) f
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.assoc, prod.map_fst, Category.comp_id,
        prod.lift_fst, ← Category.assoc]
      congr 1
      exact (MarkedPresheaf.isTerminalSharpTerminal D).hom_ext _ _
    · rw [Category.assoc, prod.lift_snd, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
        Category.comp_id, Category.id_comp]

private noncomputable def forgetProdIso (X : MarkedPresheaf.{w} D) :
    MarkedPresheaf.forget.obj ((MarkedPresheaf.sharp D).obj J.interval ⨯ X) ≅
      MarkedPresheaf.forget.obj ((MarkedPresheaf.sharp D).obj J.interval) ⊗
        MarkedPresheaf.forget.obj X where
  hom := CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
    (MarkedPresheaf.forget.map prod.snd)
  inv := prod.lift (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _) ≫
    (PreservesLimitPair.iso MarkedPresheaf.forget _ X).inv
  hom_inv_id := by
    rw [← cancel_mono (PreservesLimitPair.iso MarkedPresheaf.forget _ X).hom,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp,
      PreservesLimitPair.iso_hom]
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, CartesianMonoidalCategory.lift_fst, prodComparison_fst]
    · rw [Category.assoc, prod.lift_snd, CartesianMonoidalCategory.lift_snd, prodComparison_snd]
  inv_hom_id := by
    have h₁ : ((PreservesLimitPair.iso MarkedPresheaf.forget
        ((MarkedPresheaf.sharp D).obj J.interval) X).inv ≫
        CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
          (MarkedPresheaf.forget.map prod.snd)) ≫ CartesianMonoidalCategory.fst _ _ =
            prod.fst := by
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst, ← prodComparison_fst,
        ← PreservesLimitPair.iso_hom, Iso.inv_hom_id_assoc]
    have h₂ : ((PreservesLimitPair.iso MarkedPresheaf.forget
        ((MarkedPresheaf.sharp D).obj J.interval) X).inv ≫
        CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
          (MarkedPresheaf.forget.map prod.snd)) ≫ CartesianMonoidalCategory.snd _ _ =
            prod.snd := by
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← prodComparison_snd,
        ← PreservesLimitPair.iso_hom, Iso.inv_hom_id_assoc]
    rw [Category.assoc]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₁, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, h₂, prod.lift_snd, Category.id_comp]

private theorem forget_map_sharpEndpoint_app_comp_forgetProdIso_hom (ε : Bool)
    (X : MarkedPresheaf.{w} D) :
    MarkedPresheaf.forget.map ((J.sharpEndpoint D ε).app X) ≫ (J.forgetProdIso D X).hom =
      (J.cylinder.endpoint ε).app (MarkedPresheaf.forget.obj X) := by
  change MarkedPresheaf.forget.map (prod.lift ((MarkedPresheaf.isTerminalSharpTerminal D).from X ≫
      (MarkedPresheaf.sharp D).map (J.pt ε)) (𝟙 X)) ≫
      CartesianMonoidalCategory.lift (MarkedPresheaf.forget.map prod.fst)
        (MarkedPresheaf.forget.map prod.snd) =
    CartesianMonoidalCategory.lift (terminal.from (MarkedPresheaf.forget.obj X) ≫ J.pt ε) (𝟙 _)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.lift_fst, ← Functor.map_comp, prod.lift_fst,
      Functor.map_comp]
    refine Eq.trans ?_ (CartesianMonoidalCategory.lift_fst _ _).symm
    exact congrArg (· ≫ J.pt ε) (terminal.hom_ext _ _)
  · rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← Functor.map_comp, prod.lift_snd,
      CategoryTheory.Functor.map_id]
    exact (CartesianMonoidalCategory.lift_snd _ _).symm

private instance mono_coprod_desc_sharpEndpoint (X : MarkedPresheaf.{w} D) :
    Mono (coprod.desc ((J.sharpEndpoint D false).app X) ((J.sharpEndpoint D true).app X)) := by
  let F := MarkedPresheaf.forget (D := D)
  rw [MarkedPresheaf.mono_iff]
  have h : coprodComparison F X X ≫
      F.map (coprod.desc ((J.sharpEndpoint D false).app X) ((J.sharpEndpoint D true).app X)) =
    J.cylinder.endpoints (F.obj X) ≫ (J.forgetProdIso D X).inv := by
    refine (Iso.eq_comp_inv _).2 ?_
    apply coprod.hom_ext
    · simp only [coprodComparison, Category.assoc, coprod.inl_desc_assoc, ← F.map_comp_assoc,
        coprod.inl_desc, ExactCylinder.inl_endpoints]
      exact J.forget_map_sharpEndpoint_app_comp_forgetProdIso_hom D false X
    · simp only [coprodComparison, Category.assoc, coprod.inr_desc_assoc, ← F.map_comp_assoc,
        coprod.inr_desc, ExactCylinder.inr_endpoints]
      exact J.forget_map_sharpEndpoint_app_comp_forgetProdIso_hom D true X
  have : F.map (coprod.desc ((J.sharpEndpoint D false).app X) ((J.sharpEndpoint D true).app X)) =
      inv (coprodComparison F X X) ≫ J.cylinder.endpoints (F.obj X) ≫
        (J.forgetProdIso D X).inv :=
    (IsIso.eq_inv_comp _).2 h
  have hm : Mono (J.cylinder.endpoints (F.obj X)) := inferInstance
  have hi : Mono (J.forgetProdIso D X).inv := inferInstance
  rw [this]
  exact @mono_comp _ _ _ _ _ _ (inferInstance : Mono (inv (coprodComparison F X X))) _
    (@mono_comp _ _ _ _ _ _ hm _ hi)

noncomputable def sharpCylinder : ExactCylinder.{max w v} (MarkedPresheaf.{w} D) where
  I := prod.functor.obj ((MarkedPresheaf.sharp D).obj J.interval)
  endpoint := J.sharpEndpoint D
  contraction :=
    { app _ := prod.snd
      naturality _ _ _ := prod.map_snd _ _ }
  endpoint_contraction ε := by
    ext X : 2
    exact prod.lift_snd _ _
  mono_endpoints _ := inferInstance
  preservesMonomorphisms := ⟨fun f _ => inferInstanceAs (Mono (prod.map (𝟙 _) f))⟩
  preservesColimits := (Adjunction.ofIsLeftAdjoint _).leftAdjoint_preservesColimits

noncomputable def sharpCylinderForgetIso :
    (J.sharpCylinder D).I ⋙ MarkedPresheaf.forget ≅ MarkedPresheaf.forget ⋙ J.cylinder.I :=
  NatIso.ofComponents (J.forgetProdIso D) fun {X Y} f => by
    change MarkedPresheaf.forget.map (prod.map (𝟙 ((MarkedPresheaf.sharp D).obj J.interval)) f) ≫
        (J.forgetProdIso D Y).hom =
      (J.forgetProdIso D X).hom ≫ (_ ◁ MarkedPresheaf.forget.map f)
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst]
      change _ ≫ CartesianMonoidalCategory.lift _ _ ≫ _ = CartesianMonoidalCategory.lift _ _ ≫ _
      rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst,
        ← Functor.map_comp, prod.map_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd]
      change _ ≫ CartesianMonoidalCategory.lift _ _ ≫ _ =
        CartesianMonoidalCategory.lift _ _ ≫ _ ≫ _
      rw [CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.lift_snd_assoc,
        ← Functor.map_comp, ← Functor.map_comp, prod.map_snd]

@[reassoc]
theorem whiskerRight_endpoint_forget_comp_sharpCylinderForgetIso_hom (ε : Bool) :
    Functor.whiskerRight ((J.sharpCylinder D).endpoint ε) MarkedPresheaf.forget ≫
        (J.sharpCylinderForgetIso D).hom =
      Functor.whiskerLeft MarkedPresheaf.forget (J.cylinder.endpoint ε) := by
  ext X : 2
  exact J.forget_map_sharpEndpoint_app_comp_forgetProdIso_hom D ε X

@[reassoc]
theorem sharpCylinderForgetIso_hom_comp_whiskerLeft_contraction :
    (J.sharpCylinderForgetIso D).hom ≫
        Functor.whiskerLeft MarkedPresheaf.forget J.cylinder.contraction =
      Functor.whiskerRight (J.sharpCylinder D).contraction MarkedPresheaf.forget := by
  ext X : 2
  exact CartesianMonoidalCategory.lift_snd _ _

end SeparatingInterval

end Atoms.Homotopical
