import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Anodyne
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.ForMathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra

namespace Atoms.Homotopical

universe w v u₁ v₁ w₁ u₂ v₂

variable {A : Type v} [SmallCategory A] (L : Aᵒᵖ ⥤ Type (max w v))

noncomputable def segmentEndpoint (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L) :
    𝟭 (Aᵒᵖ ⥤ Type (max w v)) ⟶ tensorLeft L where
  app X := CartesianMonoidalCategory.lift (terminal.from X ≫ p) (𝟙 X)
  naturality X Y f := by
    apply CartesianMonoidalCategory.hom_ext <;> simp

def segmentContraction : tensorLeft L ⟶ 𝟭 (Aᵒᵖ ⥤ Type (max w v)) where
  app X := CartesianMonoidalCategory.snd L X
  naturality X Y f := by simp

theorem segmentEndpoint_app_fst (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L) (X : Aᵒᵖ ⥤ Type (max w v)) :
    (segmentEndpoint L p).app X ≫ CartesianMonoidalCategory.fst L X = terminal.from X ≫ p :=
  CartesianMonoidalCategory.lift_fst _ _

theorem segmentEndpoint_app_snd (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L) (X : Aᵒᵖ ⥤ Type (max w v)) :
    (segmentEndpoint L p).app X ≫ CartesianMonoidalCategory.snd L X = 𝟙 X :=
  CartesianMonoidalCategory.lift_snd _ _

theorem segmentEndpoint_segmentContraction (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L) :
    segmentEndpoint L p ≫ segmentContraction L = 𝟙 _ := by
  ext X : 2
  exact segmentEndpoint_app_snd L p X

theorem isPullback_of_app_ne {B : Type u₁} [Category.{v₁} B] {L : Bᵒᵖ ⥤ Type w₁}
    (pt : Bool → (⊤_ (Bᵒᵖ ⥤ Type w₁) ⟶ L))
    (h : ∀ (a : Bᵒᵖ) (t₀ t₁ : (⊤_ (Bᵒᵖ ⥤ Type w₁)).obj a),
      (pt false).app a t₀ ≠ (pt true).app a t₁) :
    IsPullback (initial.to (⊤_ (Bᵒᵖ ⥤ Type w₁))) (initial.to (⊤_ (Bᵒᵖ ⥤ Type w₁)))
      (pt false) (pt true) := by
  refine IsPullback.of_forall_isPullback_app fun a ↦ (Types.isPullback_iff _ _ _ _).2
    ⟨?_, fun x _ _ ↦ (FunctorToTypes.isEmpty_initial_obj a).elim x,
      fun x₂ x₃ he ↦ absurd he (h a x₂ x₃)⟩
  exact ConcreteCategory.hom_ext _ _ fun x ↦ (FunctorToTypes.isEmpty_initial_obj a).elim x

variable (A) in
structure SeparatingInterval where
  interval : Aᵒᵖ ⥤ Type (max w v)
  pt : Bool → ((⊤_ (Aᵒᵖ ⥤ Type (max w v))) ⟶ interval)
  isPullback : IsPullback (initial.to (⊤_ (Aᵒᵖ ⥤ Type (max w v))))
    (initial.to (⊤_ (Aᵒᵖ ⥤ Type (max w v)))) (pt false) (pt true)

namespace SeparatingInterval

variable (J : SeparatingInterval.{w, v} A)

theorem app_ne_app (a : Aᵒᵖ) (t₀ t₁ : (⊤_ (Aᵒᵖ ⥤ Type (max w v))).obj a) :
    (J.pt false).app a t₀ ≠ (J.pt true).app a t₁ := by
  intro he
  obtain ⟨x, -⟩ :=
    Types.exists_of_isPullback (J.isPullback.map ((evaluation _ _).obj a)) t₀ t₁ he
  exact (FunctorToTypes.isEmpty_initial_obj a).false x

end SeparatingInterval

theorem mono_segmentEndpoints (J : SeparatingInterval.{w, v} A) (X : Aᵒᵖ ⥤ Type (max w v)) :
    Mono (coprod.desc ((segmentEndpoint J.interval (J.pt false)).app X)
      ((segmentEndpoint J.interval (J.pt true)).app X)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [mono_iff_injective]
  set L := J.interval
  set d := coprod.desc ((segmentEndpoint L (J.pt false)).app X)
    ((segmentEndpoint L (J.pt true)).app X)
  have hc := (isColimitMapCoconeBinaryCofanEquiv ((evaluation _ _).obj a) _ _)
    (isColimitOfPreserves ((evaluation _ _).obj a) (coprodIsCoprod X X))
  obtain ⟨-, -, hcompl⟩ := (Types.binaryCofan_isColimit_iff _).mp ⟨hc⟩
  have hcover : ∀ z : (X ⨿ X).obj a, ∃ (ε : Bool) (x : X.obj a),
      (cond ε coprod.inr coprod.inl : X ⟶ X ⨿ X).app a x = z := by
    intro z
    rcases Set.eq_univ_iff_forall.mp hcompl.sup_eq_top z with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨false, x, hx⟩
    · exact ⟨true, x, hx⟩
  have hι (ε : Bool) (x : X.obj a) :
      d.app a ((cond ε coprod.inr coprod.inl : X ⟶ X ⨿ X).app a x) =
        ((segmentEndpoint L (J.pt ε)).app X).app a x := by
    cases ε
    · rw [Bool.cond_false, ← NatTrans.comp_app_apply, coprod.inl_desc]
    · rw [Bool.cond_true, ← NatTrans.comp_app_apply, coprod.inr_desc]
  have hsnd (ε : Bool) (x : X.obj a) : (CartesianMonoidalCategory.snd L X).app a
      (((segmentEndpoint L (J.pt ε)).app X).app a x) = x := by
    rw [← NatTrans.comp_app_apply, segmentEndpoint_app_snd]
    rfl
  have hfst (ε : Bool) (x : X.obj a) : (CartesianMonoidalCategory.fst L X).app a
      (((segmentEndpoint L (J.pt ε)).app X).app a x) =
        (J.pt ε).app a ((terminal.from X).app a x) := by
    rw [← NatTrans.comp_app_apply, segmentEndpoint_app_fst, NatTrans.comp_app_apply]
  intro z₁ z₂ hz
  obtain ⟨ε₁, x₁, rfl⟩ := hcover z₁
  obtain ⟨ε₂, x₂, rfl⟩ := hcover z₂
  rw [hι, hι] at hz
  by_cases hε : ε₁ = ε₂
  · subst hε
    have := congrArg ((CartesianMonoidalCategory.snd L X).app a) hz
    rw [hsnd, hsnd] at this
    rw [this]
  · exfalso
    have := congrArg ((CartesianMonoidalCategory.fst L X).app a) hz
    rw [hfst, hfst] at this
    cases ε₁ <;> cases ε₂
    · exact hε rfl
    · exact J.app_ne_app a _ _ this
    · exact J.app_ne_app a _ _ this.symm
    · exact hε rfl

@[simps I endpoint contraction]
noncomputable def SeparatingInterval.cylinder (J : SeparatingInterval.{w, v} A) :
    ExactCylinder.{max w v} (Aᵒᵖ ⥤ Type (max w v)) where
  I := tensorLeft J.interval
  endpoint ε := segmentEndpoint J.interval (J.pt ε)
  contraction := segmentContraction J.interval
  endpoint_contraction ε := segmentEndpoint_segmentContraction J.interval (J.pt ε)
  mono_endpoints := mono_segmentEndpoints J
  preservesMonomorphisms := inferInstance

noncomputable def SeparatingInterval.ofFunctor {C : Type u₂} [Category.{v₂} C] [HasTerminal C]
    [HasInitial C] {L : C} (pt : Bool → (⊤_ C ⟶ L))
    (h : IsPullback (initial.to (⊤_ C)) (initial.to (⊤_ C)) (pt false) (pt true))
    (F : C ⥤ (Aᵒᵖ ⥤ Type (max w v))) [PreservesLimitsOfShape (Discrete PEmpty.{1}) F]
    [PreservesLimitsOfShape WalkingCospan F] (hI : IsInitial (F.obj (⊥_ C))) :
    SeparatingInterval.{w, v} A where
  interval := F.obj L
  pt b := (PreservesTerminal.iso F).inv ≫ F.map (pt b)
  isPullback := by
    let eI : F.obj (⊥_ C) ≅ ⊥_ (Aᵒᵖ ⥤ Type (max w v)) := (initialIsoIsInitial hI).symm
    refine (h.map F).of_iso eI (PreservesTerminal.iso F) (PreservesTerminal.iso F) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact (cancel_epi eI.inv).1 (initial.hom_ext _ _)
    · exact (cancel_epi eI.inv).1 (initial.hom_ext _ _)
    all_goals rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

section ProductHomotopy

variable (J : SeparatingInterval.{w, v} A)

theorem segmentEndpoint_app_prod_lift (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L)
    (Z X : Aᵒᵖ ⥤ Type (max w v)) :
    (segmentEndpoint L p).app (Z ⨯ X) ≫
        CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst L (Z ⨯ X))
          (CartesianMonoidalCategory.snd L (Z ⨯ X) ≫ Limits.prod.snd) =
      Limits.prod.snd ≫ (segmentEndpoint L p).app X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, segmentEndpoint_app_fst]
    rw [← Category.assoc]
    exact congrArg (· ≫ p) (terminal.hom_ext _ _)
  · rw [Category.assoc, CartesianMonoidalCategory.lift_snd, ← Category.assoc,
      segmentEndpoint_app_snd, Category.assoc, segmentEndpoint_app_snd]
    simp

theorem segmentEndpoint_app_comp_prod_lift (p : ⊤_ (Aᵒᵖ ⥤ Type (max w v)) ⟶ L)
    (Z : Aᵒᵖ ⥤ Type (max w v)) {X Y : Aᵒᵖ ⥤ Type (max w v)} (k : L ⊗ X ⟶ Y) :
    (segmentEndpoint L p).app (Z ⨯ X) ≫
        Limits.prod.lift (CartesianMonoidalCategory.snd L (Z ⨯ X) ≫ Limits.prod.fst)
          (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst L (Z ⨯ X))
            (CartesianMonoidalCategory.snd L (Z ⨯ X) ≫ Limits.prod.snd) ≫ k) =
      Limits.prod.map (𝟙 Z) ((segmentEndpoint L p).app X ≫ k) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, Limits.prod.lift_fst, Limits.prod.map_fst, Category.comp_id,
      ← Category.assoc, segmentEndpoint_app_snd]
    simp
  · rw [Category.assoc, Limits.prod.lift_snd, Limits.prod.map_snd, ← Category.assoc,
      segmentEndpoint_app_prod_lift, Category.assoc]

theorem SeparatingInterval.cylinder_elementaryHomotopy_prod_map (Z : Aᵒᵖ ⥤ Type (max w v))
    {X Y : Aᵒᵖ ⥤ Type (max w v)} {f g : X ⟶ Y} (hfg : J.cylinder.ElementaryHomotopy f g) :
    J.cylinder.ElementaryHomotopy (Limits.prod.map (𝟙 Z) f) (Limits.prod.map (𝟙 Z) g) := by
  obtain ⟨k, h₀, h₁⟩ := hfg
  change J.interval ⊗ X ⟶ Y at k
  change (segmentEndpoint J.interval (J.pt false)).app X ≫ k = f at h₀
  change (segmentEndpoint J.interval (J.pt true)).app X ≫ k = g at h₁
  refine ⟨Limits.prod.lift
    (CartesianMonoidalCategory.snd J.interval (Z ⨯ X) ≫ Limits.prod.fst)
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst J.interval (Z ⨯ X))
      (CartesianMonoidalCategory.snd J.interval (Z ⨯ X) ≫ Limits.prod.snd) ≫ k), ?_, ?_⟩
  · exact (segmentEndpoint_app_comp_prod_lift J.interval (J.pt false) Z k).trans (by rw [h₀])
  · exact (segmentEndpoint_app_comp_prod_lift J.interval (J.pt true) Z k).trans (by rw [h₁])

theorem SeparatingInterval.cylinder_homotopic_prod_map (Z : Aᵒᵖ ⥤ Type (max w v))
    {X Y : Aᵒᵖ ⥤ Type (max w v)} {f g : X ⟶ Y} (hfg : J.cylinder.Homotopic f g) :
    J.cylinder.Homotopic (Limits.prod.map (𝟙 Z) f) (Limits.prod.map (𝟙 Z) g) :=
  ExactCylinder.Homotopic.map _ (Limits.prod.map (𝟙 Z) ·)
    (fun _ _ ↦ J.cylinder_elementaryHomotopy_prod_map Z) hfg

end ProductHomotopy

end Atoms.Homotopical
