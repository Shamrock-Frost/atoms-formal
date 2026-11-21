import Atoms.ForMathlib.CategoryTheory.Elements
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Types.Monomorphisms

namespace CategoryTheory

universe w v u

theorem mono_nerveMap_of_faithful {C D : Type u} [Category.{v} C] [Category.{v} D] (G : C ⥤ D)
    [G.Faithful] (hG : Function.Injective G.obj) : Mono (nerveMap G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  change x ⋙ G = y ⋙ G at h
  exact Functor.ext_of_comp_faithful G (fun i ↦ hG (Functor.congr_obj h i)) h

theorem nerveMap_functor_eq {X Y : Type u} [Preorder X] [Preorder Y] {f g : X → Y}
    (hf : Monotone f) (hg : Monotone g) (h : ∀ x, f x = g x) :
    nerveMap hf.functor = nerveMap hg.functor := by
  obtain rfl := funext h
  rfl

open Limits

section Iic

variable (X : Type u) [Preorder X]

def iicNerveDiagram : X ⥤ SSet.{u} where
  obj x := nerve (Set.Iic x)
  map f := nerveMap (Monotone.functor (f := Set.inclusion (Set.Iic_subset_Iic.2 (leOfHom f)))
    fun _ _ h => h)
  map_id _ := rfl
  map_comp _ _ := rfl

def iicNerveCocone : Cocone (iicNerveDiagram X) where
  pt := nerve X
  ι := { app x := nerveMap (Monotone.functor (f := Subtype.val (p := (· ∈ Set.Iic x)))
    fun _ _ h => h) }

variable {X}

def nerveIicLift {n : SimplexCategoryᵒᵖ} (σ : (nerve X).obj n) :
    (nerve (Set.Iic σ.right)).obj n :=
  Monotone.functor (f := fun i => (⟨σ.obj i, leOfHom (σ.map (homOfLE (Fin.le_last i)))⟩ :
    Set.Iic σ.right)) fun _ _ hij => leOfHom (σ.map (homOfLE hij))

private theorem nerveMap_app_nerveIicLift {n : SimplexCategoryᵒᵖ} (σ : (nerve X).obj n) :
    ((iicNerveCocone X).ι.app σ.right).app n (nerveIicLift σ) = σ :=
  nerve.ext_of_isThin rfl

private theorem ιColimitType_eq_ιColimitType_nerveIicLift (n : SimplexCategoryᵒᵖ) (x : X)
    (τ : (iicNerveDiagram X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).obj x) :
    (iicNerveDiagram X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).ιColimitType x τ =
      (iicNerveDiagram X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).ιColimitType _
        (nerveIicLift (((iicNerveCocone X).ι.app x).app n τ)) := by
  refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (𝟙 x)
    (homOfLE (ComposableArrows.right (n := n.unop.len) τ).2) ?_
  exact nerve.ext_of_isThin (C := Set.Iic x) rfl

private theorem bijective_descColimitType_iicNerveCocone (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (Functor.descColimitType _
      ((Functor.coconeTypesEquiv _).symm
        (((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone (iicNerveCocone X)))) := by
  refine ⟨fun a b hab => ?_, fun σ => ⟨(iicNerveDiagram X ⋙
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).ιColimitType _ (nerveIicLift σ),
      nerveMap_app_nerveIicLift σ⟩⟩
  obtain ⟨x, τ, rfl⟩ := Functor.ιColimitType_jointly_surjective _ a
  obtain ⟨y, τ', rfl⟩ := Functor.ιColimitType_jointly_surjective _ b
  change ((iicNerveCocone X).ι.app x).app n τ = ((iicNerveCocone X).ι.app y).app n τ' at hab
  have key : ∀ σ σ' : (nerve X).obj n, σ = σ' →
      (iicNerveDiagram X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).ιColimitType _
        (nerveIicLift σ) =
      (iicNerveDiagram X ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).ιColimitType _
        (nerveIicLift σ') := by
    rintro σ _ rfl
    rfl
  exact (ιColimitType_eq_ιColimitType_nerveIicLift n x τ).trans
    ((key _ _ hab).trans (ιColimitType_eq_ιColimitType_nerveIicLift n y τ').symm)

noncomputable def isColimitIicNerveCocone : IsColimit (iicNerveCocone X) :=
  evaluationJointlyReflectsColimits _ fun n => Nonempty.some <|
    (Types.isColimit_iff_coconeTypesIsColimit _).2
      ⟨bijective_descColimitType_iicNerveCocone n⟩

end Iic

open MonoidalCategory Simplicial in
def nerveHomotopy {X : Type v} [Preorder X] (h : ULift.{max u v} (Fin 2) × X →o X) :
    (Δ[1] ⊗ nerve (ULift.{u} X) : SSet.{max u v}) ⟶ nerve (ULift.{u} X) where
  app k := ↾fun z ↦ Monotone.functor (f := fun i ↦ ULift.up (h
      (((SSet.stdSimplex.isoNerve 1).hom.app k z.1).obj i, (z.2.obj i).down)))
    fun _ _ hle ↦ h.monotone
      ⟨leOfHom (((SSet.stdSimplex.isoNerve 1).hom.app k z.1).map (homOfLE hle)),
        ULift.down_le.2 (leOfHom (z.2.map (homOfLE hle)))⟩
  naturality k m f := by
    ext z i
    exact congrArg (fun a : (nerve (ULift.{max u v} (Fin 2))).obj m ↦
      h (a.obj i, (((nerve _).map f z.2).obj i).down))
      (NatTrans.naturality_apply (SSet.stdSimplex.isoNerve 1).hom f z.1)

section Elements

variable {C : Type u} [Category.{v} C]

def CategoryOfElements.nerveAsSmallIso (X : Cᵒᵖ ⥤ Type w) :
    nerve (AsSmall.down.op ⋙ X : (AsSmall.{w} C)ᵒᵖ ⥤ Type w).Elementsᵒᵖ ≅ nerve X.Elementsᵒᵖ :=
  NatIso.ofComponents (fun _ ↦
    { hom := TypeCat.ofHom fun s ↦ ((asSmallFunctor X).op.mapComposableArrows _).obj s
      inv := TypeCat.ofHom fun s ↦ ((asSmallInverse X).op.mapComposableArrows _).obj s
      hom_inv_id := rfl
      inv_hom_id := rfl }) fun _ ↦ rfl

end Elements

end CategoryTheory

universe u

namespace SSet

open CategoryTheory Simplicial

theorem existsUnique_extend_boundary_of_isCoskeletal {X : SSet.{u}}
    [SimplicialObject.IsCoskeletal X 2] {n : ℕ} (b : (∂Δ[n + 3] : SSet.{u}) ⟶ X) :
    ∃! v : Δ[n + 3] ⟶ X, (∂Δ[n + 3]).ι ≫ v = b := by
  have hι : IsIso ((SimplicialObject.truncation 2).map
      (∂Δ[n + 3] : (Δ[n + 3] : SSet.{u}).Subcomplex).ι) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨k, hk⟩⟩
    induction k using SimplexCategory.rec with | _ k => ?_
    rw [isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun s ↦ ⟨⟨s, ?_⟩, rfl⟩⟩
    have h := boundary_obj_eq_univ.{u} k (n + 3) (by simp only at hk; omega)
    exact (Set.ext_iff.1 h s).2 trivial
  let e (Y : SSet.{u}) : (Y ⟶ X) ≃
      ((SimplicialObject.truncation 2).obj Y ⟶ (SimplicialObject.truncation 2).obj X) :=
    (Iso.homCongr (Iso.refl Y) (X.isoCoskOfIsCoskeletal 2)).trans
      ((SimplicialObject.coskAdj 2).homEquiv _ _).symm
  have he {Y Y' : SSet.{u}} (f : Y' ⟶ Y) (g : Y ⟶ X) :
      e Y' (f ≫ g) = (SimplicialObject.truncation 2).map f ≫ e Y g := by
    simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  refine ⟨(e _).symm (inv ((SimplicialObject.truncation 2).map (∂Δ[n + 3]).ι) ≫ e _ b), ?_,
    fun v hv ↦ (e _).injective ?_⟩
  · refine (e _).injective ?_
    rw [he, Equiv.apply_symm_apply, IsIso.hom_inv_id_assoc]
  · rw [Equiv.apply_symm_apply, ← hv, he, IsIso.inv_hom_id_assoc]

end SSet
