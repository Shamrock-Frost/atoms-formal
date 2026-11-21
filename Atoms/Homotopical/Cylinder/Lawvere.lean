import Atoms.ForMathlib.CategoryTheory.Sites.Closed
import Atoms.Homotopical.Cylinder.Segment
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Topos.Sheaf

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable (A : Type v) [SmallCategory A]

def lawverePoint (b : Bool) : ⊤_ (Aᵒᵖ ⥤ Type v) ⟶ Functor.sieves A where
  app a := ↾fun _ ↦ (cond b ⊥ ⊤ : Sieve a.unop)
  naturality a a' g := by
    cases b <;> ext x <;> exact Sieve.ext fun _ _ ↦ Iff.rfl

theorem isPullback_lawverePoint :
    IsPullback (initial.to (⊤_ (Aᵒᵖ ⥤ Type v))) (initial.to (⊤_ (Aᵒᵖ ⥤ Type v)))
      (lawverePoint A false) (lawverePoint A true) := by
  refine isPullback_of_app_ne _ fun a _ _ h ↦ ?_
  have h' : (⊤ : Sieve a.unop) = ⊥ := h
  exact absurd (congrArg (fun S : Sieve a.unop ↦ S (𝟙 _)) h') (by simp)

def lawvereInterval : SeparatingInterval A :=
  ⟨Functor.sieves A, lawverePoint A, isPullback_lawverePoint A⟩

noncomputable def lawvereCylinder : ExactCylinder.{v} (Aᵒᵖ ⥤ Type v) :=
  (lawvereInterval A).cylinder

variable {A}

def lawvereExtension {K X : Aᵒᵖ ⥤ Type v} (m : K ⟶ X) (φ : K ⟶ Functor.sieves A) :
    X ⟶ Functor.sieves A where
  app a := ↾fun x ↦ (
    { arrows := fun b g ↦ ∃ k : K.obj (Opposite.op b),
        m.app _ k = X.map g.op x ∧ @Eq (Sieve b) (φ.app _ k) ⊤
      downward_closed := by
        rintro b c g ⟨k, hk, hφ⟩ h
        refine ⟨K.map h.op k, ?_, NatTrans.app_map_eq_top_of_app_eq_top φ h.op hφ⟩
        rw [NatTrans.naturality_apply, hk, op_comp, Functor.map_comp_apply] } :
      Sieve a.unop)
  naturality a a' f := by
    ext x
    refine Sieve.ext fun b g ↦ ?_
    change (∃ k, _ ∧ _) ↔ ∃ k, _ ∧ _
    rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]
    exact Iff.rfl

theorem mem_lawvereExtension_iff {K X : Aᵒᵖ ⥤ Type v} (m : K ⟶ X) (φ : K ⟶ Functor.sieves A)
    {a : Aᵒᵖ} (x : X.obj a) {b : A} (g : b ⟶ a.unop) :
    Sieve.arrows (X := a.unop) ((lawvereExtension m φ).app a x) g ↔
      ∃ k : K.obj (Opposite.op b), m.app _ k = X.map g.op x ∧ @Eq (Sieve b) (φ.app _ k) ⊤ :=
  Iff.rfl

theorem comp_lawvereExtension {K X : Aᵒᵖ ⥤ Type v} (m : K ⟶ X) [Mono m]
    (φ : K ⟶ Functor.sieves A) : m ≫ lawvereExtension m φ = φ := by
  refine NatTrans.ext (funext fun a ↦ ConcreteCategory.hom_ext _ _ fun k ↦ ?_)
  have hinj (b : Aᵒᵖ) : Function.Injective (m.app b) :=
    (mono_iff_injective (m.app b)).1 inferInstance
  refine Sieve.ext fun b g ↦ (mem_lawvereExtension_iff m φ (m.app a k) g).trans ?_
  rw [← NatTrans.naturality_apply]
  constructor
  · rintro ⟨k', hk', hφ⟩
    rw [hinj _ hk', NatTrans.naturality_apply] at hφ
    rw [← Category.id_comp g]
    exact (Sieve.id_mem_iff_eq_top).2 (hφ : Sieve.pullback g (φ.app a k) = ⊤)
  · intro hg
    refine ⟨K.map g.op k, rfl, ?_⟩
    rw [NatTrans.naturality_apply]
    exact Sieve.pullback_eq_top_of_mem _ hg

variable (A)

instance injective_sieves : Injective (Functor.sieves A) :=
  ⟨fun φ m _ ↦ ⟨lawvereExtension m φ, comp_lawvereExtension m φ⟩⟩

theorem rlp_monomorphisms_terminal_from_sieves :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (terminal.from (Functor.sieves A)) := by
  intro K X m hm
  have : Mono m := hm
  exact ⟨fun {f _} _ ↦
    ⟨⟨⟨lawvereExtension m f, comp_lawvereExtension m f, terminal.hom_ext _ _⟩⟩⟩⟩

theorem rlp_monomorphisms_lawvereCylinder_contraction (X : Aᵒᵖ ⥤ Type v) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp
      ((lawvereCylinder A).contraction.app X) := by
  have h : IsPullback (CartesianMonoidalCategory.fst (Functor.sieves A) X)
      (CartesianMonoidalCategory.snd (Functor.sieves A) X) (terminal.from (Functor.sieves A))
      (terminal.from X) :=
    IsPullback.of_is_product
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct (Functor.sieves A) X)
      terminalIsTerminal
  exact (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp.of_isPullback h
    (rlp_monomorphisms_terminal_from_sieves A)

end Atoms.Homotopical
