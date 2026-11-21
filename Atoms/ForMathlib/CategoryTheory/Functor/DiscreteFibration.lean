import Atoms.ForMathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory.Functor

structure IsDiscreteFibration {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) : Prop where
  exists_lift : ∀ {c : C} {d : D} (g : d ⟶ F.obj c),
    ∃ (c' : C) (f : c' ⟶ c) (e : F.obj c' = d), F.map f = eqToHom e ≫ g
  lift_unique : ∀ {c c₁ c₂ : C} (f₁ : c₁ ⟶ c) (f₂ : c₂ ⟶ c) (e : F.obj c₁ = F.obj c₂),
    F.map f₁ = eqToHom e ≫ F.map f₂ → ∃ e' : c₁ = c₂, f₁ = eqToHom e' ≫ f₂

theorem IsDiscreteFibration.map_injective {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} (hF : IsDiscreteFibration F) {c c' : C} {f₁ f₂ : c' ⟶ c}
    (h : F.map f₁ = F.map f₂) : f₁ = f₂ := by
  obtain ⟨e, he⟩ := hF.lift_unique f₁ f₂ rfl (by simpa using h)
  simpa using he

end CategoryTheory.Functor

namespace CategoryTheory

open Opposite

theorem isDiscreteFibration_costructuredArrow_map {C : Type u₁} [Category.{v₁} C] {E : Type u₂}
    [Category.{v₂} E] (S : C ⥤ E) {X Y : E} (p : X ⟶ Y) :
    Functor.IsDiscreteFibration (CostructuredArrow.map (S := S) p) where
  exists_lift {c} d g := by
    obtain ⟨dl, ⟨⟨⟩⟩, dh⟩ := d
    have hg : S.map g.left ≫ c.hom ≫ p = dh := CostructuredArrow.w g
    refine ⟨CostructuredArrow.mk (Y := dl) (S.map g.left ≫ c.hom),
      CostructuredArrow.homMk g.left rfl, ?_, ?_⟩
    · rw [CostructuredArrow.map_mk, Category.assoc, hg]
      rfl
    · ext
      simp
  lift_unique {c} c₁ c₂ f₁ f₂ e H := by
    obtain ⟨l₁, ⟨⟨⟩⟩, h₁⟩ := c₁
    obtain ⟨l₂, ⟨⟨⟩⟩, h₂⟩ := c₂
    obtain rfl : l₁ = l₂ := congrArg Comma.left e
    have hf : f₁.left = f₂.left := by simpa using congrArg CommaMorphism.left H
    have w₁ : S.map f₁.left ≫ c.hom = h₁ := CostructuredArrow.w f₁
    have w₂ : S.map f₂.left ≫ c.hom = h₂ := CostructuredArrow.w f₂
    obtain rfl : h₁ = h₂ := by rw [← w₁, ← w₂, hf]
    refine ⟨rfl, ?_⟩
    ext
    simpa using hf

theorem isDiscreteFibration_elements_map {C : Type u₁} [Category.{v₁} C] {X Y : C ⥤ Type w}
    (p : X ⟶ Y) : Functor.IsDiscreteFibration (CategoryOfElements.map p).op where
  exists_lift {c} d g := by
    let e' : X.Elements := X.elementsMk d.unop.1 (X.map g.unop.1 c.unop.2)
    refine ⟨op e', (CategoryOfElements.homMk c.unop e' g.unop.1 rfl).op, ?_, ?_⟩
    · change op (Y.elementsMk d.unop.1 (p.app _ (X.map g.unop.1 c.unop.2))) = op d.unop
      congr 1
      refine Functor.Elements.ext _ _ rfl ?_
      simp only [eqToHom_refl, Functor.map_id_apply]
      exact (NatTrans.naturality_apply p g.unop.1 c.unop.2).trans g.unop.2
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      simp only [Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op, CategoryOfElements.map_map_coe,
        unop_comp, eqToHom_unop, CategoryOfElements.comp_val, CategoryOfElements.eqToHom_val]
      exact (Category.comp_id _).symm
  lift_unique {c} c₁ c₂ f₁ f₂ e H := by
    have ha : c₁.unop.1 = c₂.unop.1 := congrArg (fun z => z.unop.1) e
    have hf : f₁.unop.1 = f₂.unop.1 ≫ eqToHom ha.symm := by
      have := congrArg (fun m => m.unop.val) H
      simp only [unop_comp, CategoryOfElements.comp_val, eqToHom_unop,
        CategoryOfElements.eqToHom_val] at this
      exact this
    have hx : X.map (eqToHom ha) c₁.unop.2 = c₂.unop.2 := by
      rw [← f₁.unop.2, ← f₂.unop.2, hf]
      simp
    obtain rfl : c₁ = c₂ := Opposite.unop_injective (Functor.Elements.ext _ _ ha hx)
    refine ⟨rfl, ?_⟩
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simpa using hf

theorem isDiscreteFibration_elements_proj {C : Type u₁} [Category.{v₁} C] (X : Cᵒᵖ ⥤ Type w) :
    Functor.IsDiscreteFibration (CategoryOfElements.π X).leftOp where
  exists_lift {c} d g := by
    let e' : X.Elements := X.elementsMk (op d) (X.map g.op c.unop.2)
    refine ⟨op e', (CategoryOfElements.homMk c.unop e' g.op rfl).op, rfl, ?_⟩
    exact (Category.id_comp g).symm
  lift_unique {c} c₁ c₂ f₁ f₂ e H := by
    obtain ⟨⟨⟨a₁⟩, x₁⟩⟩ := c₁
    obtain ⟨⟨⟨a₂⟩, x₂⟩⟩ := c₂
    change a₁ = a₂ at e
    subst e
    have hf : f₁.unop.val = f₂.unop.val := by
      have := Quiver.Hom.unop_inj (H.trans (Category.id_comp _))
      exact this
    have hx : x₁ = x₂ := by
      have h1 : X.map f₁.unop.val c.unop.2 = x₁ := f₁.unop.2
      have h2 : X.map f₂.unop.val c.unop.2 = x₂ := f₂.unop.2
      rw [← h1, ← h2, hf]
    subst hx
    refine ⟨rfl, ?_⟩
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simpa using hf

end CategoryTheory
