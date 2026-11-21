import Atoms.ForMathlib.CategoryTheory.Category.Cat.Comma
import Atoms.TestCategory.BasicLocalizer.Basic

open CategoryTheory Limits

namespace Atoms.TestCategory

universe u

def interval : Cat.{u, u} := Cat.of (ULift.{u} Bool)

instance : HasTerminal interval.{u} :=
  IsTerminal.hasTerminal (X := (show interval.{u} from ULift.up true))
    (IsTerminal.ofUniqueHom
      (fun X => homOfLE (X := ULift.{u} Bool) (show X.down ≤ true from Bool.le_true _))
      (fun _ _ => rfl))

theorem down_le_of_intervalHom {p q : interval.{u}} (f : p ⟶ q) : p.down ≤ q.down :=
  leOfHom (X := ULift.{u} Bool) f

section Homotopy

variable {A B : Cat.{u, u}} {F G : ↥A ⥤ ↥B} (α : F ⟶ G)

private def natTransHomotopyObj (F G : ↥A ⥤ ↥B) : Bool → ↥A → ↥B
  | false, x => F.obj x
  | true, x => G.obj x

private def natTransHomotopyMap : (s t : Bool) → s ≤ t → {x y : ↥A} → (x ⟶ y) →
    (natTransHomotopyObj F G s x ⟶ natTransHomotopyObj F G t y)
  | false, false, _, _, _, f => F.map f
  | false, true, _, _, y, f => F.map f ≫ α.app y
  | true, true, _, _, _, f => G.map f
  | true, false, h, _, _, _ => absurd h (by decide)

def natTransHomotopy : Cat.of (↥A × ↥interval.{u}) ⟶ B :=
  Functor.toCatHom
    { obj := fun p => natTransHomotopyObj F G p.2.down p.1
      map := fun {p q} f =>
        natTransHomotopyMap α p.2.down q.2.down (down_le_of_intervalHom f.2) f.1
      map_id := fun p => by
        rcases p with ⟨x, ⟨_ | _⟩⟩ <;> simp [natTransHomotopyMap, natTransHomotopyObj]
      map_comp := fun {p q r} f g => by
        have hf := down_le_of_intervalHom f.2
        have hg := down_le_of_intervalHom g.2
        rcases p with ⟨x, ⟨_ | _⟩⟩ <;> rcases q with ⟨y, ⟨_ | _⟩⟩ <;>
          rcases r with ⟨z, ⟨_ | _⟩⟩
        · simp [natTransHomotopyMap, natTransHomotopyObj]
        · simp [natTransHomotopyMap, natTransHomotopyObj]
        · exact absurd hg (by simp)
        · simp [natTransHomotopyMap, natTransHomotopyObj]
        · exact absurd hf (by simp)
        · exact absurd hf (by simp)
        · exact absurd hg (by simp)
        · simp [natTransHomotopyMap, natTransHomotopyObj] }

end Homotopy

def intervalInclusion (A : Cat.{u, u}) (ε : Bool) : A ⟶ Cat.of (↥A × ↥interval.{u}) :=
  (CategoryTheory.Prod.sectL ↥A (show ↥interval.{u} from ULift.up ε)).toCatHom

theorem intervalInclusion_comp_fst (A : Cat.{u, u}) (ε : Bool) :
    intervalInclusion A ε ≫ (CategoryTheory.Prod.fst ↥A ↥interval.{u}).toCatHom = 𝟙 A :=
  rfl

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u})

theorem asphericalFunctor_sliceFstSnd (A B : Cat.{u, u}) (a : A) :
    𝒲.AsphericalFunctor (Cat.sliceFstSnd A B a) := fun b => by
  let top : CostructuredArrow (Cat.sliceFstSnd A B a).toFunctor b :=
    CostructuredArrow.mk
      (Y := (CostructuredArrow.mk (Y := ((a, b) : Cat.of (↥A × ↥B))) (𝟙 a) :
        Cat.of (CostructuredArrow (CategoryTheory.Prod.fst ↥A ↥B) a))) (𝟙 b)
  have : HasTerminal (Cat.of (CostructuredArrow (Cat.sliceFstSnd A B a).toFunctor b)) :=
    IsTerminal.hasTerminal (X := top) (IsTerminal.ofUniqueHom
      (fun Z => CostructuredArrow.homMk
        (CostructuredArrow.homMk ⟨Z.left.hom, Z.hom⟩ (Category.comp_id _))
        (Category.comp_id _))
      (fun Z m => by
        refine CostructuredArrow.hom_ext _ _ (CostructuredArrow.hom_ext _ _ ?_)
        refine CategoryTheory.Prod.hom_ext (C := ↥A) (D := ↥B) ?_ ?_
        · exact (Category.comp_id _).symm.trans (CostructuredArrow.w m.left)
        · exact (Category.comp_id _).symm.trans (CostructuredArrow.w m)))
  exact 𝒲.terminal_aspherical _

theorem asphericalFunctor_fst (A : Cat.{u, u}) {B : Cat.{u, u}} (hB : 𝒲.Aspherical B) :
    𝒲.AsphericalFunctor ((CategoryTheory.Prod.fst ↥A ↥B).toCatHom : Cat.of (↥A × ↥B) ⟶ A) :=
  fun a => (𝒲.aspherical_iff_W (Cat.sliceFstSnd A B a) hB).2
    (𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_sliceFstSnd A B a))

theorem W_fst (A : Cat.{u, u}) {B : Cat.{u, u}} (hB : 𝒲.Aspherical B) :
    𝒲.W ((CategoryTheory.Prod.fst ↥A ↥B).toCatHom : Cat.of (↥A × ↥B) ⟶ A) :=
  𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_fst A hB)

theorem aspherical_prod {A B : Cat.{u, u}} (hA : 𝒲.Aspherical A) (hB : 𝒲.Aspherical B) :
    𝒲.Aspherical (Cat.of (↥A × ↥B)) :=
  (𝒲.aspherical_iff_W _ hA).2 (𝒲.W_fst A hB)

theorem W_intervalInclusion (A : Cat.{u, u}) (ε : Bool) : 𝒲.W (intervalInclusion A ε) := by
  refine 𝒲.W.of_postcomp _ _ (𝒲.W_fst A (𝒲.terminal_aspherical interval.{u})) ?_
  rw [intervalInclusion_comp_fst]
  exact 𝒲.W.id_mem A

theorem W_iff_of_natTrans {A B : Cat.{u, u}} {u v : A ⟶ B} (α : u.toFunctor ⟶ v.toFunctor) :
    𝒲.W u ↔ 𝒲.W v := by
  change 𝒲.W (intervalInclusion A false ≫ natTransHomotopy α) ↔
    𝒲.W (intervalInclusion A true ≫ natTransHomotopy α)
  rw [𝒲.W.precomp_iff _ _ (𝒲.W_intervalInclusion A false),
    𝒲.W.precomp_iff _ _ (𝒲.W_intervalInclusion A true)]

theorem W_iff_of_isEquivalence_of_iso {C₁ C₂ D₁ D₂ : Cat.{u, u}} (e₁ : C₁ ⟶ D₁) (e₂ : C₂ ⟶ D₂)
    (he₁ : e₁.toFunctor.IsEquivalence) (he₂ : e₂.toFunctor.IsEquivalence) (F : C₁ ⟶ C₂)
    (G : D₁ ⟶ D₂) (α : e₁.toFunctor ⋙ G.toFunctor ≅ F.toFunctor ⋙ e₂.toFunctor) :
    𝒲.W F ↔ 𝒲.W G := by
  have h₁ := 𝒲.W_of_isEquivalence e₁
  have h₂ := 𝒲.W_of_isEquivalence e₂
  have hα : 𝒲.W (e₁ ≫ G) ↔ 𝒲.W (F ≫ e₂) := 𝒲.W_iff_of_natTrans (u := e₁ ≫ G) α.hom
  constructor
  · intro hF
    exact 𝒲.W.of_precomp _ _ h₁ (hα.2 (𝒲.W.comp_mem _ _ hF h₂))
  · intro hG
    exact 𝒲.W.of_postcomp _ _ h₂ (hα.1 (𝒲.W.comp_mem _ _ h₁ hG))

theorem W_of_adjunction_right {A B : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ A}
    (adj : u.toFunctor ⊣ v.toFunctor) : 𝒲.W v := by
  have h : 𝒲.W (u ≫ v) :=
    (𝒲.W_iff_of_natTrans (u := 𝟙 A) (v := u ≫ v) adj.unit).1 (𝒲.W.id_mem A)
  exact 𝒲.W.of_precomp _ _ (𝒲.W_of_adjunction adj) h

theorem W_of_comp_eq_id_of_W {C D : Cat.{u, u}} {i : D ⟶ C} {r : C ⟶ D} (hri : i ≫ r = 𝟙 D)
    (h : 𝒲.W (r ≫ i)) : 𝒲.W i := by
  have hr : 𝒲.W r := 𝒲.W.of_retract
    { i := Arrow.homMk (𝟙 C) i (by simp)
      r := Arrow.homMk (𝟙 C) r (by simp [hri])
      retract := Arrow.hom_ext _ _ (by simp) (by simp [hri]) } h
  exact 𝒲.W.of_postcomp _ _ hr (hri ▸ 𝒲.W.id_mem D)

theorem aspherical_of_thin {C : Cat.{u, u}}
    (hC : ∀ X Y : C, Subsingleton (X ⟶ Y)) (ρ : C ⥤ C) (t : C)
    (α : ∀ X, ρ.obj X ⟶ X) (β : ∀ X, ρ.obj X ⟶ t) : 𝒲.Aspherical C := by
  let i : Cat.of (Discrete PUnit.{u + 1}) ⟶ C := (Functor.fromPUnit t).toCatHom
  let r : C ⟶ Cat.of (Discrete PUnit.{u + 1}) := (Functor.star C).toCatHom
  have hri : i ≫ r = 𝟙 _ := Cat.Hom.ext (Functor.punit_ext' _ _)
  have hρ : 𝒲.W ρ.toCatHom :=
    (𝒲.W_iff_of_natTrans (u := ρ.toCatHom) (v := 𝟙 C)
      { app := α, naturality := fun _ _ _ => (hC _ _).elim _ _ }).2 (𝒲.W.id_mem C)
  have hri' : 𝒲.W (r ≫ i) :=
    (𝒲.W_iff_of_natTrans (u := ρ.toCatHom) (v := r ≫ i)
      { app := β, naturality := fun _ _ _ => (hC _ _).elim _ _ }).1 hρ
  exact 𝒲.aspherical_of_retraction_of_W i r hri hri' (𝒲.terminal_aspherical _)

end BasicLocalizer

end Atoms.TestCategory
