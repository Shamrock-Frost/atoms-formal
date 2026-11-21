import Atoms.ForMathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.Retract

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

def elementsFunctor (A : Type u) [SmallCategory A] : (Aᵒᵖ ⥤ Type u) ⥤ Cat.{u, u} :=
  Functor.elementsFunctor ⋙ Cat.opFunctor

structure BasicLocalizer where
  W : MorphismProperty Cat.{u, u}
  containsIdentities : W.ContainsIdentities
  hasTwoOutOfThree : W.HasTwoOutOfThreeProperty
  isStableUnderRetracts : W.IsStableUnderRetracts
  terminal_aspherical : ∀ (C : Cat.{u, u}) [HasTerminal C], W (terminal.from C)
  quillenA : ∀ {A B C : Cat.{u, u}} (u : A ⟶ B) (v : B ⟶ C),
    (∀ c : C, W (CostructuredArrow.pre u.toFunctor v.toFunctor c).toCatHom) → W u

@[ext]
theorem BasicLocalizer.ext {𝒲 𝒲' : BasicLocalizer.{u}} (h : 𝒲.W = 𝒲'.W) : 𝒲 = 𝒲' := by
  cases 𝒲
  cases 𝒲'
  cases h
  rfl

namespace BasicLocalizer

attribute [instance] containsIdentities hasTwoOutOfThree isStableUnderRetracts

variable (𝒲 : BasicLocalizer.{u})

def Aspherical (C : Cat.{u, u}) : Prop := 𝒲.W (terminal.from C)

def AsphericalFunctor {A B : Cat.{u, u}} (u : A ⟶ B) : Prop :=
  ∀ b : B, 𝒲.Aspherical (Cat.of (CostructuredArrow u.toFunctor b))

def wPsh (A : Type u) [SmallCategory A] : MorphismProperty (Aᵒᵖ ⥤ Type u) :=
  𝒲.W.inverseImage (elementsFunctor A)

instance (A : Type u) [SmallCategory A] : (𝒲.wPsh A).ContainsIdentities :=
  inferInstanceAs (𝒲.W.inverseImage _).ContainsIdentities

instance (A : Type u) [SmallCategory A] : (𝒲.wPsh A).HasTwoOutOfThreeProperty :=
  inferInstanceAs (𝒲.W.inverseImage _).HasTwoOutOfThreeProperty

instance (A : Type u) [SmallCategory A] : (𝒲.wPsh A).IsStableUnderRetracts :=
  inferInstanceAs (𝒲.W.inverseImage _).IsStableUnderRetracts

def IsAccessible : Prop :=
  ∃ T : MorphismProperty Cat.{u, u}, MorphismProperty.IsSmall.{u} T ∧ T ≤ 𝒲.W ∧
    ∀ 𝒱 : BasicLocalizer.{u}, T ≤ 𝒱.W → 𝒲.W ≤ 𝒱.W

theorem W_of_aspherical_of_hasTerminal {X Y : Cat.{u, u}} [HasTerminal Y] (f : X ⟶ Y)
    (hX : 𝒲.Aspherical X) : 𝒲.W f :=
  𝒲.W.of_postcomp f (terminal.from Y) (𝒲.terminal_aspherical Y)
    (by rw [terminal.comp_from]; exact hX)

theorem W_pre_id_of_aspherical {A B : Cat.{u, u}} (u : A ⟶ B) (b : B)
    (h : 𝒲.Aspherical (Cat.of (CostructuredArrow u.toFunctor b))) :
    𝒲.W (CostructuredArrow.pre u.toFunctor (Cat.Hom.toFunctor (𝟙 B)) b).toCatHom :=
  𝒲.W_of_aspherical_of_hasTerminal _ h

theorem W_of_asphericalFunctor {A B : Cat.{u, u}} {u : A ⟶ B} (h : 𝒲.AsphericalFunctor u) :
    𝒲.W u :=
  𝒲.quillenA u (𝟙 B) fun b => 𝒲.W_pre_id_of_aspherical u b (h b)

theorem asphericalFunctor_of_adjunction {A B : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ A}
    (adj : u.toFunctor ⊣ v.toFunctor) : 𝒲.AsphericalFunctor u := fun b => by
  have : HasTerminal (Cat.of (CostructuredArrow u.toFunctor b)) :=
    (mkTerminalOfRightAdjoint _ adj b).hasTerminal
  exact 𝒲.terminal_aspherical _

theorem W_of_adjunction {A B : Cat.{u, u}} {u : A ⟶ B} {v : B ⟶ A}
    (adj : u.toFunctor ⊣ v.toFunctor) : 𝒲.W u :=
  𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_of_adjunction adj)

theorem asphericalFunctor_of_isEquivalence {A B : Cat.{u, u}} (u : A ⟶ B)
    [u.toFunctor.IsEquivalence] : 𝒲.AsphericalFunctor u :=
  𝒲.asphericalFunctor_of_adjunction (v := u.toFunctor.inv.toCatHom)
    u.toFunctor.asEquivalence.toAdjunction

theorem W_of_isEquivalence {A B : Cat.{u, u}} (u : A ⟶ B) [u.toFunctor.IsEquivalence] :
    𝒲.W u :=
  𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_of_isEquivalence u)

theorem aspherical_iff_of_W {X Y : Cat.{u, u}} (f : X ⟶ Y) (hf : 𝒲.W f) :
    𝒲.Aspherical X ↔ 𝒲.Aspherical Y := by
  unfold Aspherical
  rw [show terminal.from X = f ≫ terminal.from Y from terminal.hom_ext _ _]
  exact ⟨𝒲.W.of_precomp _ _ hf, 𝒲.W.comp_mem _ _ hf⟩

theorem aspherical_iff_W {X Y : Cat.{u, u}} (f : X ⟶ Y) (hY : 𝒲.Aspherical Y) :
    𝒲.Aspherical X ↔ 𝒲.W f := by
  have e : terminal.from X = f ≫ terminal.from Y := terminal.hom_ext _ _
  unfold Aspherical
  rw [e]
  exact 𝒲.W.postcomp_iff f _ hY

theorem asphericalFunctor_initialPoint (C : Cat.{u, u}) [HasInitial C] :
    𝒲.AsphericalFunctor (Cat.initialPoint C) := fun c => by
  have : HasTerminal (Cat.of (CostructuredArrow (Cat.initialPoint C).toFunctor c)) :=
    IsTerminal.hasTerminal
      (X := (CostructuredArrow.mk (Y := (⟨⟨⟩⟩ : Cat.of (Discrete PUnit.{u + 1})))
        (initial.to c) : CostructuredArrow (Cat.initialPoint C).toFunctor c))
      (IsTerminal.ofUniqueHom
        (fun _ => CostructuredArrow.homMk (𝟙 _) (initial.hom_ext _ _))
        (fun _ _ => CostructuredArrow.ext _ _ rfl))
  exact 𝒲.terminal_aspherical _

theorem aspherical_of_hasInitial (C : Cat.{u, u}) [HasInitial C] : 𝒲.Aspherical C :=
  (𝒲.aspherical_iff_of_W _
    (𝒲.W_of_asphericalFunctor (𝒲.asphericalFunctor_initialPoint C))).1
      (𝒲.terminal_aspherical _)

theorem aspherical_iff_of_equivalence {A B : Cat.{u, u}} (e : ↥A ≌ ↥B) :
    𝒲.Aspherical A ↔ 𝒲.Aspherical B :=
  have : (Cat.Hom.ofFunctor e.functor).toFunctor.IsEquivalence := e.isEquivalence_functor
  𝒲.aspherical_iff_of_W (Cat.Hom.ofFunctor e.functor) (𝒲.W_of_isEquivalence _)

theorem aspherical_of_equivalence {A B : Cat.{u, u}} (e : ↥A ≌ ↥B) (hA : 𝒲.Aspherical A) :
    𝒲.Aspherical B :=
  (𝒲.aspherical_iff_of_equivalence e).1 hA

theorem aspherical_of_retraction_of_W {C D : Cat.{u, u}} (i : D ⟶ C)
    (r : C ⟶ D) (hri : i ≫ r = 𝟙 D) (h : 𝒲.W (r ≫ i)) (hD : 𝒲.Aspherical D) :
    𝒲.Aspherical C := by
  have hr : 𝒲.W r := 𝒲.W.of_retract
    { i := Arrow.homMk (𝟙 C) i (by simp)
      r := Arrow.homMk (𝟙 C) r (by simp [hri])
      retract := Arrow.hom_ext _ _ (by simp) (by simp [hri]) } h
  have e : terminal.from C = r ≫ terminal.from D := terminal.hom_ext _ _
  unfold Aspherical
  rw [e]
  exact 𝒲.W.comp_mem _ _ hr hD

end BasicLocalizer

end Atoms.TestCategory
