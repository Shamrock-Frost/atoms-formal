import Atoms.ForMathlib.CategoryTheory.Sites.Coverage
import Atoms.ForMathlib.CategoryTheory.Sites.Separated

open CategoryTheory Opposite

namespace Atoms.Homotopical

universe w v u

structure MarkingData (A : Type u) [Category.{v} A] where
  markable : ObjectProperty A
  degeneracy : MorphismProperty A
  [respectsIso : degeneracy.RespectsIso]
  markable_of_degeneracy : ∀ ⦃a b : A⦄ (p : a ⟶ b), degeneracy p → markable a
  markable_of_iso : ∀ ⦃a b : A⦄ (_ : a ≅ b), markable b → markable a

variable {A : Type v} [SmallCategory A] (D : MarkingData A)

namespace MarkingData

def Degenerate {a b : A} (g : a ⟶ b) : Prop :=
  ∃ (c : A) (p : a ⟶ c) (q : c ⟶ b), D.degeneracy p ∧ p ≫ q = g

variable {D}

theorem Degenerate.of_degeneracy {a b : A} {p : a ⟶ b} (hp : D.degeneracy p) :
    D.Degenerate p :=
  ⟨b, p, 𝟙 b, hp, Category.comp_id p⟩

theorem Degenerate.comp {a b c : A} {g : a ⟶ b} (hg : D.Degenerate g) (h : b ⟶ c) :
    D.Degenerate (g ≫ h) := by
  obtain ⟨d, p, q, hp, rfl⟩ := hg
  exact ⟨d, p, q ≫ h, hp, (Category.assoc _ _ _).symm⟩

theorem Degenerate.iso_comp {a b c : A} (e : a ⟶ b) [IsIso e] {g : b ⟶ c}
    (hg : D.Degenerate g) : D.Degenerate (e ≫ g) := by
  have := D.respectsIso
  obtain ⟨d, p, q, hp, rfl⟩ := hg
  exact ⟨d, e ≫ p, q, (D.degeneracy.cancel_left_of_respectsIso e p).2 hp,
    Category.assoc _ _ _⟩

end MarkingData

structure MarkedSite where
  obj : A
  isMarked : Bool
  markable : isMarked = true → D.markable obj

namespace MarkedSite

variable {D}

def Hom (x y : MarkedSite D) : Type v :=
  {g : x.obj ⟶ y.obj // x.isMarked = true → (y.isMarked = true ∧ IsIso g) ∨ D.Degenerate g}

instance category : SmallCategory (MarkedSite D) where
  Hom := Hom
  id x := ⟨𝟙 _, fun h => Or.inl ⟨h, inferInstance⟩⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, fun hx => by
    rcases f.2 hx with ⟨hy, hf⟩ | hf
    · rcases g.2 hy with ⟨hz, hg⟩ | hg
      · exact Or.inl ⟨hz, inferInstance⟩
      · exact Or.inr (hg.iso_comp f.1)
    · exact Or.inr (hf.comp g.1)⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[ext]
theorem hom_ext {x y : MarkedSite D} {f g : x ⟶ y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp]
theorem id_val (x : MarkedSite D) : (𝟙 x : x ⟶ x).1 = 𝟙 x.obj := rfl

@[simp]
theorem comp_val {x y z : MarkedSite D} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

variable (D)

def unmarked : A ⥤ MarkedSite D where
  obj a := ⟨a, false, fun h => absurd h Bool.false_ne_true⟩
  map g := ⟨g, fun h => absurd h Bool.false_ne_true⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def base : MarkedSite D ⥤ A where
  obj x := x.obj
  map g := g.1
  map_id _ := rfl
  map_comp _ _ := rfl

variable {D}

def marked (a : A) (h : D.markable a) : MarkedSite D := ⟨a, true, fun _ => h⟩

def toSelf (x : MarkedSite D) : (unmarked D).obj x.obj ⟶ x :=
  ⟨𝟙 _, fun h => absurd h Bool.false_ne_true⟩

theorem toSelf_comp {x y : MarkedSite D} (g : x ⟶ y) :
    toSelf x ≫ g = (unmarked D).map g.1 ≫ toSelf y :=
  hom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)

variable (D)

def coverage : Coverage (MarkedSite D) where
  coverings x := {Presieve.singleton (toSelf x)}
  pullback x y f S hS := by
    rw [Set.mem_singleton_iff] at hS
    subst hS
    refine ⟨Presieve.singleton (toSelf y), rfl, ?_⟩
    rintro z g ⟨⟩
    exact ⟨_, (unmarked D).map (toSelf y ≫ f).1, toSelf x, Presieve.singleton_self _,
      hom_ext (Category.comp_id _)⟩

def topology : GrothendieckTopology (MarkedSite D) :=
  (coverage D).toGrothendieck

variable {D}

theorem isSeparated_iff {P : (MarkedSite D)ᵒᵖ ⥤ Type (max w v)} :
    Presieve.IsSeparated (topology D) P ↔ ∀ x : MarkedSite D, Function.Injective
      (P.map (toSelf x).op) := by
  refine (Presieve.isSeparated_coverage _ P).trans ⟨fun h x => ?_, fun h x R hR => ?_⟩
  · exact Presieve.isSeparatedFor_singleton.1 (h _ rfl)
  · obtain rfl : R = Presieve.singleton (toSelf x) := hR
    exact Presieve.isSeparatedFor_singleton.2 (h x)

end MarkedSite

end Atoms.Homotopical
