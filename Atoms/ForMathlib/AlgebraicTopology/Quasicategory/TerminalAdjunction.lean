import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InvertibleTransformation
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject
import Atoms.ForMathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Atoms.ForMathlib.CategoryTheory.Bicategory.TerminalObject

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

section Section

variable {X : SSet.{u}} {ω : X _⦋0⦌} {s : X ⟶ sliceAt X ω}

private noncomputable def sectionEdge (hs : s ≫ sliceAtπ X ω = 𝟙 X) (x : X _⦋0⦌) : Edge x ω :=
  Edge.mk (sliceSimplex (yonedaEquiv.symm x ≫ s))
    ((δ_last_sliceSimplex _).trans (by
      rw [Category.assoc, hs, Category.comp_id, Equiv.apply_symm_apply]))
    (δ_zero_sliceSimplex _)

private lemma nonempty_compStruct_sectionEdge (hs : s ≫ sliceAtπ X ω = 𝟙 X)
    (hω : yonedaEquiv.symm ω ≫ s = yonedaEquiv.symm (sliceId X ω)) {x : X _⦋0⦌}
    (e : Edge x ω) : Nonempty (Edge.CompStruct e (Edge.id ω) (sectionEdge hs x)) := by
  let ℓ : Δ[1] ⟶ sliceAt X ω := yonedaEquiv.symm e.edge ≫ s
  refine ⟨Edge.CompStruct.mk (sliceSimplex ℓ) ?_ ?_ ?_⟩
  · exact (δ_last_sliceSimplex ℓ).trans (by
      rw [Category.assoc, hs, Category.comp_id, Equiv.apply_symm_apply])
  · refine (δ_castSucc_sliceSimplex ℓ 0).trans ?_
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq, hω]
    exact sliceSimplex_sliceId X ω
  · refine (δ_castSucc_sliceSimplex ℓ 1).trans ?_
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg (fun v ↦ sliceSimplex (yonedaEquiv.symm v ≫ s)) e.src_eq

private noncomputable def isTerminalOfSection [X.Quasicategory] (hs : s ≫ sliceAtπ X ω = 𝟙 X)
    (hω : yonedaEquiv.symm ω ≫ s = yonedaEquiv.symm (sliceId X ω)) :
    IsTerminal (Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) ω) := by
  have hne (a : Truncated.HomotopyCategory ((truncation 2).obj X)) :
      Nonempty (a ⟶ Truncated.HomotopyCategory.mk ω) := by
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    exact ⟨Truncated.HomotopyCategory.homMk (sectionEdge hs x).toTruncated⟩
  have hsub (x : X _⦋0⦌)
      (f : Truncated.HomotopyCategory.mk (V := (truncation 2).obj X) x ⟶
        Truncated.HomotopyCategory.mk ω) :
      f = Truncated.HomotopyCategory.homMk (sectionEdge hs x).toTruncated := by
    obtain ⟨e, rfl⟩ := Truncated.HomotopyCategory.homMk_surjective f
    obtain ⟨c⟩ := nonempty_compStruct_sectionEdge hs hω (Edge.ofTruncated e)
    exact (Truncated.HomotopyCategory.homMk_eq_homMk_iff _ _).2 ⟨c.toTruncated⟩
  refine IsTerminal.ofUniqueHom (fun a ↦ (hne a).some) (fun a m ↦ ?_)
  obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  exact (hsub x m).trans (hsub x _).symm

end Section

private lemma subsingleton_nonempty_hom_hoFunctor_obj {X : SSet.{u}} (hX : IsTerminal X)
    (x y : hoFunctor.obj X) : Subsingleton (x ⟶ y) ∧ Nonempty (x ⟶ y) := by
  let e := Cat.equivOfIso (hoFunctor.mapIso (hX.uniqueUpToIso stdSimplex.isTerminalObj₀))
  have hxy : e.functor.obj x = e.functor.obj y :=
    Subsingleton.elim (α := ((truncation.{u} 2).obj Δ[0]).HomotopyCategory) _ _
  exact ⟨⟨fun f g ↦ e.functor.map_injective
    ((IsDiscrete.subsingleton (C := ((truncation.{u} 2).obj Δ[0]).HomotopyCategory) _ _).elim
      _ _)⟩, ⟨e.functor.preimage (eqToHom hxy)⟩⟩

private noncomputable def isTerminalIhomTerminal (K : SSet.{u}) :
    IsTerminal ((ihom K).obj (⊤_ SSet.{u})) :=
  IsTerminal.ofUniqueHom (fun _ ↦ MonoidalClosed.curry (terminal.from _))
    (fun _ _ ↦ ihom_terminal_hom_ext _ _)

private lemma curry'_app_const (K : SSet.{u}) {X : SSet.{u}} (t : X _⦋0⦌) :
    (MonoidalClosed.curry' (stdSimplex.isTerminalObj₀.from K ≫ yonedaEquiv.symm t)).app _
      PUnit.unit = (MonoidalClosed.curry (snd K X)).app _ t := by
  have h : yonedaEquiv.symm ((MonoidalClosed.curry (snd K X)).app _ t) =
      MonoidalClosed.curry (snd K Δ[0] ≫ yonedaEquiv.symm t) := by
    rw [← yonedaEquiv_symm_comp, ← MonoidalClosed.curry_natural_left, whiskerLeft_snd]
  refine ((yonedaEquiv_comp (toUnit Δ[0]) _).symm.trans ?_).trans
    ((congrArg yonedaEquiv h).symm.trans (Equiv.apply_symm_apply _ _))
  rw [MonoidalClosed.curry', ← MonoidalClosed.curry_natural_left]
  refine congrArg _ (congrArg _ ?_)
  simp only [← Category.assoc]
  exact congrArg (· ≫ yonedaEquiv.symm t) (stdSimplex.isTerminalObj₀.hom_ext _ _)

open Bicategory

noncomputable def QCat.terminal : QCat.{u} :=
  ⟨⊤_ SSet.{u}, inferInstance⟩

noncomputable def QCat.toTerminal (A : QCat.{u}) : A ⟶ QCat.terminal :=
  ObjectProperty.homMk (terminal.from A.obj)

noncomputable def QCat.vertexHom {A : QCat.{u}} (t : A.obj _⦋0⦌) : QCat.terminal ⟶ A :=
  ObjectProperty.homMk (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm t)

def QCat.IsTerminalObject {A : QCat.{u}} (t : A.obj _⦋0⦌) : Prop :=
  Nonempty (Bicategory.Adjunction (QCat.toTerminal A) (QCat.vertexHom t))

theorem QCat.isTwoTerminal_terminal : IsTwoTerminal QCat.terminal.{u} where
  nonempty_hom A := ⟨QCat.toTerminal A⟩
  subsingleton_hom _ := ⟨fun _ _ ↦ ObjectProperty.hom_ext _ (terminal.hom_ext _ _)⟩
  nonempty_hom₂ {A} _ _ := ⟨CatEnrichedOrdinary.Hom.mk
    ((subsingleton_nonempty_hom_hoFunctor_obj (isTerminalIhomTerminal A.obj) _ _).2.some)⟩
  subsingleton_hom₂ {A} _ _ := ⟨fun _ _ ↦ CatEnrichedOrdinary.Hom.ext _ _
    ((subsingleton_nonempty_hom_hoFunctor_obj (isTerminalIhomTerminal A.obj) _ _).1.elim _ _)⟩

theorem QCat.vertexHom_comp {A B : QCat.{u}} (t : A.obj _⦋0⦌) (g : A ⟶ B) :
    QCat.vertexHom t ≫ g = QCat.vertexHom (g.hom.app _ t) :=
  ObjectProperty.hom_ext _ ((Category.assoc _ _ _).trans
    (congrArg (stdSimplex.isTerminalObj₀.from _ ≫ ·) (yonedaEquiv_symm_comp _ _)))

theorem QCat.isTerminalObject_iff_forall {A : QCat.{u}} (t : A.obj _⦋0⦌) :
    QCat.IsTerminalObject t ↔
      ∀ X : QCat.{u}, Nonempty (IsTerminal (QCat.toTerminal X ≫ QCat.vertexHom t)) := by
  refine (QCat.isTwoTerminal_terminal.nonempty_adjunction_iff _ _).trans
    ⟨fun h X ↦ h _, fun h X k ↦ ?_⟩
  obtain rfl : QCat.toTerminal X = k := (QCat.isTwoTerminal_terminal.subsingleton_hom X).elim _ _
  exact h X

theorem QCat.IsTerminalObject.map_of_adjunction {A B : QCat.{u}} {f : B ⟶ A} {g : A ⟶ B}
    (adj : Bicategory.Adjunction f g) {t : A.obj _⦋0⦌} (ht : QCat.IsTerminalObject t) :
    QCat.IsTerminalObject (A := B) (g.hom.app _ t) :=
  (congrArg (fun k : QCat.terminal ⟶ B ↦ Nonempty (Bicategory.Adjunction (QCat.toTerminal B) k))
    (QCat.vertexHom_comp t g)).mp
      (QCat.isTwoTerminal_terminal.nonempty_adjunction_comp adj (QCat.toTerminal A)
        (QCat.toTerminal B) ht)

theorem QCat.IsTerminalObject.map_of_equivalence {A B : QCat.{u}}
    (e : Bicategory.Equivalence A B) {t : A.obj _⦋0⦌} (ht : QCat.IsTerminalObject t) :
    QCat.IsTerminalObject (A := B) (e.hom.hom.app _ t) :=
  ht.map_of_adjunction
    (Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm).toAdjunction

private lemma homEquiv_toTerminal_comp_vertexHom (K : QCat.{u}) {A : QCat.{u}}
    (t : A.obj _⦋0⦌) :
    CatEnrichedOrdinary.homEquiv (QCat.toTerminal K ≫ QCat.vertexHom t) =
      Truncated.HomotopyCategory.mk (V := (truncation 2).obj ((ihom K.obj).obj A.obj))
        ((MonoidalClosed.curry (snd K.obj A.obj)).app _ t) := by
  have h : (QCat.toTerminal K ≫ QCat.vertexHom t).hom =
      stdSimplex.isTerminalObj₀.from K.obj ≫ yonedaEquiv.symm t :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ yonedaEquiv.symm t) (stdSimplex.isTerminalObj₀.hom_ext _ _))
  exact congrArg
    (Truncated.HomotopyCategory.mk (V := (truncation 2).obj ((ihom K.obj).obj A.obj)))
    ((congrArg (fun g : K.obj ⟶ A.obj ↦ (MonoidalClosed.curry' g).app _ PUnit.unit) h).trans
      (curry'_app_const _ _))

private noncomputable def isTerminalOfHomEquiv {K A : QCat.{u}} (t : A.obj _⦋0⦌)
    (h : IsTerminal (CatEnrichedOrdinary.homEquiv (QCat.toTerminal K ≫ QCat.vertexHom t))) :
    IsTerminal (QCat.toTerminal K ≫ QCat.vertexHom t) :=
  IsTerminal.ofUniqueHom (fun _ ↦ CatEnrichedOrdinary.Hom.mk (h.from _))
    fun _ _ ↦ CatEnrichedOrdinary.Hom.ext _ _ (h.hom_ext _ _)

theorem QCat.isTerminalObject_of_isFinal {A : QCat.{u}} {t : A.obj _⦋0⦌} (ht : IsFinal t) :
    QCat.IsTerminalObject t := by
  have := A.property
  refine (QCat.isTerminalObject_iff_forall t).2 fun K ↦ ?_
  obtain ⟨s, hs, hω⟩ := exists_section_of_isFinal (isFinal_const ht K.obj)
  exact ⟨isTerminalOfHomEquiv t ((isTerminalOfSection hs hω).ofIso
    (eqToIso (homEquiv_toTerminal_comp_vertexHom K t).symm))⟩

end SSet
