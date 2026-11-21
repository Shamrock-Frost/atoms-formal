import Atoms.Diagrammatic.Context.RoundBicategoryFunctor
import Atoms.Diagrammatic.HomotopyCategory
import Atoms.ForMathlib.CategoryTheory.Bicategory.Truncation

open CategoryTheory Bicategory
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace RoundBicat

def ofVertex (x : X.Vertex) : RoundBicat X 0 :=
  ⟨cellRound x, dimension_atomPoint⟩

def Arrow.ofEdge {x y : X.Vertex} (f : X.Edge x y) : Arrow (ofVertex x) (ofVertex y) :=
  ⟨cellRound f.cell, hasBdry_ofCell_edge f⟩

end RoundBicat

namespace HomotopyCategory

open RoundBicat

noncomputable def toTruncation (hX : HasWeakComposites X) :
    HomotopyCategory X hX ⥤ Bicategory.Truncation (RoundBicat X 0) where
  obj a := .mk (ofVertex a.pt)
  map {a b} := Quotient.lift (s := edgeSetoid X a.pt b.pt)
    (fun f => Truncation.homMk (Arrow.ofEdge f).hom) fun f g h =>
      (Truncation.homMk_eq_homMk_iff _ _).2 ((nonempty_hom_iso_hom_iff _ _).2 h)
  map_id a := by
    refine (congrArg Truncation.homMk ?_).trans (Truncation.homMk_id _)
    exact (Arrow.hom_eq_hom_iff _ (Arrow.id _)).2 (equiv_ofCell_edge_id_unit a.pt)
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    obtain ⟨h, hh⟩ := exists_edge_equivalent_pasteEdges hX f g
    have e : homMk hX f ≫ homMk hX g = homMk hX h := (homMk_comp_homMk_iff hX f g h).2 hh
    refine (congrArg _ e).trans ?_
    exact (Truncation.homMk_eq_homMk_iff _ _).2 ((nonempty_hom_iso_hom_iff (Arrow.ofEdge h)
      ((Arrow.ofEdge f).comp (Arrow.ofEdge g))).2 (equivalent_symm hh))

@[simp]
theorem toTruncation_obj (hX : HasWeakComposites X) (a : HomotopyCategory X hX) :
    (toTruncation hX).obj a = Bicategory.Truncation.mk (RoundBicat.ofVertex a.pt) :=
  rfl

@[simp]
theorem toTruncation_map_homMk (hX : HasWeakComposites X) {x y : X.Vertex} (f : X.Edge x y) :
    (toTruncation hX).map (homMk hX f) = Truncation.homMk (Arrow.ofEdge f).hom :=
  rfl

instance faithful_toTruncation (hX : HasWeakComposites X) : (toTruncation hX).Faithful where
  map_injective := by
    rintro a b ⟨f⟩ ⟨g⟩ h
    exact (homMk_eq_homMk_iff hX f g).2 ((nonempty_hom_iso_hom_iff _ _).1
      ((Truncation.homMk_eq_homMk_iff _ _).1 h))

instance full_toTruncation (hX : HasWeakComposites X) : (toTruncation hX).Full where
  map_surjective := by
    intro a b φ
    obtain ⟨f, rfl⟩ := Truncation.homMk_surjective φ
    obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
    obtain ⟨h, hh⟩ := exists_edge_equivalent_of_hasBdry hX p.diag p.hasBdry
    exact ⟨homMk hX h, (Truncation.homMk_eq_homMk_iff _ _).2
      ((nonempty_hom_iso_hom_iff (Arrow.ofEdge h) p).2 (equivalent_symm hh))⟩

instance essSurj_toTruncation (hX : HasWeakComposites X) : (toTruncation hX).EssSurj where
  mem_essImage c := by
    obtain ⟨x, hx⟩ := PastingDiagram.exists_equiv_ofCell_of_dim_eq_zero c.as.dim_diag
    obtain ⟨e⟩ := nonempty_equivalence_of_equiv (a := ofVertex x) (b := c.as) hx.symm
    exact ⟨⟨x⟩, ⟨Truncation.isoMk e⟩⟩

instance isEquivalence_toTruncation (hX : HasWeakComposites X) :
    (toTruncation hX).IsEquivalence where

theorem toTruncation_comp_map {Y : DiagSet.{u}} (hX : HasWeakComposites X)
    (hY : HasWeakComposites Y) (φ : X ⟶ Y) :
    toTruncation hX ⋙ Truncation.map (RoundBicat.map φ).toPseudofunctor =
      homotopyFunctor hX hY φ ⋙ toTruncation hY := by
  have hobj (x : X.Vertex) : (RoundBicat.map φ).obj (ofVertex x) = ofVertex (x.map φ) :=
    ext_diag (PastingDiagram.ofCell_app φ x).symm
  have hmk {a a' b b' : RoundBicat Y 0} (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
      (h : f ≍ g) : Truncation.homMk f ≍ Truncation.homMk g := by
    subst ha hb
    rw [eq_of_heq h]
  refine CategoryTheory.Functor.hext (fun a ↦ congrArg Truncation.mk (hobj a.pt)) ?_
  rintro a b ⟨f⟩
  refine hmk (hobj a.pt) (hobj b.pt) (Arrow.hom_heq (hobj a.pt) (hobj b.pt)
    ((Arrow.ofEdge f).mapTo φ) (Arrow.ofEdge (f.map φ)) ?_)
  change ((PastingDiagram.ofCell f.cell).mapTo φ).Equiv (PastingDiagram.ofCell (φ.app _ f.cell))
  rw [← PastingDiagram.ofCell_app]

end HomotopyCategory

noncomputable def homotopyCategoryTruncationEquivalence (hX : IsInftyCategory 1 X) :
    SSet.hoFunctor.obj (DiagSet.toSSet.obj X) ≌ Bicategory.Truncation (RoundBicat X 0) :=
  (homotopyCategoryEquivalence hX).symm.trans (HomotopyCategory.toTruncation hX.1).asEquivalence

end Atoms.Diagrammatic
