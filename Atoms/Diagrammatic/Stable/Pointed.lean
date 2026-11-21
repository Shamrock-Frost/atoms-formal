import Atoms.Diagrammatic.FinalObjectComparison
import Atoms.Diagrammatic.HomotopyCategoryInvariance

open CategoryTheory Limits Opposite Simplicial MorphismProperty HomotopicalAlgebra
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped ReversiblePathSpace

variable {X Y : DiagSet.{u}}

def DiagSet.IsPointed (X : DiagSet.{u}) : Prop :=
  ∃ z : X.Vertex, X.IsZeroObject z

theorem DiagSet.isZeroObject_iff_of_isEquivalence (hX : IsInftyCategory 1 X)
    {t t' : X.Vertex} (e : X.Edge t t') (he : IsEquivalence X e.cell) :
    X.IsZeroObject t ↔ X.IsZeroObject t' :=
  forall_congr' fun α => X.hasContractibleHoms_iff_of_isEquivalence hX α e he

theorem DiagSet.isZeroObject_map_iff (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] (t : X.Vertex) :
    Y.IsZeroObject (t.map F) ↔ X.IsZeroObject t :=
  forall_congr' fun α => DiagSet.hasContractibleHoms_map_iff hX hY F α t

theorem DiagSet.isPointed_iff_of_weakEquivalence (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    Y.IsPointed ↔ X.IsPointed := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨z, hz⟩ => ⟨_, (DiagSet.isZeroObject_map_iff hX hY F z).2 hz⟩⟩
  obtain ⟨x, hx⟩ := DiagSet.exists_hasContractibleHoms_iff_map hX hY F z
  exact ⟨x, (DiagSet.isZeroObject_map_iff hX hY F x).1 fun α => (hx α).1 (hz α)⟩

theorem DiagSet.isPointed_iff_toSSet_isPointed (hX : IsInftyCategory 1 X) :
    X.IsPointed ↔ (DiagSet.toSSet.obj X).IsPointed :=
  X.vertexEquivSSet.exists_congr fun t => X.isZeroObject_iff_isZeroObject hX t

theorem DiagSet.isEquivalence_of_isFinalObject_of_isInitialObject (hX : IsInftyCategory 1 X)
    {t i : X.Vertex} (ht : X.IsFinalObject t) (hi : X.IsInitialObject i)
    (f : X.Edge t i) : IsEquivalence X f.cell := by
  have hT := X.isTerminalOfIsFinalObject hX ht
  have hI := X.isInitialOfIsInitialObject hX hi
  rw [← HomotopyCategory.isIso_homMk_iff hX.1]
  exact ⟨hI.to _, hT.hom_ext _ _, hI.hom_ext _ _⟩

theorem DiagSet.isPointed_iff (hX : IsInftyCategory 1 X) :
    X.IsPointed ↔ ∃ i t : X.Vertex,
      X.IsInitialObject i ∧ X.IsFinalObject t ∧ Nonempty (X.Edge t i) := by
  refine ⟨fun ⟨z, hz⟩ => ⟨z, z, hz false, hz true, ⟨DiagSet.Edge.id z⟩⟩,
    fun ⟨i, t, hi, ht, ⟨f⟩⟩ => ⟨i, ?_⟩⟩
  have hfin := (X.hasContractibleHoms_iff_of_isEquivalence hX true f
    (X.isEquivalence_of_isFinalObject_of_isInitialObject hX ht hi f)).1 ht
  intro α
  cases α
  exacts [hi, hfin]

theorem DiagSet.hasZeroObject_homotopyCategory (hX : IsInftyCategory 1 X) (h : X.IsPointed) :
    HasZeroObject (HomotopyCategory X hX.1) :=
  let ⟨_, hz⟩ := h
  ⟨⟨_, X.isZero_of_isZeroObject hX hz⟩⟩

theorem DiagSet.comp_eq_comp_of_isZeroObject (hX : IsInftyCategory 1 X)
    {x y z z' : HomotopyCategory X hX.1} (hz : X.IsZeroObject z.pt) (hz' : X.IsZeroObject z'.pt)
    (a : x ⟶ z) (b : z ⟶ y) (a' : x ⟶ z') (b' : z' ⟶ y) : a ≫ b = a' ≫ b' := by
  have hZ : IsZero z := X.isZero_of_isZeroObject hX hz
  have hZ' : IsZero z' := X.isZero_of_isZeroObject hX hz'
  calc a ≫ b = (a ≫ (hZ.iso hZ').hom) ≫ ((hZ.iso hZ').inv ≫ b) := by simp
    _ = a' ≫ b' := by rw [hZ'.eq_of_tgt (a ≫ _) a', hZ'.eq_of_src (_ ≫ b) b']

def DiagSet.IsZeroEdge (hX : HasWeakComposites X) {x y : X.Vertex} (f : X.Edge x y) : Prop :=
  ∃ z : HomotopyCategory X hX, X.IsZeroObject z.pt ∧
    ∃ (a : (⟨x⟩ : HomotopyCategory X hX) ⟶ z) (b : z ⟶ ⟨y⟩), HomotopyCategory.homMk hX f = a ≫ b

theorem DiagSet.exists_isZeroEdge (hX : IsInftyCategory 1 X) (h : X.IsPointed)
    (x y : X.Vertex) : ∃ f : X.Edge x y, X.IsZeroEdge hX.1 f := by
  obtain ⟨z, hz⟩ := h
  have hZ := X.isZero_of_isZeroObject hX hz
  obtain ⟨f, hf⟩ := HomotopyCategory.homMk_surjective hX.1 (hZ.from_ ⟨x⟩ ≫ hZ.to_ ⟨y⟩)
  exact ⟨f, ⟨z⟩, hz, _, _, hf⟩

theorem DiagSet.homMk_eq_of_isZeroEdge (hX : IsInftyCategory 1 X)
    {x y : X.Vertex} {f g : X.Edge x y} (hf : X.IsZeroEdge hX.1 f)
    (hg : X.IsZeroEdge hX.1 g) :
    HomotopyCategory.homMk hX.1 f = HomotopyCategory.homMk hX.1 g := by
  obtain ⟨z, hz, a, b, hab⟩ := hf
  obtain ⟨z', hz', a', b', hab'⟩ := hg
  rw [hab, hab']
  exact X.comp_eq_comp_of_isZeroObject hX hz hz' a b a' b'

theorem DiagSet.IsZeroEdge.of_homMk_eq_comp (hX : HasWeakComposites X)
    {x y v w : X.Vertex} {f : X.Edge x y} (hf : X.IsZeroEdge hX f) {g : X.Edge v w}
    (c : (⟨v⟩ : HomotopyCategory X hX) ⟶ ⟨x⟩)
    (d : (⟨y⟩ : HomotopyCategory X hX) ⟶ ⟨w⟩)
    (hg : HomotopyCategory.homMk hX g = c ≫ HomotopyCategory.homMk hX f ≫ d) :
    X.IsZeroEdge hX g := by
  obtain ⟨z, hz, a, b, hab⟩ := hf
  exact ⟨z, hz, c ≫ a, b ≫ d, by rw [hg, hab, Category.assoc, Category.assoc]⟩

theorem DiagSet.IsZeroEdge.map (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] {x y : X.Vertex}
    {f : X.Edge x y} (hf : X.IsZeroEdge hX.1 f) : Y.IsZeroEdge hY.1 (f.map F) := by
  obtain ⟨z, hz, a, b, hab⟩ := hf
  refine ⟨(homotopyFunctor hX.1 hY.1 F).obj z, (DiagSet.isZeroObject_map_iff hX hY F z.pt).2 hz,
    (homotopyFunctor hX.1 hY.1 F).map a, (homotopyFunctor hX.1 hY.1 F).map b, ?_⟩
  rw [← homotopyFunctor_map_homMk hX.1 hY.1, hab]
  exact Functor.map_comp _ _ _

theorem DiagSet.isZeroEdge_map_iff (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    {x y : X.Vertex} (f : X.Edge x y) : Y.IsZeroEdge hY.1 (f.map F) ↔ X.IsZeroEdge hX.1 f := by
  refine ⟨fun hf => ?_, DiagSet.IsZeroEdge.map hX hY F⟩
  have h : X.IsPointed := by
    obtain ⟨z, hz, -⟩ := hf
    exact (DiagSet.isPointed_iff_of_weakEquivalence hX hY F).1 ⟨z.pt, hz⟩
  obtain ⟨g, hg⟩ := X.exists_isZeroEdge hX h x y
  have := DiagSet.faithful_homotopyFunctor hX hY F
  have hfg : HomotopyCategory.homMk hX.1 f = HomotopyCategory.homMk hX.1 g :=
    (homotopyFunctor hX.1 hY.1 F).map_injective (by
      rw [homotopyFunctor_map_homMk, homotopyFunctor_map_homMk]
      exact Y.homMk_eq_of_isZeroEdge hY hf (hg.map hX hY F))
  exact hg.of_homMk_eq_comp hX.1 (𝟙 _) (𝟙 _) (by rw [hfg, Category.id_comp, Category.comp_id])

end Atoms.Diagrammatic
