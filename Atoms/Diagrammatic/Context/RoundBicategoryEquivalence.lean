import Atoms.Diagrammatic.Context.RoundBicategoryCoherence
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Bicategory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace RoundBicat

variable {n : ℕ} {a b : RoundBicat X n}

noncomputable def equivalenceOfCells (p : Arrow a b) (q : Arrow b a)
    (z₀ : Cell (p.hom ≫ q.hom) (𝟙 a)) (h₀ : Cell (𝟙 b) (q.hom ≫ p.hom))
    (hz₀ : z₀.diag ∈ equivalences X) (hh₀ : h₀.diag ∈ equivalences X) :
    Bicategory.Equivalence a b :=
  haveI := (isIso_homMk_iff z₀).2 hz₀
  haveI := (isIso_homMk_iff h₀).2 hh₀
  Equivalence.mkOfAdjointifyCounit (asIso (homMk z₀)).symm (asIso (homMk h₀)).symm

section equivalenceOfCells

variable (p : Arrow a b) (q : Arrow b a) (z₀ : Cell (p.hom ≫ q.hom) (𝟙 a))
  (h₀ : Cell (𝟙 b) (q.hom ≫ p.hom)) (hz₀ : z₀.diag ∈ equivalences X)
  (hh₀ : h₀.diag ∈ equivalences X)

@[simp]
theorem equivalenceOfCells_hom : (equivalenceOfCells p q z₀ h₀ hz₀ hh₀).hom = p.hom :=
  rfl

@[simp]
theorem equivalenceOfCells_inv : (equivalenceOfCells p q z₀ h₀ hz₀ hh₀).inv = q.hom :=
  rfl

@[simp]
theorem equivalenceOfCells_unit_inv : (equivalenceOfCells p q z₀ h₀ hz₀ hh₀).unit.inv = homMk z₀ :=
  rfl

end equivalenceOfCells

private theorem equivalent_of_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
    {x y : RoundPastingDiagram X} (hx : f.Mem x.toPastingDiagram) (hy : g.Mem y.toPastingDiagram) :
    Equivalent x y := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  exact equivalent_of_mem_equivalences_cond false ((isIso_homMk_iff t).1 inferInstance)
    hx.dim_eq hy.dim_eq t.dim_diag (t.source.equiv hx) (t.target.equiv hy)

theorem nonempty_hom_iso_hom_iff (p q : Arrow a b) :
    Nonempty (p.hom ≅ q.hom) ↔ Equivalent p.diag q.diag := by
  refine ⟨fun ⟨e⟩ => equivalent_of_isIso e.hom ((Arrow.mem_hom p _).2 (.refl _))
    ((Arrow.mem_hom q _).2 (.refl _)), fun h => ?_⟩
  obtain ⟨-, e, he, hd, hs, ht⟩ := h.data
  rw [p.hasBdry.dim_h] at hd hs ht
  let t : Cell p.hom q.hom :=
    ⟨e, hd, (Arrow.mem_hom p _).2 hs.symm, (Arrow.mem_hom q _).2 ht.symm⟩
  have := (isIso_homMk_iff t).2 he
  exact ⟨asIso (homMk t)⟩

theorem exists_cells_of_isWeakInverse (p : Arrow a b) (q : Arrow b a)
    (hw : IsWeakInverse p.diag.toPastingDiagram q.diag.toPastingDiagram) :
    ∃ (z : Cell (p.hom ≫ q.hom) (𝟙 a)) (h : Cell (𝟙 b) (q.hom ≫ p.hom)),
      z.diag ∈ equivalences X ∧ h.diag ∈ equivalences X := by
  obtain ⟨-, -, ⟨z, hz, hzm, tz⟩, ⟨z', hz', hzm', tz'⟩⟩ := hw.spec p.hasBdry
  rw [pasteOr_of (p.hasBdry.pastable q.hasBdry (.refl _))] at tz
  rw [pasteOr_of (q.hasBdry.pastable p.hasBdry (.refl _))] at tz'
  exact ⟨⟨⟨z, hz⟩, tz.dim_h, (Arrow.mem_hom (p.comp q) _).2 tz.side.symm,
      (Hom.mem_id a).of_equiv tz.other.symm⟩,
    ⟨⟨z', hz'⟩, tz'.dim_h, (Hom.mem_id b).of_equiv tz'.side.symm,
      (Arrow.mem_hom (q.comp p) _).2 tz'.other.symm⟩, hzm, hzm'⟩

theorem mem_equivalences_iff_exists_equivalence (p : Arrow a b) :
    p.diag ∈ equivalences X ↔ ∃ e : Bicategory.Equivalence a b, e.hom = p.hom := by
  constructor
  · intro he
    obtain ⟨e', hw⟩ := exists_isWeakInverse he
    obtain ⟨-, te'⟩ := hw.hasBdry p.hasBdry
    obtain ⟨z₀, h₀, hz₀, hh₀⟩ := exists_cells_of_isWeakInverse p ⟨e', te'⟩ hw
    exact ⟨equivalenceOfCells p _ z₀ h₀ hz₀ hh₀, rfl⟩
  · rintro ⟨E, hE⟩
    have hp : E.hom.Mem p.diag.toPastingDiagram := hE ▸ (Arrow.mem_hom p _).2 (.refl _)
    have hpq := p.hasBdry.pastable E.inv.rep.hasBdry (.refl _)
    have hqp := E.inv.rep.hasBdry.pastable p.hasBdry (.refl _)
    exact mem_equivalences_of_equivalent_unit p.hasBdry E.inv.rep.hasBdry a.diag.isRound
      b.diag.isRound (equivalent_of_isIso E.unit.inv (hp.comp E.inv.mem_rep hpq) (Hom.mem_id a))
      (equivalent_of_isIso E.counit.inv (Hom.mem_id b) (E.inv.mem_rep.comp hp hqp))

def Arrow.ofEquiv (h : a.diag.toPastingDiagram.Equiv b.diag.toPastingDiagram) :
    Arrow a b :=
  ⟨a.diag.isRound.unit, ⟨(hasType_unit a.dim_diag).dim_h, a.dim_diag, b.dim_diag,
    (hasType_unit a.dim_diag).side, (hasType_unit a.dim_diag).other.trans h⟩⟩

theorem nonempty_equivalence_of_equiv
    (h : a.diag.toPastingDiagram.Equiv b.diag.toPastingDiagram) :
    Nonempty (Bicategory.Equivalence a b) :=
  let ⟨e, _⟩ := (mem_equivalences_iff_exists_equivalence (Arrow.ofEquiv h)).1
    (unit_mem_equivalences a.diag)
  ⟨e⟩

theorem exists_adjoint_invertors (p : Arrow a b) (q : Arrow b a)
    (z₀ : Cell (p.hom ≫ q.hom) (𝟙 a)) (h₀ : Cell (𝟙 b) (q.hom ≫ p.hom))
    (hz₀ : z₀.diag ∈ equivalences X) (hh₀ : h₀.diag ∈ equivalences X) :
    ∃ (z : Cell (p.hom ≫ q.hom) (𝟙 a)) (h : Cell (𝟙 b) (q.hom ≫ p.hom)),
      z.diag ∈ equivalences X ∧ h.diag ∈ equivalences X ∧
      (ρ_ p.hom).inv ≫ p.hom ◁ homMk h ≫ (α_ p.hom q.hom p.hom).inv ≫ homMk z ▷ p.hom ≫
          (λ_ p.hom).hom = 𝟙 p.hom ∧
      (λ_ q.hom).inv ≫ homMk h ▷ q.hom ≫ (α_ q.hom p.hom q.hom).hom ≫ q.hom ◁ homMk z ≫
          (ρ_ q.hom).hom = 𝟙 q.hom := by
  let E := equivalenceOfCells p q z₀ h₀ hz₀ hh₀
  have e₁ : (ρ_ E.hom).inv ≫ E.hom ◁ E.counit.inv ≫ (α_ E.hom E.inv E.hom).inv ≫
      E.unit.inv ▷ E.hom ≫ (λ_ E.hom).hom = 𝟙 E.hom := by
    have e := congrArg Iso.inv E.left_triangle
    rw [leftZigzagIso_inv, Iso.trans_inv, Iso.symm_inv] at e
    calc _ = (ρ_ E.hom).inv ≫ rightZigzag E.counit.inv E.unit.inv ≫ (λ_ E.hom).hom := by
          bicategory
      _ = 𝟙 E.hom := by rw [e]; simp
  have e₂ : (λ_ E.inv).inv ≫ E.counit.inv ▷ E.inv ≫ (α_ E.inv E.hom E.inv).hom ≫
      E.inv ◁ E.unit.inv ≫ (ρ_ E.inv).hom = 𝟙 E.inv := by
    have e := congrArg Iso.inv E.right_triangle
    rw [rightZigzagIso_inv, Iso.trans_inv, Iso.symm_inv] at e
    calc _ = (λ_ E.inv).inv ≫ leftZigzag E.counit.inv E.unit.inv ≫ (ρ_ E.inv).hom := by
          bicategory
      _ = 𝟙 E.inv := by rw [e]; simp
  obtain ⟨h, hh⟩ := homMk_surjective (f := 𝟙 b) (g := q.hom ≫ p.hom) E.counit.inv
  refine ⟨z₀, h, hz₀, (isIso_homMk_iff h).1 (hh ▸ E.counit.isIso_inv), ?_, ?_⟩
  · rw [hh]
    exact e₁
  · rw [hh]
    exact e₂

theorem exists_adjoint_invertors_of_isWeakInverse (p : Arrow a b) (q : Arrow b a)
    (hw : IsWeakInverse p.diag.toPastingDiagram q.diag.toPastingDiagram) :
    ∃ (z : Cell (p.hom ≫ q.hom) (𝟙 a)) (h : Cell (𝟙 b) (q.hom ≫ p.hom)),
      z.diag ∈ equivalences X ∧ h.diag ∈ equivalences X ∧
      (ρ_ p.hom).inv ≫ p.hom ◁ homMk h ≫ (α_ p.hom q.hom p.hom).inv ≫ homMk z ▷ p.hom ≫
          (λ_ p.hom).hom = 𝟙 p.hom ∧
      (λ_ q.hom).inv ≫ homMk h ▷ q.hom ≫ (α_ q.hom p.hom q.hom).hom ≫ q.hom ◁ homMk z ≫
          (ρ_ q.hom).hom = 𝟙 q.hom := by
  obtain ⟨z₀, h₀, hz₀, hh₀⟩ := exists_cells_of_isWeakInverse p q hw
  exact exists_adjoint_invertors p q z₀ h₀ hz₀ hh₀

end RoundBicat

end Atoms.Diagrammatic
