import Atoms.Diagrammatic.Localization.Inversion

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {V : Type u} {X Y : DiagSet.{u}}

def DiagSet.discrete (V : Type u) : DiagSet.{u} := (Functor.const Atomᵒᵖ).obj V

private def discreteDesc (p : V → diagram Y atomPoint) : DiagSet.discrete V ⟶ Y where
  app U := ↾fun v => Y.map (toAtomPoint U.unop).op (p v)
  naturality U W g := by
    ext v
    refine (congrArg (fun t => Y.map t.op (p v)) (Subsingleton.elim (toAtomPoint W.unop)
      (g.unop ≫ toAtomPoint U.unop))).trans ?_
    exact Y.map_comp_apply (toAtomPoint U.unop).op g (p v)

def DiagSet.discreteHomEquiv (V : Type u) (Y : DiagSet.{u}) :
    (DiagSet.discrete V ⟶ Y) ≃ (V → diagram Y atomPoint) where
  toFun f v := f.app (op atomPoint) v
  invFun := discreteDesc
  left_inv f := by
    ext U v
    exact (NatTrans.naturality_apply f (toAtomPoint U.unop).op v).symm
  right_inv p := by
    funext v
    refine (congrArg (fun t => Y.map t.op (p v))
      (Subsingleton.elim (toAtomPoint atomPoint) (𝟙 _))).trans ?_
    exact Y.map_id_apply (op atomPoint) (p v)

theorem DiagSet.discreteHomEquiv_apply (f : DiagSet.discrete V ⟶ Y) (v : V) :
    DiagSet.discreteHomEquiv V Y f v = f.app (op atomPoint) v :=
  rfl

theorem DiagSet.discreteHomEquiv_symm_app (p : V → diagram Y atomPoint) (U : Atom) (v : V) :
    ((DiagSet.discreteHomEquiv V Y).symm p).app (op U) v = Y.map (toAtomPoint U).op (p v) :=
  rfl

@[simp]
theorem DiagSet.discreteHomEquiv_symm_app_atomPoint (p : V → diagram Y atomPoint) (v : V) :
    ((DiagSet.discreteHomEquiv V Y).symm p).app (op atomPoint) v = p v :=
  congrFun ((DiagSet.discreteHomEquiv V Y).apply_symm_apply p) v

theorem DiagSet.isDegenerate_discrete {U : Atom} (hU : U.dimension ≠ 0)
    (x : diagram (DiagSet.discrete V) U) : IsDegenerate (DiagSet.discrete V) x := by
  refine ⟨atomPoint, toAtomPoint U, x, isCollapseHom_toAtomPoint U, fun hi => hU ?_, rfl⟩
  exact (Atom.dimension_eq_of_iso (asIso (toAtomPoint U))).trans dimension_atomPoint

noncomputable def DiagSet.discretePoint (v : V) : RoundPastingDiagram (DiagSet.discrete V) :=
  cellRound (X := DiagSet.discrete V) (U := atomPoint) v

theorem DiagSet.parallel_discretePoint (v w : V) :
    Parallel (DiagSet.discretePoint v) (DiagSet.discretePoint w) :=
  ⟨rfl, Or.inl dimension_atomPoint⟩

theorem DiagSet.discretePoint_mapTo (p : V → diagram Y atomPoint) (v : V) :
    (DiagSet.discretePoint v).mapTo ((DiagSet.discreteHomEquiv V Y).symm p) = cellRound (p v) :=
  (RoundPastingDiagram.ext (PastingDiagram.ofCell_app _ _)).symm.trans
    (congrArg cellRound (DiagSet.discreteHomEquiv_symm_app_atomPoint p v))

inductive Presentation : DiagSet.{u} → Type (u + 1)
  | discrete (V : Type u) : Presentation (DiagSet.discrete V)
  | extend {X : DiagSet.{u}} (p : Presentation X) (c : CellularExtensionData X) :
      Presentation c.extension

namespace Presentation

@[reducible] def Points : {X : DiagSet.{u}} → Presentation X → Type u
  | _, discrete V => V
  | _, extend p _ => p.Points

@[reducible] def Cells : {X : DiagSet.{u}} → Presentation X → Type u
  | _, discrete _ => PEmpty
  | _, extend p c => p.Cells ⊕ c.ι

noncomputable def point : {X : DiagSet.{u}} → (p : Presentation X) → p.Points →
    diagram X atomPoint
  | _, discrete _, v => v
  | _, extend p c, v => c.incl.app _ (p.point v)

noncomputable def shape : {X : DiagSet.{u}} → (p : Presentation X) → p.Cells → Atom
  | _, discrete _, a => PEmpty.elim a
  | _, extend p c, a => Sum.elim p.shape c.shape a

noncomputable def cell : {X : DiagSet.{u}} → (p : Presentation X) → (a : p.Cells) →
    diagram X (p.shape a)
  | _, discrete _, a => PEmpty.elim a
  | _, extend p c, a =>
    Sum.rec (motive := fun a => diagram c.extension (Sum.elim p.shape c.shape a))
      (fun a => c.incl.app _ (p.cell a)) c.cell a

noncomputable def boundary (α : Bool) : {X : DiagSet.{u}} → (p : Presentation X) → p.Cells →
    RoundPastingDiagram X
  | _, discrete _, a => PEmpty.elim a
  | _, extend p c, a => Sum.elim (fun a => (p.boundary α a).mapTo c.incl)
    (fun e => (cond α c.target c.source e).mapTo c.incl) a

noncomputable abbrev source (p : Presentation X) : p.Cells → RoundPastingDiagram X :=
  p.boundary false

noncomputable abbrev target (p : Presentation X) : p.Cells → RoundPastingDiagram X :=
  p.boundary true

theorem hasRoundType_cell : {X : DiagSet.{u}} → (p : Presentation X) → (a : p.Cells) →
    HasRoundType (PastingDiagram.ofCell (p.cell a)) (p.source a) (p.target a)
  | _, discrete _, a => PEmpty.elim a
  | _, extend p c, a => by
    rcases a with a | e
    · have h := (p.hasRoundType_cell a).mapTo c.incl
      rw [← PastingDiagram.ofCell_app] at h
      exact h
    · exact c.hasRoundType_cell e

theorem dimension_shape {X : DiagSet.{u}} (p : Presentation X) (a : p.Cells) :
    (p.shape a).dimension = (p.source a).dim + 1 :=
  (p.hasRoundType_cell a).dim_eq

theorem hom_ext : {X : DiagSet.{u}} → (p : Presentation X) → {φ ψ : X ⟶ Y} →
    (∀ v, φ.app _ (p.point v) = ψ.app _ (p.point v)) →
    (∀ a, φ.app _ (p.cell a) = ψ.app _ (p.cell a)) → φ = ψ
  | _, discrete V, _, _, h₀, _ => (DiagSet.discreteHomEquiv V Y).injective (funext h₀)
  | _, extend p c, _, _, h₀, h₁ =>
    c.hom_ext (p.hom_ext (fun v => (NatTrans.comp_app_apply _ _ _ _).trans ((h₀ v).trans
      (NatTrans.comp_app_apply _ _ _ _).symm)) fun a => (NatTrans.comp_app_apply _ _ _ _).trans
        ((h₁ (Sum.inl a : p.Cells ⊕ c.ι)).trans (NatTrans.comp_app_apply _ _ _ _).symm))
      fun e => h₁ (Sum.inr e : p.Cells ⊕ c.ι)

private noncomputable def interpData (Y : DiagSet.{u}) :
    {X : DiagSet.{u}} → Presentation X → Σ T : Type u, T → (X ⟶ Y)
  | _, discrete V => ⟨V → diagram Y atomPoint, (DiagSet.discreteHomEquiv V Y).symm⟩
  | _, extend p c =>
    ⟨Σ i : (interpData Y p).1, {g : ∀ e, diagram Y (c.shape e) // ∀ e,
        HasRoundType (PastingDiagram.ofCell (g e)) ((c.source e).mapTo ((interpData Y p).2 i))
          ((c.target e).mapTo ((interpData Y p).2 i))},
      fun i => c.desc _ i.2.1 i.2.2⟩

def Interp {X : DiagSet.{u}} (p : Presentation X) (Y : DiagSet.{u}) : Type u :=
  (interpData Y p).1

noncomputable def Interp.toHom {p : Presentation X} (i : p.Interp Y) : X ⟶ Y :=
  (interpData Y p).2 i

def Interp.ofPoints (q : V → diagram Y atomPoint) : (discrete V).Interp Y := q

def Interp.attach {p : Presentation X} {c : CellularExtensionData X} (i : p.Interp Y)
    (g : ∀ e, diagram Y (c.shape e))
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e)) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) :
    (p.extend c).Interp Y :=
  ⟨i, g, hg⟩

@[simp]
theorem Interp.toHom_ofPoints (q : V → diagram Y atomPoint) :
    (Interp.ofPoints q).toHom = (DiagSet.discreteHomEquiv V Y).symm q :=
  rfl

@[simp]
theorem Interp.toHom_attach {p : Presentation X} {c : CellularExtensionData X} (i : p.Interp Y)
    (g : ∀ e, diagram Y (c.shape e))
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e)) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) :
    (Interp.attach i g hg).toHom = c.desc i.toHom g hg :=
  rfl

private theorem Interp.attach_surjective {p : Presentation X} {c : CellularExtensionData X}
    (i : (p.extend c).Interp Y) : ∃ j g hg, Interp.attach j g hg = i :=
  ⟨i.1, i.2.1, i.2.2, rfl⟩

def Interp.point : {X : DiagSet.{u}} → {p : Presentation X} → p.Interp Y → p.Points →
    diagram Y atomPoint
  | _, discrete _, i, v => i v
  | _, extend _ _, i, v => Interp.point i.1 v

def Interp.cell : {X : DiagSet.{u}} → {p : Presentation X} → p.Interp Y → (a : p.Cells) →
    diagram Y (p.shape a)
  | _, discrete _, _, a => PEmpty.elim a
  | _, extend p c, i, a => Sum.rec (motive := fun a => diagram Y (Sum.elim p.shape c.shape a))
    (fun a => Interp.cell i.1 a) i.2.1 a

theorem Interp.toHom_app_point : {X : DiagSet.{u}} → {p : Presentation X} → (i : p.Interp Y) →
    (v : p.Points) → i.toHom.app (op atomPoint) (p.point v) = i.point v
  | _, discrete _, i, v => DiagSet.discreteHomEquiv_symm_app_atomPoint (Y := Y) i v
  | _, extend p c, i, v => by
    obtain ⟨j, g, hg, rfl⟩ := Interp.attach_surjective i
    exact (NatTrans.comp_app_apply _ _ _ _).symm.trans
      ((congrArg (fun φ => φ.app (op atomPoint) (p.point v)) (c.incl_desc j.toHom g hg)).trans
        (Interp.toHom_app_point j v))

theorem Interp.toHom_app_cell : {X : DiagSet.{u}} → {p : Presentation X} → (i : p.Interp Y) →
    (a : p.Cells) → i.toHom.app (op (p.shape a)) (p.cell a) = i.cell a
  | _, discrete _, _, a => PEmpty.elim a
  | _, extend p c, i, a => by
    obtain ⟨j, g, hg, rfl⟩ := Interp.attach_surjective i
    rcases a with a | e
    · exact (NatTrans.comp_app_apply _ _ _ _).symm.trans
        ((congrArg (fun φ => φ.app (op (p.shape a)) (p.cell a)) (c.incl_desc j.toHom g hg)).trans
          (Interp.toHom_app_cell j a))
    · exact c.desc_app_cell j.toHom g hg e

theorem Interp.exists_toHom_eq : {X : DiagSet.{u}} → (p : Presentation X) → (φ : X ⟶ Y) →
    ∃ i : p.Interp Y, i.toHom = φ
  | _, discrete V, φ => ⟨Interp.ofPoints (DiagSet.discreteHomEquiv V Y φ),
    (DiagSet.discreteHomEquiv V Y).symm_apply_apply φ⟩
  | _, extend p c, φ => by
    obtain ⟨j, hj⟩ := Interp.exists_toHom_eq p (c.incl ≫ φ)
    have hg : ∀ e, HasRoundType (PastingDiagram.ofCell (φ.app _ (c.cell e)))
        ((c.source e).mapTo j.toHom) ((c.target e).mapTo j.toHom) := fun e => by
      rw [hj]
      exact c.hasRoundType_app_cell φ e
    exact ⟨Interp.attach j _ hg, c.hom_ext ((c.incl_desc j.toHom _ hg).trans hj)
      fun e => c.desc_app_cell j.toHom _ hg e⟩

theorem Interp.toHom_injective : {X : DiagSet.{u}} → (p : Presentation X) →
    Function.Injective (Interp.toHom (Y := Y) (p := p))
  | _, discrete V, i, i', h => (DiagSet.discreteHomEquiv V Y).symm.injective h
  | _, extend p c, i, i', h => by
    obtain ⟨j, g, hg, rfl⟩ := Interp.attach_surjective i
    obtain ⟨j', g', hg', rfl⟩ := Interp.attach_surjective i'
    obtain rfl : j = j' := Interp.toHom_injective p
      (((c.incl_desc j.toHom g hg).symm.trans (congrArg (c.incl ≫ ·) h)).trans
        (c.incl_desc j'.toHom g' hg'))
    obtain rfl : g = g' := funext fun e =>
      ((c.desc_app_cell j.toHom g hg e).symm.trans
        (congrArg (fun φ => φ.app _ (c.cell e)) h)).trans (c.desc_app_cell j.toHom g' hg' e)
    rfl

theorem Interp.toHom_bijective {X : DiagSet.{u}} (p : Presentation X) :
    Function.Bijective (Interp.toHom (Y := Y) (p := p)) :=
  ⟨Interp.toHom_injective p, Interp.exists_toHom_eq p⟩

noncomputable def homEquiv {X : DiagSet.{u}} (p : Presentation X) (Y : DiagSet.{u}) :
    (X ⟶ Y) ≃ p.Interp Y :=
  (Equiv.ofBijective _ (Interp.toHom_bijective (Y := Y) p)).symm

@[simp]
theorem toHom_homEquiv {X : DiagSet.{u}} (p : Presentation X) (φ : X ⟶ Y) :
    (p.homEquiv Y φ).toHom = φ :=
  (Equiv.ofBijective _ (Interp.toHom_bijective (Y := Y) p)).apply_symm_apply φ

@[simp]
theorem homEquiv_toHom {X : DiagSet.{u}} (p : Presentation X) (i : p.Interp Y) :
    p.homEquiv Y i.toHom = i :=
  (Equiv.ofBijective _ (Interp.toHom_bijective (Y := Y) p)).symm_apply_apply i

noncomputable def Interp.extend {p : Presentation X} {c : CellularExtensionData X}
    (i : p.Interp Y) (g : c.ι → Σ H : Atom, diagram Y H)
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e).2) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) :
    (p.extend c).Interp Y :=
  Interp.attach i (fun e => (c.parallel e).reindexCell i.toHom (g e).2 (hg e))
    fun e => (c.parallel e).hasRoundType_reindexCell i.toHom (g e).2 (hg e)

@[reassoc (attr := simp)]
theorem Interp.incl_toHom_extend {p : Presentation X} {c : CellularExtensionData X}
    (i : p.Interp Y) (g : c.ι → Σ H : Atom, diagram Y H)
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e).2) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) :
    c.incl ≫ (i.extend g hg).toHom = i.toHom :=
  c.incl_desc i.toHom _ fun e => (c.parallel e).hasRoundType_reindexCell i.toHom (g e).2 (hg e)

theorem Interp.toHom_extend_app_cell {p : Presentation X} {c : CellularExtensionData X}
    (i : p.Interp Y) (g : c.ι → Σ H : Atom, diagram Y H)
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e).2) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) (e : c.ι) (σ : c.shape e ≅ (g e).1) :
    (i.extend g hg).toHom.app (op (c.shape e)) (c.cell e) = Y.map σ.hom.op (g e).2 := by
  refine (c.desc_app_cell i.toHom _
    (fun e => (c.parallel e).hasRoundType_reindexCell i.toHom (g e).2 (hg e)) e).trans ?_
  exact (c.parallel e).reindexCell_eq i.toHom (g e).2 (hg e) σ

theorem Interp.equiv_ofCell_toHom_extend_app_cell {p : Presentation X}
    {c : CellularExtensionData X} (i : p.Interp Y) (g : c.ι → Σ H : Atom, diagram Y H)
    (hg : ∀ e, HasRoundType (PastingDiagram.ofCell (g e).2) ((c.source e).mapTo i.toHom)
      ((c.target e).mapTo i.toHom)) (e : c.ι) :
    (PastingDiagram.ofCell ((i.extend g hg).toHom.app (op (c.shape e)) (c.cell e))).Equiv
      (PastingDiagram.ofCell (g e).2) := by
  obtain ⟨σ⟩ := (c.parallel e).nonempty_iso_of_hasRoundType i.toHom (g e).2 (hg e)
  rw [i.toHom_extend_app_cell g hg e σ]
  exact equiv_ofCell_map_iso σ (g e).2

end Presentation

end Atoms.Diagrammatic
