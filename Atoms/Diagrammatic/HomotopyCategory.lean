import Atoms.Diagrammatic.Joyal.Quillen
import Atoms.Diagrammatic.Vertex
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.TwoTruncated

open CategoryTheory Simplicial Opposite
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

section Edges

theorem hasBdry_ofCell_simplexEdge {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (f : SSet.Edge x y) :
    HasBdry false 0 (ofCell (f.edge : diagram X (atomSimplex 1)))
      (ofCell (x : diagram X (atomSimplex 0))) (ofCell (y : diagram X (atomSimplex 0))) :=
  ⟨dimension_atomSimplex 1, dimension_atomSimplex 0, dimension_atomSimplex 0,
    (equiv_boundary_ofCell_atomSimplex_one _ false).trans (ofCell_equiv_ofCell_iff.2 f.src_eq),
    (equiv_boundary_ofCell_atomSimplex_one _ true).trans (ofCell_equiv_ofCell_iff.2 f.tgt_eq)⟩

theorem pastable_ofCell_simplexEdge {x y z : (DiagSet.toSSet.obj X) _⦋0⦌} (f : SSet.Edge x y)
    (g : SSet.Edge y z) :
    (ofCell (f.edge : diagram X (atomSimplex 1))).Pastable
      (ofCell (g.edge : diagram X (atomSimplex 1))) 0 :=
  (hasBdry_ofCell_simplexEdge f).pastable (hasBdry_ofCell_simplexEdge g) (.refl _)

theorem equiv_boundary_ofCell_atomGlobe_one (c : diagram X (atomGlobe 1)) (α : Bool) :
    ((ofCell c).boundary 0 α).Equiv (ofCell (X.map (atomGlobeVertex α).op c)) := by
  have h := ((equiv_ofCell_map_iso atomSimplexOneIsoGlobe c).boundary 0 α).symm.trans
    (equiv_boundary_ofCell_atomSimplex_one (X.map atomSimplexOneIsoGlobe.hom.op c) α)
  rwa [← Functor.map_comp_apply, ← op_comp, simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom] at h

variable {x y z w : X.Vertex}

theorem equiv_ofCell_edgeEquivSSet (f : X.Edge x y) :
    (ofCell ((X.edgeEquivSSet f).edge : diagram X (atomSimplex 1))).Equiv (ofCell f.cell) :=
  equiv_ofCell_map_iso atomSimplexOneIsoGlobe f.cell

theorem equiv_ofCell_edgeEquivSSet_symm
    (f : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    (ofCell (f.edge : diagram X (atomSimplex 1))).Equiv (ofCell (X.edgeEquivSSet.symm f).cell) := by
  have h := equiv_ofCell_edgeEquivSSet (X.edgeEquivSSet.symm f)
  rwa [Equiv.apply_symm_apply] at h

theorem hasBdry_ofCell_edge (f : X.Edge x y) :
    HasBdry false 0 (ofCell f.cell) (ofCell x) (ofCell y) :=
  ⟨dimension_atomGlobe 1, dimension_atomPoint, dimension_atomPoint,
    (equiv_boundary_ofCell_atomGlobe_one _ false).trans (ofCell_equiv_ofCell_iff.2 f.src_eq),
    (equiv_boundary_ofCell_atomGlobe_one _ true).trans (ofCell_equiv_ofCell_iff.2 f.tgt_eq)⟩

theorem pastable_ofCell_edge (f : X.Edge x y) (g : X.Edge y z) :
    (ofCell f.cell).Pastable (ofCell g.cell) 0 :=
  (hasBdry_ofCell_edge f).pastable (hasBdry_ofCell_edge g) (.refl _)

@[implicit_reducible]
noncomputable def pasteEdges (f : X.Edge x y) (g : X.Edge y z) : RoundPastingDiagram X :=
  ⟨(ofCell f.cell).paste (ofCell g.cell) 0 (pastable_ofCell_edge f g),
    isRound_paste_of_dim (cellRound f.cell) (cellRound g.cell) (k := 0) (dimension_atomGlobe 1)
      (dimension_atomGlobe 1) _⟩

theorem hasBdry_pasteEdges (f : X.Edge x y) (g : X.Edge y z) :
    HasBdry false 0 (pasteEdges f g).toPastingDiagram (ofCell x) (ofCell z) := by
  have h := (hasBdry_ofCell_edge f).pasteOr (hasBdry_ofCell_edge g) (.refl _)
  rw [pasteOr_of (pastable_ofCell_edge f g)] at h
  exact h

theorem equiv_pasteEdges_edgeEquivSSet (f : X.Edge x y) (g : X.Edge y z) :
    (pasteEdges f g).toPastingDiagram.Equiv
      ((ofCell ((X.edgeEquivSSet f).edge : diagram X (atomSimplex 1))).paste
        (ofCell ((X.edgeEquivSSet g).edge : diagram X (atomSimplex 1))) 0
        (pastable_ofCell_simplexEdge _ _)) :=
  Equiv.paste (equiv_ofCell_edgeEquivSSet f).symm (equiv_ofCell_edgeEquivSSet g).symm
    (pastable_ofCell_edge f g) _

private theorem HasBdry.of_equivalent {u v : RoundPastingDiagram X} {a b : PastingDiagram X}
    {n : ℕ} (h : Equivalent u v) (t : HasBdry false n u.toPastingDiagram a b) :
    HasBdry false n v.toPastingDiagram a b :=
  have hk : n < u.dim := by rw [t.dim_h]; exact Nat.lt_succ_self n
  ⟨h.data.dim_eq.symm.trans t.dim_h, t.dim_a, t.dim_b,
    (h.equiv_boundary hk false).symm.trans t.side,
    (h.equiv_boundary hk true).symm.trans t.other⟩

theorem exists_equiv_ofCell_atomSimplex_one {U : Atom} (hU : U.dimension = 1)
    (c : diagram X U) : ∃ a : diagram X (atomSimplex 1), (ofCell c).Equiv (ofCell a) := by
  obtain ⟨φ⟩ := (nonempty_iso_atomGlobe_of_dimension_eq_one hU).map
      fun i => i.symm ≪≫ atomSimplexOneIsoGlobe.symm
  exact ⟨X.map φ.symm.hom.op c, (equiv_ofCell_map_iso φ.symm c).symm⟩

theorem exists_edge_equivalent_of_hasBdry (hX : HasWeakComposites X) (v : RoundPastingDiagram X)
    (hv : HasBdry false 0 v.toPastingDiagram (ofCell x) (ofCell z)) :
    ∃ h : X.Edge x z, Equivalent v (cellRound h.cell) := by
  obtain ⟨c, hc⟩ := hX v
  obtain ⟨a, ha⟩ := exists_equiv_ofCell_atomSimplex_one (hc.data.dim_eq.symm.trans hv.dim_h) c
  have hva : Equivalent v (cellRound (X.map atomSimplexOneIsoGlobe.inv.op a)) :=
    equivalent_trans hc (equivalent_of_equiv
      (ha.trans (equiv_ofCell_map_iso atomSimplexOneIsoGlobe.symm a).symm))
  have ht := HasBdry.of_equivalent hva hv
  exact ⟨⟨X.map atomSimplexOneIsoGlobe.inv.op a,
    ofCell_equiv_ofCell_iff.1 ((equiv_boundary_ofCell_atomGlobe_one _ false).symm.trans ht.side),
    ofCell_equiv_ofCell_iff.1 ((equiv_boundary_ofCell_atomGlobe_one _ true).symm.trans ht.other)⟩,
    hva⟩

theorem exists_edge_equivalent_pasteEdges (hX : HasWeakComposites X) (f : X.Edge x y)
    (g : X.Edge y z) : ∃ h : X.Edge x z, Equivalent (pasteEdges f g) (cellRound h.cell) :=
  exists_edge_equivalent_of_hasBdry hX _ (hasBdry_pasteEdges f g)

theorem equivalent_pasteEdges {f f' : X.Edge x y} {g g' : X.Edge y z}
    (hf : Equivalent (cellRound f.cell) (cellRound f'.cell))
    (hg : Equivalent (cellRound g.cell) (cellRound g'.cell)) :
    Equivalent (pasteEdges f g) (pasteEdges f' g') :=
  equivalent_trans
    (equivalent_paste_left (v := cellRound g.cell) hf rfl
      (pastable_ofCell_edge f g) (pastable_ofCell_edge f' g)
      (pasteEdges f g).isRound (pasteEdges f' g).isRound)
    (equivalent_paste_right (u := cellRound f'.cell) hg rfl rfl
      (pastable_ofCell_edge f' g) (pastable_ofCell_edge f' g')
      (pasteEdges f' g).isRound (pasteEdges f' g').isRound)

theorem equiv_ofCell_edge_id_unit (x : X.Vertex) :
    (ofCell (DiagSet.Edge.id x).cell).Equiv (ofCell x).unit := by
  have h := equiv_ofCell_edgeEquivSSet (DiagSet.Edge.id x)
  rw [DiagSet.edgeEquivSSet_id] at h
  exact h.symm.trans (equiv_unit_ofCell_atomSimplex_zero (X.vertexEquivSSet x)).symm

theorem equivalent_pasteEdges_id (α : Bool) (f : X.Edge x y) :
    Equivalent (cond α (pasteEdges f (DiagSet.Edge.id y))
      (pasteEdges (DiagSet.Edge.id x) f)) (cellRound f.cell) := by
  let p := cond α (pasteEdges f (DiagSet.Edge.id y))
    (pasteEdges (DiagSet.Edge.id x) f)
  have eu : (ofCell (DiagSet.Edge.id (cond α y x)).cell).Equiv
      ((ofCell f.cell).boundary 0 α).unit := by
    refine (equiv_ofCell_edge_id_unit _).trans ?_
    apply PastingDiagram.Equiv.unit
    cases α
    · exact (hasBdry_ofCell_edge f).side.symm
    · exact (hasBdry_ofCell_edge f).other.symm
  have hp : (cond α (ofCell f.cell) ((ofCell f.cell).boundary 0 α).unit).Pastable
      (cond α ((ofCell f.cell).boundary 0 α).unit (ofCell f.cell)) 0 := by
    cases α
    · exact (pastable_ofCell_edge (DiagSet.Edge.id x) f).of_equiv eu (.refl _)
    · exact (pastable_ofCell_edge f (DiagSet.Edge.id y)).of_equiv (.refl _) eu
  have E : p.toPastingDiagram.Equiv
      ((cond α (ofCell f.cell) ((ofCell f.cell).boundary 0 α).unit).paste
        (cond α ((ofCell f.cell).boundary 0 α).unit (ofCell f.cell)) 0 hp) := by
    cases α
    · exact Equiv.paste eu (.refl _) (pastable_ofCell_edge (DiagSet.Edge.id x) f) hp
    · exact Equiv.paste (.refl _) eu (pastable_ofCell_edge f (DiagSet.Edge.id y)) hp
  have hr := E.isRound_iff.1 p.isRound
  exact equivalent_trans (equivalent_of_equiv (u := p) (v := ⟨_, hr⟩) E)
    (equivalent_symm (equivalent_paste_unit_cond α (cellRound f.cell)
      (n := 0) (dimension_atomGlobe 1) hp hr))

theorem equivalent_pasteEdges_id_left (f : X.Edge x y) :
    Equivalent (pasteEdges (DiagSet.Edge.id x) f) (cellRound f.cell) :=
  equivalent_pasteEdges_id false f

theorem equivalent_pasteEdges_id_right (f : X.Edge x y) :
    Equivalent (pasteEdges f (DiagSet.Edge.id y)) (cellRound f.cell) :=
  equivalent_pasteEdges_id true f

private theorem equivalent_pasteEdges_assoc {f : X.Edge w x} {g : X.Edge x y}
    {h : X.Edge y z} {fg : X.Edge w y} {gh : X.Edge x z}
    (hfg : Equivalent (pasteEdges f g) (cellRound fg.cell))
    (hgh : Equivalent (pasteEdges g h) (cellRound gh.cell)) :
    Equivalent (pasteEdges fg h) (pasteEdges f gh) := by
  have p₂ := pastable_of_equivalent_left (v := cellRound h.cell)
    (equivalent_symm hfg) (pastable_ofCell_edge fg h)
  obtain ⟨p₃, p₄, e⟩ := equiv_paste_assoc (pastable_ofCell_edge f g) p₂
  have r₂ := isRound_paste_of_dim (pasteEdges f g) (cellRound h.cell)
    ((hasBdry_pasteEdges f g).dim_h) (dimension_atomGlobe 1) p₂
  have r₄ := e.isRound_iff.1 r₂
  exact equivalent_trans
    (equivalent_paste_left (v := cellRound h.cell)
      (equivalent_symm hfg) rfl (pastable_ofCell_edge fg h) p₂ (pasteEdges fg h).isRound r₂)
    (equivalent_trans (equivalent_of_equiv (u := ⟨_, r₂⟩) (v := ⟨_, r₄⟩) e)
      (equivalent_paste_right (u := cellRound f.cell)
        (v := pasteEdges g h) hgh rfl
        ((dimension_atomGlobe 1).trans (hasBdry_pasteEdges g h).dim_h.symm) p₄
        (pastable_ofCell_edge f gh) r₄ (pasteEdges f gh).isRound))

end Edges

structure HomotopyCategory (X : DiagSet.{u}) (hX : HasWeakComposites X) : Type u where
  pt : X.Vertex

namespace HomotopyCategory

def edgeSetoid (X : DiagSet.{u}) (x y : X.Vertex) : Setoid (X.Edge x y) where
  r f g := Equivalent (cellRound f.cell) (cellRound g.cell)
  iseqv := ⟨fun _ => equivalent_refl _, equivalent_symm, equivalent_trans⟩

variable {x y z : X.Vertex}

private noncomputable def comp (hX : HasWeakComposites X) :
    Quotient (edgeSetoid X x y) → Quotient (edgeSetoid X y z) → Quotient (edgeSetoid X x z) :=
  Quotient.lift₂ (fun f g => ⟦(exists_edge_equivalent_pasteEdges hX f g).choose⟧)
    fun f g f' g' hf hg => Quotient.sound (equivalent_trans
      (equivalent_symm (exists_edge_equivalent_pasteEdges hX f g).choose_spec)
      (equivalent_trans (equivalent_pasteEdges hf hg)
        (exists_edge_equivalent_pasteEdges hX f' g').choose_spec))

private theorem comp_mk_mk_eq_mk_iff (hX : HasWeakComposites X) (f : X.Edge x y)
    (g : X.Edge y z) (h : X.Edge x z) :
    comp hX ⟦f⟧ ⟦g⟧ = ⟦h⟧ ↔ Equivalent (pasteEdges f g) (cellRound h.cell) :=
  Quotient.eq.trans
    ⟨equivalent_trans (exists_edge_equivalent_pasteEdges hX f g).choose_spec,
      equivalent_trans (equivalent_symm (exists_edge_equivalent_pasteEdges hX f g).choose_spec)⟩

private theorem comp_id (hX : HasWeakComposites X) (α : Bool)
    (f : Quotient (edgeSetoid X x y)) :
    (match α with
      | true => comp hX f ⟦DiagSet.Edge.id y⟧
      | false => comp hX ⟦DiagSet.Edge.id x⟧ f) = f := by
  induction f using Quotient.inductionOn with
  | h f =>
    have hid := equivalent_pasteEdges_id α f
    cases α <;> exact (comp_mk_mk_eq_mk_iff hX _ _ f).2 hid

end HomotopyCategory

open HomotopyCategory in
noncomputable instance (hX : HasWeakComposites X) : Category (HomotopyCategory X hX) where
  Hom a b := Quotient (edgeSetoid X a.pt b.pt)
  id a := ⟦DiagSet.Edge.id a.pt⟧
  comp := comp hX
  id_comp f := comp_id hX false f
  comp_id f := comp_id hX true f
  assoc := by
    rintro a b c d ⟨f⟩ ⟨g⟩ ⟨h⟩
    obtain ⟨fg, hfg⟩ := exists_edge_equivalent_pasteEdges hX f g
    obtain ⟨gh, hgh⟩ := exists_edge_equivalent_pasteEdges hX g h
    have e₁ : comp hX ⟦f⟧ ⟦g⟧ = ⟦fg⟧ := (comp_mk_mk_eq_mk_iff hX f g fg).2 hfg
    have e₂ : comp hX ⟦g⟧ ⟦h⟧ = ⟦gh⟧ := (comp_mk_mk_eq_mk_iff hX g h gh).2 hgh
    obtain ⟨c, hc⟩ := exists_edge_equivalent_pasteEdges hX fg h
    refine (congrArg (comp hX · ⟦h⟧) e₁).trans (((comp_mk_mk_eq_mk_iff hX fg h c).2 hc).trans
      ((congrArg (comp hX ⟦f⟧ ·) e₂).trans ((comp_mk_mk_eq_mk_iff hX f gh c).2 ?_)).symm)
    exact equivalent_trans (equivalent_symm (equivalent_pasteEdges_assoc hfg hgh)) hc

namespace HomotopyCategory

def homMk (hX : HasWeakComposites X) {x y : X.Vertex} (f : X.Edge x y) :
    (⟨x⟩ : HomotopyCategory X hX) ⟶ ⟨y⟩ :=
  ⟦f⟧

theorem homMk_surjective (hX : HasWeakComposites X) {x y : X.Vertex}
    (φ : (⟨x⟩ : HomotopyCategory X hX) ⟶ ⟨y⟩) : ∃ f : X.Edge x y, HomotopyCategory.homMk hX f = φ :=
  Quotient.exists_rep φ

theorem homMk_eq_homMk_iff (hX : HasWeakComposites X) {x y : X.Vertex} (f g : X.Edge x y) :
    HomotopyCategory.homMk hX f = HomotopyCategory.homMk hX g ↔
      Equivalent (cellRound f.cell) (cellRound g.cell) :=
  Quotient.eq

theorem homMk_id (hX : HasWeakComposites X) (x : X.Vertex) :
    HomotopyCategory.homMk hX (DiagSet.Edge.id x) = 𝟙 (⟨x⟩ : HomotopyCategory X hX) :=
  rfl

theorem homMk_comp_homMk_iff (hX : HasWeakComposites X) {x y z : X.Vertex} (f : X.Edge x y)
    (g : X.Edge y z) (h : X.Edge x z) :
    HomotopyCategory.homMk hX f ≫ HomotopyCategory.homMk hX g = HomotopyCategory.homMk hX h ↔
      Equivalent (pasteEdges f g) (cellRound h.cell) :=
  comp_mk_mk_eq_mk_iff hX f g h

theorem isIso_homMk_iff (hX : HasWeakComposites X) {x y : X.Vertex} (f : X.Edge x y) :
    IsIso (HomotopyCategory.homMk hX f) ↔ IsEquivalence X f.cell := by
  have hxr := (cellRound x).isRound
  have hyr := (cellRound y).isRound
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := homMk_surjective hX (inv (homMk hX f))
    have h₁ := (homMk_comp_homMk_iff hX f g (DiagSet.Edge.id x)).1
      (by rw [hg, IsIso.hom_inv_id]; rfl)
    have h₂ := (homMk_comp_homMk_iff hX g f (DiagSet.Edge.id y)).1
      (by rw [hg, IsIso.inv_hom_id]; rfl)
    refine mem_equivalences_of_equivalent_unit (e := cellRound f.cell)
      (e' := cellRound g.cell) (hasBdry_ofCell_edge f)
      (hasBdry_ofCell_edge g) hxr hyr ?_ ?_
    · exact equivalent_trans h₁ (equivalent_of_equiv (equiv_ofCell_edge_id_unit x))
    · exact equivalent_symm
        (equivalent_trans h₂ (equivalent_of_equiv (equiv_ofCell_edge_id_unit y)))
  · intro hf
    obtain ⟨e', he'⟩ := exists_isWeakInverse hf
    obtain ⟨hr', te', ⟨z, hz, hzm, tz⟩, ⟨v, hv, hvm, tv⟩⟩ := he'.spec (hasBdry_ofCell_edge f)
    obtain ⟨g, hg⟩ := exists_edge_equivalent_of_hasBdry hX ⟨e'.toPastingDiagram, hr'⟩ te'
    have p₁ := (hasBdry_ofCell_edge f).pastable te' (.refl _)
    have p₂ := te'.pastable (hasBdry_ofCell_edge f) (.refl _)
    have tz' : HasBdry false (0 + 1) z ((ofCell f.cell).paste e'.toPastingDiagram 0 p₁)
        (ofCell x).unit := by
      rw [← pasteOr_of p₁]; exact tz
    have tv' : HasBdry false (0 + 1) v (ofCell y).unit (e'.paste (ofCell f.cell) 0 p₂) := by
      rw [← pasteOr_of p₂]; exact tv
    have r₁ := isRound_paste_of_dim (cellRound f.cell) ⟨e'.toPastingDiagram, hr'⟩
      (dimension_atomGlobe 1) te'.dim_h p₁
    have r₂ := isRound_paste_of_dim ⟨e'.toPastingDiagram, hr'⟩ (cellRound f.cell)
      te'.dim_h (dimension_atomGlobe 1) p₂
    have E₁ : Equivalent (⟨_, r₁⟩ : RoundPastingDiagram X) hxr.unit :=
      equivalent_of_mem_equivalences_cond false hzm tz'.dim_a tz'.dim_b tz'.dim_h tz'.side
        tz'.other
    have E₂ : Equivalent hyr.unit (⟨_, r₂⟩ : RoundPastingDiagram X) :=
      equivalent_of_mem_equivalences_cond false hvm tv'.dim_a tv'.dim_b tv'.dim_h tv'.side
        tv'.other
    refine ⟨homMk hX g, (homMk_comp_homMk_iff hX f g _).2 ?_,
      (homMk_comp_homMk_iff hX g f _).2 ?_⟩
    · refine equivalent_trans (equivalent_paste_right
        (u := cellRound f.cell) (equivalent_symm hg) rfl rfl
        (pastable_ofCell_edge f g) p₁ (pasteEdges f g).isRound r₁) (equivalent_trans E₁ ?_)
      exact equivalent_of_equiv (equiv_ofCell_edge_id_unit x).symm
    · refine equivalent_trans (equivalent_paste_left
        (v := cellRound f.cell) (equivalent_symm hg) rfl
        (pastable_ofCell_edge g f) p₂ (pasteEdges g f).isRound r₂)
        (equivalent_trans (equivalent_symm E₂) ?_)
      exact equivalent_of_equiv (equiv_ofCell_edge_id_unit y).symm

end HomotopyCategory

section Functoriality

variable {Z : DiagSet.{u}} {x y z : X.Vertex}

private theorem cellRound_edge_map (F : X ⟶ Y) (f : X.Edge x y) :
    cellRound (f.map F).cell =
      ⟨(cellRound f.cell).toPastingDiagram.mapTo F, (cellRound f.cell).isRound⟩ :=
  RoundPastingDiagram.ext (PastingDiagram.ofCell_app F f.cell)

private theorem equivalent_edge_map (F : X ⟶ Y) {f g : X.Edge x y}
    (h : Equivalent (cellRound f.cell) (cellRound g.cell)) :
    Equivalent (cellRound (f.map F).cell) (cellRound (g.map F).cell) := by
  rw [cellRound_edge_map, cellRound_edge_map]
  exact h.map F

private theorem equivalent_pasteEdges_map (F : X ⟶ Y) {f : X.Edge x y} {g : X.Edge y z}
    {h : X.Edge x z} (hc : Equivalent (pasteEdges f g) (cellRound h.cell)) :
    Equivalent (pasteEdges (f.map F) (g.map F)) (cellRound (h.map F).cell) := by
  have ef : (cellRound (f.map F).cell).toPastingDiagram.Equiv ((ofCell f.cell).mapTo F) := by
    rw [cellRound_edge_map]
    exact .refl _
  have eg : (cellRound (g.map F).cell).toPastingDiagram.Equiv ((ofCell g.cell).mapTo F) := by
    rw [cellRound_edge_map]
    exact .refl _
  have hp := (pastable_ofCell_edge f g).mapTo F
  have E := (Equiv.paste ef eg (pastable_ofCell_edge _ _) hp).trans
    (paste_mapTo _ _ 0 (pastable_ofCell_edge f g) F hp).symm
  rw [cellRound_edge_map]
  exact equivalent_trans (equivalent_of_equiv
    (v := ⟨(pasteEdges f g).toPastingDiagram.mapTo F, (pasteEdges f g).isRound⟩) E) (hc.map F)

private def homotopyFunctorMap (hX : HasWeakComposites X)
    (hY : HasWeakComposites Y) (F : X ⟶ Y) {a b : HomotopyCategory X hX} (φ : a ⟶ b) :
    (⟨a.pt.map F⟩ : HomotopyCategory Y hY) ⟶ ⟨b.pt.map F⟩ :=
  Quotient.map (fun f => f.map F) (fun _ _ h => equivalent_edge_map F h) φ

def homotopyFunctor (hX : HasWeakComposites X) (hY : HasWeakComposites Y)
    (F : X ⟶ Y) : HomotopyCategory X hX ⥤ HomotopyCategory Y hY where
  obj a := ⟨a.pt.map F⟩
  map := homotopyFunctorMap hX hY F
  map_id a := congrArg (HomotopyCategory.homMk hY) (DiagSet.Edge.map_id a.pt F)
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    obtain ⟨h, hh⟩ := exists_edge_equivalent_pasteEdges hX f g
    exact (congrArg (homotopyFunctorMap hX hY F)
      ((HomotopyCategory.homMk_comp_homMk_iff hX f g h).2 hh)).trans
      ((HomotopyCategory.homMk_comp_homMk_iff hY _ _ _).2 (equivalent_pasteEdges_map F hh)).symm

theorem homotopyFunctor_map_homMk (hX : HasWeakComposites X) (hY : HasWeakComposites Y)
    (F : X ⟶ Y) {x y : X.Vertex} (f : X.Edge x y) :
    (homotopyFunctor hX hY F).map (HomotopyCategory.homMk hX f) =
      HomotopyCategory.homMk hY (f.map F) :=
  rfl

theorem homotopyFunctor_id (hX : HasWeakComposites X) :
    homotopyFunctor hX hX (𝟙 X) = 𝟭 (HomotopyCategory X hX) :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ φ => by
    induction φ using Quotient.inductionOn
    exact HEq.rfl

theorem homotopyFunctor_comp (hX : HasWeakComposites X) (hY : HasWeakComposites Y)
    (hZ : HasWeakComposites Z) (F : X ⟶ Y) (G : Y ⟶ Z) :
    homotopyFunctor hX hZ (F ≫ G) = homotopyFunctor hX hY F ⋙ homotopyFunctor hY hZ G :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ φ => by
    induction φ using Quotient.inductionOn
    exact HEq.rfl

end Functoriality

section Comparison

variable {x y z : X.Vertex}

private theorem equivalent_pasteEdges_of_compStruct (hX : IsInftyCategory 1 X)
    {f : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)}
    {g : SSet.Edge (X.vertexEquivSSet y) (X.vertexEquivSSet z)}
    {h : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet z)} (σ : SSet.Edge.CompStruct f g h) :
    Equivalent (pasteEdges (X.edgeEquivSSet.symm f) (X.edgeEquivSSet.symm g))
      (cellRound (X.edgeEquivSSet.symm h).cell) := by
  let s : diagram X (atomSimplex 2) := σ.simplex
  have hs : cellRound s ∈ equivalences X :=
    hX.2 (atomSimplex 2) s (by rw [dimension_atomSimplex]; exact_mod_cast (by omega : 1 < 2))
  have e₁ : ((ofCell s).boundary 1 false).Equiv (ofCell (X.edgeEquivSSet.symm h).cell) :=
    (equiv_boundary_false_ofCell_atomSimplex_two s).trans ((ofCell_equiv_ofCell_iff.2 σ.d₁).trans
      (equiv_ofCell_edgeEquivSSet_symm h))
  have e₂ : ((ofCell s).boundary 1 true).Equiv
      (pasteEdges (X.edgeEquivSSet.symm f) (X.edgeEquivSSet.symm g)).toPastingDiagram :=
    (equiv_boundary_true_ofCell_atomSimplex_two s).trans (Equiv.paste
      ((ofCell_equiv_ofCell_iff.2 σ.d₂).trans (equiv_ofCell_edgeEquivSSet_symm f))
      ((ofCell_equiv_ofCell_iff.2 σ.d₀).trans (equiv_ofCell_edgeEquivSSet_symm g)) _
      (pastable_ofCell_edge _ _))
  exact equivalent_symm (equivalent_of_mem_equivalences_cond false hs (dimension_atomGlobe 1)
    (hasBdry_pasteEdges _ _).dim_h (dimension_atomSimplex 2) e₁ e₂)

private theorem nonempty_compStruct_of_equivalent (hX : IsInftyCategory 1 X)
    {f g : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)}
    (hfg : Equivalent (cellRound (X.edgeEquivSSet.symm f).cell)
      (cellRound (X.edgeEquivSSet.symm g).cell)) :
    Nonempty (SSet.Edge.CompStruct f (SSet.Edge.id (X.vertexEquivSSet y)) g) := by
  have h₁ : Equivalent (cellRound (X.edgeEquivSSet.symm g).cell)
      (pasteEdges (X.edgeEquivSSet.symm f) (DiagSet.Edge.id y)) :=
    equivalent_trans (equivalent_symm hfg) (equivalent_symm (equivalent_pasteEdges_id_right _))
  obtain ⟨U, c, -, hU, hc₁, hc₂⟩ := exists_equivalence_cell_side hX.1 false _ _ h₁
  have hd : (cellRound (X.edgeEquivSSet.symm g).cell).dim = 1 := dimension_atomGlobe 1
  rw [hd] at hU hc₁ hc₂
  have hc₁' := hc₁.trans (equiv_ofCell_edgeEquivSSet_symm g).symm
  have hc₂' := hc₂.trans (equiv_pasteEdges_edgeEquivSSet _ (DiagSet.Edge.id y))
  rw [DiagSet.edgeEquivSSet_id, Equiv.apply_symm_apply] at hc₂'
  let τ : diagram X (atomSimplex 2) := (DiagSet.toSSet.obj X).σ 0 g.edge
  have hτ₁ := (equiv_boundary_false_ofCell_atomSimplex_two τ)
  have hτ₂ := (equiv_boundary_true_ofCell_atomSimplex_two τ)
  have hsh : ((ofCell (f.edge : diagram X (atomSimplex 1))).paste
        (ofCell ((SSet.Edge.id (X.vertexEquivSSet y)).edge : diagram X (atomSimplex 1))) 0
        (pastable_ofCell_simplexEdge _ _)).shape.ogp =
      ((ofCell ((DiagSet.toSSet.obj X).δ 2 τ : diagram X (atomSimplex 1))).paste
        (ofCell ((DiagSet.toSSet.obj X).δ 0 τ : diagram X (atomSimplex 1))) 0
        (pastable_ofCell_atomSimplex_two τ)).shape.ogp := by
    have : Subsingleton (((atomSimplex 1).toMoleculeShape.boundary 0 true).ogp ≅
        ((atomSimplex 1).toMoleculeShape.boundary 0 false).ogp) :=
      ((atomSimplex 1).toMoleculeShape.boundary 0 true).isMolecule.subsingleton_iso
    exact congrArg (fun ψ => ((atomSimplex 1).toMoleculeShape.paste
      (atomSimplex 1).toMoleculeShape 0 ψ).ogp) (Subsingleton.elim _ _)
  obtain ⟨φ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso U.toMoleculeShape
    (atomSimplex 2).toMoleculeShape (n := 1)
    (fun α => by
      cases α
      · exact hc₁'.iso ≪≫ hτ₁.iso.symm
      · exact hc₂'.iso ≪≫ eqToIso hsh ≪≫ hτ₂.iso.symm)
    U.isAtom (atomSimplex 2).isAtom hU (dimension_atomSimplex 2)
  let Φ : atomSimplex 2 ≅ U := (Atom.isoOfOGPIso φ).symm
  let s : diagram X (atomSimplex 2) := X.map Φ.hom.op c
  have hs := equiv_ofCell_map_iso Φ c
  have d₁ : (DiagSet.toSSet.obj X).δ 1 s = g.edge :=
    ofCell_equiv_ofCell_iff.1 ((equiv_boundary_false_ofCell_atomSimplex_two s).symm.trans
      ((hs.boundary 1 false).trans hc₁'))
  have d₂₀ := eq_of_equiv_paste (pastable_ofCell_atomSimplex_two s)
    (pastable_ofCell_simplexEdge f (SSet.Edge.id (X.vertexEquivSSet y)))
    ((equiv_boundary_true_ofCell_atomSimplex_two s).symm.trans ((hs.boundary 1 true).trans hc₂'))
  exact ⟨SSet.Edge.CompStruct.mk s (ofCell_map_injective d₂₀.1) (ofCell_map_injective d₂₀.2) d₁⟩

theorem homMk_comp_homMk_of_compStruct (hX : IsInftyCategory 1 X) {x y z : X.Vertex}
    {f : X.Edge x y} {g : X.Edge y z} {h : X.Edge x z}
    (σ : SSet.Edge.CompStruct (X.edgeEquivSSet f) (X.edgeEquivSSet g) (X.edgeEquivSSet h)) :
    HomotopyCategory.homMk hX.1 f ≫ HomotopyCategory.homMk hX.1 g =
      HomotopyCategory.homMk hX.1 h := by
  have hc := equivalent_pasteEdges_of_compStruct hX σ
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hc
  exact (HomotopyCategory.homMk_comp_homMk_iff hX.1 f g h).2 hc

private theorem homMk_edgeEquivSSet_symm_id (hX : HasWeakComposites X) (x : X.Vertex) :
    HomotopyCategory.homMk hX (X.edgeEquivSSet.symm (SSet.Edge.id (X.vertexEquivSSet x))) =
      𝟙 (⟨x⟩ : HomotopyCategory X hX) :=
  (congrArg (HomotopyCategory.homMk hX)
    (DiagSet.edgeEquivSSet_symm_id x)).trans
    (HomotopyCategory.homMk_id hX x)

private noncomputable def toNative (hX : IsInftyCategory 1 X) :
    SSet.hoFunctor.obj (DiagSet.toSSet.obj X) ⥤ HomotopyCategory X hX.1 :=
  SSet.Truncated.HomotopyCategory.lift (fun x => ⟨X.vertexEquivSSet.symm x⟩)
    (fun e => HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm (SSet.Edge.ofTruncated e)))
    (fun x => homMk_edgeEquivSSet_symm_id hX.1 (X.vertexEquivSSet.symm x))
    (fun σ => (HomotopyCategory.homMk_comp_homMk_iff hX.1 _ _ _).2
      (equivalent_pasteEdges_of_compStruct hX (SSet.Edge.CompStruct.ofTruncated σ)))

private theorem toNative_map_homMk (hX : IsInftyCategory 1 X)
    (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    (toNative hX).map (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) =
      HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm e) :=
  SSet.Truncated.HomotopyCategory.lift_map_homMk
    (V := (SSet.truncation 2).obj (DiagSet.toSSet.obj X))
    (fun x => (⟨X.vertexEquivSSet.symm x⟩ : HomotopyCategory X hX.1))
    (fun e => HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm (SSet.Edge.ofTruncated e)))
    (fun x => homMk_edgeEquivSSet_symm_id hX.1 (X.vertexEquivSSet.symm x))
    (fun σ => (HomotopyCategory.homMk_comp_homMk_iff hX.1 _ _ _).2
      (equivalent_pasteEdges_of_compStruct hX (SSet.Edge.CompStruct.ofTruncated σ))) e.toTruncated

private theorem isEquivalence_toNative (hX : IsInftyCategory 1 X) :
    (toNative hX).IsEquivalence := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  have hess : (toNative hX).EssSurj :=
    ⟨fun a => ⟨SSet.Truncated.HomotopyCategory.mk (X.vertexEquivSSet a.pt), ⟨Iso.refl _⟩⟩⟩
  have hfaith : (toNative hX).Faithful := by
    refine ⟨fun {a b} φ ψ hφψ => ?_⟩
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, rfl⟩ := SSet.Truncated.HomotopyCategory.homMk_surjective φ
    obtain ⟨e', rfl⟩ := SSet.Truncated.HomotopyCategory.homMk_surjective ψ
    have h := (toNative_map_homMk hX (x := X.vertexEquivSSet.symm x)
      (y := X.vertexEquivSSet.symm y) (SSet.Edge.ofTruncated e)).symm.trans
      (hφψ.trans (toNative_map_homMk hX (SSet.Edge.ofTruncated e')))
    exact (SSet.Truncated.HomotopyCategory.homMk_eq_homMk_iff e e').2
      (nonempty_compStruct_of_equivalent hX ((HomotopyCategory.homMk_eq_homMk_iff hX.1 _ _).1 h))
  have hfull : (toNative hX).Full := by
    refine ⟨fun {a b} φ => ?_⟩
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, he⟩ := HomotopyCategory.homMk_surjective hX.1 φ
    exact ⟨SSet.Truncated.HomotopyCategory.homMk (X.edgeEquivSSet e).toTruncated,
      ((toNative_map_homMk hX (X.edgeEquivSSet e)).trans (congrArg (HomotopyCategory.homMk hX.1)
        (X.edgeEquivSSet.symm_apply_apply e))).trans he⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

noncomputable def homotopyCategoryEquivalence (hX : IsInftyCategory 1 X) :
    HomotopyCategory X hX.1 ≌ SSet.hoFunctor.obj (DiagSet.toSSet.obj X) :=
  (@Functor.asEquivalence _ _ _ _ (toNative hX) (isEquivalence_toNative hX)).symm

theorem homotopyCategoryEquivalence_inverse_obj (hX : IsInftyCategory 1 X)
    (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (homotopyCategoryEquivalence hX).inverse.obj (SSet.Truncated.HomotopyCategory.mk x) =
      ⟨X.vertexEquivSSet.symm x⟩ :=
  rfl

theorem homotopyCategoryEquivalence_inverse_map_homMk (hX : IsInftyCategory 1 X)
    (e : SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y)) :
    (homotopyCategoryEquivalence hX).inverse.map
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) =
      HomotopyCategory.homMk hX.1 (X.edgeEquivSSet.symm e) :=
  toNative_map_homMk hX e

end Comparison

end Atoms.Diagrammatic
