import Atoms.Diagrammatic.Marked.ComparisonCell
import Atoms.Diagrammatic.Marked.NaturalMarking

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : MarkedDiagSet.{u}}

def TopMarked (X : MarkedDiagSet.{u}) (p : PastingDiagram X.underlying) : Prop :=
  ∀ t : p.shape.ogp, grade ℕ t = p.dim → p.cellAt t ∈ X.marked _

theorem equiv_ofCell_cellAt_within {Y : DiagSet.{u}} {v m : PastingDiagram Y} (W : Within v m)
    (t : v.shape.ogp) : (ofCell (v.cellAt t)).Equiv (ofCell (m.cellAt (W.emb t))) := by
  refine equiv_of_emb_of_image_eq (C := m.shape.rdc) m.map (v.principalEmb t ≫ W.emb)
    (m.principalEmb (W.emb t)) ?_ ?_ ?_
  · rw [ofCell_cellAt_map, ← W.comm, ← Category.assoc, ← realize.map_comp]
    exact congrArg (fun φ => realize.map φ ≫ m.map) (by ext; rfl)
  · rw [ofCell_cellAt_map]
    exact congrArg (fun φ => realize.map φ ≫ m.map) (by ext; rfl)
  · rw [map_comp, image_principalEmb, map_Iic, image_principalEmb]

theorem topMarked_of_cover {m v₁ v₂ : PastingDiagram X.underlying} (W₁ : Within v₁ m)
    (W₂ : Within v₂ m) (hcov : ⊤ = W₁.image ⊔ W₂.image) (hd₁ : v₁.dim = m.dim)
    (hd₂ : v₂.dim = m.dim) (h₁ : TopMarked X v₁) (h₂ : TopMarked X v₂) : TopMarked X m := by
  intro t ht
  have hmem : t ∈ W₁.image ⊔ W₂.image := hcov ▸ LowerSet.mem_top
  rcases hmem with ⟨t', -, rfl⟩ | ⟨t', -, rfl⟩
  · rw [(isMorphism W₁.emb).grade_eq] at ht
    exact (mem_marked_iff_of_equiv_ofCell (equiv_ofCell_cellAt_within W₁ t')).1
      (h₁ t' (ht.trans hd₁.symm))
  · rw [(isMorphism W₂.emb).grade_eq] at ht
    exact (mem_marked_iff_of_equiv_ofCell (equiv_ofCell_cellAt_within W₂ t')).1
      (h₂ t' (ht.trans hd₂.symm))

theorem PasteAtData.topMarked {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X.underlying}
    (d : PasteAtData α n e u') (he : TopMarked X e.toPastingDiagram)
    (hu : TopMarked X u'.toPastingDiagram) : TopMarked X d.pasting :=
  topMarked_of_cover d.pasteAtInl d.pasteAtInr d.isPastingAtIn_pasteAtInl.eq_sup
    (d.dim_e.trans d.dim_pasting.symm) (d.dim_u'.trans d.dim_pasting.symm) he hu

theorem topMarked_ofCell {W : Atom} {w : diagram X.underlying W} (hw : w ∈ X.marked W) :
    TopMarked X (ofCell w) := by
  intro t ht
  obtain rfl : t = W.top := GradeOrder.eq_of_le_of_grade_le (W.le_top t)
    (by rw [← W.dimension_eq]; exact ht.ge)
  refine (mem_marked_iff_of_equiv_ofCell ?_).2 hw
  refine equiv_of_emb_of_image_eq (C := (ofCell w).shape.rdc) (ofCell w).map
    ((ofCell w).principalEmb W.top) (𝟙 _) ?_ ?_ ?_
  · rw [ofCell_cellAt_map]
    exact congrArg (fun φ => realize.map φ ≫ (ofCell w).map) (by ext; rfl)
  · exact (congrArg (fun φ => realize.map φ ≫ (ofCell w).map) (by ext; rfl :
      RDCpx.ofInclusion (P := (ofCell w).shape.rdc) (Q := (ofCell w).shape.rdc) (𝟙 _) = 𝟙 _)).trans
      ((congrArg (· ≫ (ofCell w).map) (realize.map_id _)).trans (Category.id_comp _))
  · rw [image_principalEmb, map_top_of_isIso]
    exact W.Iic_top

theorem isDegenerate_cellAt_of_isDegenerate {Y : DiagSet.{u}} {v : PastingDiagram Y}
    (hv : v.IsDegenerate) {t : v.shape.ogp} (ht : grade ℕ t = v.dim) :
    IsDegenerate Y (v.cellAt t) := by
  classical
  obtain ⟨⟨Q, p, w, hs, hd, hm⟩⟩ := hv
  have : FinEnum Q.obj.toOGP :=
    FinEnum.ofSurjective (β := v.shape.ogp) (ConcreteCategory.hom p.hom) hs
  let q : principalAtomRDC v.shape.rdc t ⟶ principalAtomRDC Q (ConcreteCategory.hom p.hom t) :=
    principalLiftRDC Q _ (principalInclusionRDC v.shape.rdc t ≫ p)
      (principalInclusionRDC_comp_mem_closure p t)
  refine ⟨_, q, w.app (op _) ⟨principalInclusionRDC Q (ConcreteCategory.hom p.hom t)⟩,
    isCollapseHom_principalLiftRDC p t, fun hiso => ?_, ?_⟩
  · have hinv : IsCollapseHom (CategoryTheory.inv q) := fun z =>
      ⟨q z, ConcreteCategory.congr_hom (CategoryTheory.IsIso.hom_inv_id q) z⟩
    have h₁ := (dimension_le_of_isCollapseHom (CategoryTheory.inv q) hinv).trans_eq
      (dimension_principalAtomRDC Q (ConcreteCategory.hom p.hom t))
    rw [dimension_principalAtomRDC, ht] at h₁
    have h₂ : ((v.dim : ℕ) : WithBot ℕ∞) ≤ Order.krullDim Q.obj.toOGP :=
      (Nat.cast_le.2 h₁).trans (Order.grade_le_krullDim _)
    exact absurd hd (not_lt.2 h₂)
  · refine (app_eq_map_principalLiftRDC w _ _ _).symm.trans ?_
    exact (congrArg (fun φ => φ.app (op _) ⟨principalInclusionRDC v.shape.rdc t⟩) hm)

theorem topMarked_of_isDegenerate {v : PastingDiagram X.underlying} (hv : v.IsDegenerate) :
    TopMarked X v := fun _ ht =>
  X.mem_marked_of_isDegenerate (isDegenerate_cellAt_of_isDegenerate hv ht)

private theorem equiv_compositorHornMap_app (p : RoundPastingDiagram X.underlying) (hp : 0 < p.dim)
    (t : p.shape.ogp) {a : (toMergerAtom p.roundShape hp).ogp}
    (ha : a ∈ (compositorTopMarkedHorn p.roundShape hp).hornSet)
    (hat : toMergerInputIncl p.roundShape hp t = a) :
    (ofCell ((compositorHornMap p.roundShape hp p.map).app (op _)
      ⟨principalInclusionIn (compositorTopMarkedHorn p.roundShape hp).atom
        (compositorTopMarkedHorn p.roundShape hp).hornSet ha⟩)).Equiv (ofCell (p.cellAt t)) := by
  have hp' : 0 < p.roundShape.dimension := hp
  have hmem : ∀ s, Atom.closureInclOGP (toMergerAtom p.roundShape hp') a s ∈
      (compositorMarkedHorn p.roundShape hp').hornSet := fun s =>
    (compositorMarkedHorn p.roundShape hp').hornSet.lower (closureIncl_mem_closure _ a s) ha
  let f : (Atom.ofClosure (toMergerAtom p.roundShape hp') a).rdc.obj.toOGP ⟶
      p.shape.rdc.obj.toOGP :=
    codRestrict (Atom.closureInclOGP (toMergerAtom p.roundShape hp') a)
      (compositorMarkedHorn p.roundShape hp').hornSet hmem ≫
        (compositorHornIso p.roundShape hp').inv
  have hf : IsInclusion f := ⟨fun _ _ e => IsInclusion.injective
    (f := Atom.closureInclOGP (toMergerAtom p.roundShape hp') a)
    (congrArg Subtype.val
      (IsInclusion.injective (f := (compositorHornIso p.roundShape hp').inv) e) :)⟩
  have hinc : (compositorHornIso p.roundShape hp').hom ≫
      incl (compositorMarkedHorn p.roundShape hp').hornSet =
      toMergerInputIncl p.roundShape hp' := by
    ext; rfl
  refine @equiv_of_emb_of_image_eq _ (ofCell _) (ofCell (p.cellAt t)) p.shape.rdc p.map f
    (p.principalEmb t) hf _ ?_ ?_ ?_
  · refine (congrArg (fun φ => realize.map φ ≫ p.map) (by ext; rfl :
      RDCpx.ofInclusion (P := (Atom.ofClosure (toMergerAtom p.roundShape hp') a).rdc)
        (Q := p.shape.rdc) f =
        principalInclusionIn (compositorTopMarkedHorn p.roundShape hp').atom
          (compositorTopMarkedHorn p.roundShape hp').hornSet ha ≫
          (RDCpx.isoOfIso (P := (compositorMarkedHorn p.roundShape hp').hornRDC)
            (Q := p.roundShape.rdc)
            (compositorHornIso p.roundShape hp').symm).hom)).trans ?_
    exact ((realize.map_comp_assoc _ _ _).trans rfl).trans (ofCell_app_realize _ _).symm
  · rw [ofCell_cellAt_map]
    exact congrArg (fun φ => realize.map φ ≫ p.map) (by ext; rfl)
  · refine map_injective (f := toMergerInputIncl p.roundShape hp') ?_
    have h₁ : f ≫ toMergerInputIncl p.roundShape hp' =
        Atom.closureInclOGP (toMergerAtom p.roundShape hp') a := by
      ext x
      exact (congrArg (fun φ : p.roundShape.ogp ⟶ (toMergerAtom p.roundShape hp').ogp =>
        ConcreteCategory.hom φ ((compositorHornIso p.roundShape hp').inv
        (codRestrict _ _ hmem x))) hinc).symm.trans
        (congrArg Subtype.val (Iso.inv_hom_id_apply (compositorHornIso p.roundShape hp') _))
    refine (map_comp f _ ⊤).symm.trans ((congrArg (map · ⊤) h₁).trans ?_)
    rw [Atom.map_closureInclOGP_top, image_principalEmb]
    exact (congrArg LowerSet.Iic hat.symm).trans (map_Iic _ _).symm

theorem exists_mem_marked_compress (hH : HasMarkedRLP markedHorns X)
    (p : RoundPastingDiagram X.underlying) (hp : 0 < p.dim)
    (htop : TopMarked X p.toPastingDiagram) :
    ∃ c : diagram X.underlying (mergerAtom p.roundShape hp), c ∈ X.marked _ ∧
      ∀ β, ((ofCell c).boundary (p.dim - 1) β).Equiv (p.boundary (p.dim - 1) β) := by
  have hp' : 0 < p.roundShape.dimension := hp
  have hd : p.roundShape.dimension = p.roundShape.dimension - 1 + 1 := (Nat.sub_add_cancel hp).symm
  have hw : (compositorTopMarkedHorn p.roundShape hp').MarksHorn X
      (compositorHornMap p.roundShape hp' p.map) := by
    intro a ha
    have ha₁ := ha.1
    rw [hornSet_compositorFace] at ha₁
    obtain ⟨t, -, hat⟩ := ha₁
    have hgt : grade ℕ t = p.roundShape.dimension :=
      ((isMorphism (toMergerInputIncl p.roundShape hp')).grade_eq t).symm.trans
        ((congrArg (grade ℕ) hat).trans ha.2)
    exact (mem_marked_iff_of_equiv_ofCell (equiv_compositorHornMap_app p hp t ha.1 hat)).2
      (htop t hgt)
  obtain ⟨z₀, hz, -, hzf⟩ := hasMarkedRLP_markedHorns_iff_fills.1 hH _ _ hw
  let z : diagram X.underlying (toMergerAtom p.roundShape hp') := z₀
  let outIncl : (mergerAtom p.roundShape hp').ogp ⟶ (toMergerAtom p.roundShape hp').ogp :=
    p.roundShape.outputIncl hd
  have : IsInclusion outIncl := inferInstanceAs (IsInclusion (p.roundShape.outputIncl hd))
  let g : mergerAtom p.roundShape hp' ⟶ toMergerAtom p.roundShape hp' := Atom.ofInclusion outIncl
  obtain ⟨e, he⟩ := exists_iso_comp_closureIncl g (a := compositorFace p.roundShape hp') (by
      have h := congrArg SetLike.coe ((p.roundShape.map_outputIncl hd).trans
        (closure_compositorFace p.roundShape hp').symm)
      rw [coe_map, LowerSet.coe_top, Set.image_univ] at h
      exact h.trans (LowerSet.coe_Iic _))
    ((mergerAtom p.roundShape hp').dimension_eq.trans ((isMorphism outIncl).grade_eq _).symm)
  have hc : X.underlying.map g.op z ∈ X.marked _ := by
    rw [← he, op_comp]
    exact (congrArg (· ∈ X.marked _) (Functor.map_comp_apply X.underlying _ _ z)).mpr
      ((X.transport e _).1 (hzf (faces_compositorTopMarkedHorn_subset_marking _ hp')))
  refine ⟨_, hc, fun β => ?_⟩
  let inIncl : p.shape.ogp ⟶ (toMergerAtom p.roundShape hp').ogp :=
    toMergerInputIncl p.roundShape hp'
  have : IsInclusion inIncl := inferInstanceAs (IsInclusion (toMergerInputIncl p.roundShape hp'))
  have hin : realize.map (RDCpx.ofInclusion (P := p.shape.rdc)
      (Q := (toMergerAtom p.roundShape hp').rdc) inIncl) ≫ (ofCell z).map = p.map := by
    have hcomp : RDCpx.ofInclusion (P := p.roundShape.rdc)
        (Q := (compositorMarkedHorn p.roundShape hp').hornRDC)
        (codRestrict (toMergerInputIncl p.roundShape hp')
          (compositorMarkedHorn p.roundShape hp').hornSet
          (inputEmb_mem_horn p.roundShape hp')) ≫ (compositorMarkedHorn p.roundShape hp').hornIncl =
        RDCpx.ofInclusion (P := p.roundShape.rdc)
          (Q := atomToRDCpx.obj (toMergerAtom p.roundShape hp'))
          (toMergerInputIncl p.roundShape hp') := by
      ext x
      rfl
    exact (congrArg (fun t => realize.map t ≫ (ofCell z).map) hcomp.symm).trans
      ((realize.map_comp_assoc _ _ _).trans ((congrArg (realize.map _ ≫ ·) hz).trans
        ((realize.map_comp_assoc _ _ _).symm.trans
          ((congrArg (fun t => realize.map t ≫ p.map)
            (inputEmb_comp_compositorHornIso p.roundShape hp')).trans
            ((congrArg (· ≫ p.map) (realize.map_id _)).trans (Category.id_comp _))))))
  have hsrc : ((ofCell z).boundary p.dim false).Equiv p.toPastingDiagram :=
    equiv_of_emb_of_image_eq (a := (ofCell z).boundary p.dim false) (b := p.toPastingDiagram)
      (C := (toMergerAtom p.roundShape hp').toMoleculeShape.rdc) (ofCell z).map
      ((toMergerAtom p.roundShape hp').toMoleculeShape.boundaryIncl p.dim false) inIncl
      (boundary_comm (ofCell z) _ _) hin
      ((MoleculeShape.map_boundaryIncl_top _ _ _).trans
        ((bdry_toMergerAtom p.roundShape hp' false).symm.trans
        (p.roundShape.map_inputIncl hd).symm))
  have htgt : ((ofCell z).boundary p.dim true).Equiv (ofCell (X.underlying.map g.op z)) :=
    equiv_of_emb_of_image_eq (a := (ofCell z).boundary p.dim true)
      (b := ofCell (X.underlying.map g.op z))
      (C := (toMergerAtom p.roundShape hp').toMoleculeShape.rdc) (ofCell z).map
      ((toMergerAtom p.roundShape hp').toMoleculeShape.boundaryIncl p.dim true) outIncl
      (boundary_comm (ofCell z) _ _) (ofCell_map_op_map g z).symm
      ((MoleculeShape.map_boundaryIncl_top _ _ _).trans
        ((bdry_toMergerAtom p.roundShape hp' true).symm.trans
        (p.roundShape.map_outputIncl hd).symm))
  have hk : p.dim - 1 < p.dim := by omega
  exact ((htgt.boundary _ β).symm.trans (equiv_boundary_boundary _ hk true β)).trans
    ((equiv_boundary_boundary _ hk false β).symm.trans (hsrc.boundary _ β))

private theorem exists_left_invertor (hH : HasMarkedRLP markedHorns X) {V : Atom}
    (hV : 0 < V.dimension) {a b : diagram X.underlying V} {W : Atom} {w : diagram X.underlying W}
    (hw : w ∈ X.marked W) (hab : HasRoundType (ofCell w) (cellRound a) (cellRound b))
    (bL : RoundPastingDiagram X.underlying) (hbL : bL.dim = V.dimension)
    (hpa : (ofCell a).Pastable bL.toPastingDiagram (V.dimension - 1))
    (hpb : (ofCell b).Pastable bL.toPastingDiagram (V.dimension - 1)) {Z : Atom}
    {l : diagram X.underlying Z} (hl : l ∈ X.marked Z) (hZ : Z.dimension = V.dimension + 1)
    (hls : ((ofCell l).boundary V.dimension false).Equiv
      ((ofCell b).paste bL.toPastingDiagram (V.dimension - 1) hpb))
    (hlt : ((ofCell l).boundary V.dimension true).Equiv
      ((ofCell b).boundary (V.dimension - 1) false).unit) :
    ∃ (Q : Atom) (c : diagram X.underlying Q), c ∈ X.marked Q ∧
      Q.dimension = V.dimension + 1 ∧
      ((ofCell c).boundary V.dimension false).Equiv
        ((ofCell a).paste bL.toPastingDiagram (V.dimension - 1) hpa) ∧
      ((ofCell c).boundary V.dimension true).Equiv
        ((ofCell b).boundary (V.dimension - 1) false).unit := by
  have hd : V.dimension = V.dimension - 1 + 1 := by omega
  have hr := isRound_paste_of_round false (u := ofCell a) (x := bL.toPastingDiagram) hpa
    V.isAtom.isRound hd (by omega)
  let E : EquivalenceData (cellRound a) (cellRound b) :=
    ⟨rfl, cellRound w, marked_subset_equivalences X hH W w hw, hab.dim_eq, hab.source, hab.target⟩
  let D := SubstituteData.ofPaste (c := bL) (h := cellRound a) false hpa hr E.hasBdry hbL
  have hn : (pasteRound hpa hr).dim = V.dimension :=
    dim_paste_of_dim_eq (c := bL) (h := cellRound a) false hpa hbL
  have hTs := D.equiv_source
  have hTt := SubstituteData.equiv_target_ofPaste (c := bL) (h := cellRound a) false hpa hr
    E.hasBdry hbL hpb
  have hTm : TopMarked X D.pasteData.pasting := D.pasteData.topMarked (topMarked_ofCell hw)
    (topMarked_of_isDegenerate (isDegenerate_unit _))
  replace hTs := (PastingDiagram.equiv_of_eq (boundary_congr _ hn false).symm).trans hTs
  replace hTt := (PastingDiagram.equiv_of_eq (boundary_congr _ hn true).symm).trans hTt
  have hTd : D.pasteData.round.dim = V.dimension + 1 := D.pasteData.dim_pasting.trans
    (congrArg (· + 1) hn)
  let P := PasteAtData.ofBoundary (α := false) (e := D.pasteData.round) (u' := cellRound l)
    (n := V.dimension) hTd hZ (hTt.trans hls.symm)
  have hPm : TopMarked X P.pasting := P.topMarked hTm (topMarked_ofCell hl)
  have hPd : P.round.dim = V.dimension + 1 := P.dim_pasting
  obtain ⟨c, hc, hcb⟩ := exists_mem_marked_compress hH P.round (by omega) hPm
  have hidx : P.round.dim - 1 = V.dimension := by rw [hPd]; rfl
  have hcb' (β : Bool) :
      ((ofCell c).boundary V.dimension β).Equiv (P.pasting.boundary V.dimension β) :=
    (PastingDiagram.equiv_of_eq (boundary_congr _ hidx β).symm).trans
      ((hcb β).trans (PastingDiagram.equiv_of_eq (boundary_congr _ hidx β)))
  refine ⟨_, c, hc, (dimension_mergerAtom _ _).trans hPd, ?_, ?_⟩
  · exact ((hcb' false).trans (P.equiv_boundary_pasting_of_image_univ (Within.image_refl _))).trans
      hTs
  · exact ((hcb' true).trans P.equiv_boundary_not).trans hlt

private theorem exists_right_invertor (hH : HasMarkedRLP markedHorns X) {V : Atom}
    (hV : 0 < V.dimension) {a b : diagram X.underlying V} {W : Atom} {w : diagram X.underlying W}
    (hw : w ∈ X.marked W) (hba : HasRoundType (ofCell w) (cellRound b) (cellRound a))
    (bR : RoundPastingDiagram X.underlying) (hbR : bR.dim = V.dimension)
    (hpa : bR.toPastingDiagram.Pastable (ofCell a) (V.dimension - 1))
    (hpb : bR.toPastingDiagram.Pastable (ofCell b) (V.dimension - 1)) {Z : Atom}
    {r : diagram X.underlying Z} (hrm : r ∈ X.marked Z) (hZ : Z.dimension = V.dimension + 1)
    (hrs : ((ofCell r).boundary V.dimension false).Equiv
      ((ofCell b).boundary (V.dimension - 1) true).unit)
    (hrt : ((ofCell r).boundary V.dimension true).Equiv
      (bR.toPastingDiagram.paste (ofCell b) (V.dimension - 1) hpb)) :
    ∃ (Q : Atom) (c : diagram X.underlying Q), c ∈ X.marked Q ∧
      Q.dimension = V.dimension + 1 ∧
      ((ofCell c).boundary V.dimension false).Equiv
        ((ofCell b).boundary (V.dimension - 1) true).unit ∧
      ((ofCell c).boundary V.dimension true).Equiv
        (bR.toPastingDiagram.paste (ofCell a) (V.dimension - 1) hpa) := by
  have hd : V.dimension = V.dimension - 1 + 1 := by omega
  have hr := isRound_paste_of_round true (u := ofCell b) (x := bR.toPastingDiagram) hpb
    V.isAtom.isRound hd (by omega)
  let E : EquivalenceData (cellRound b) (cellRound a) :=
    ⟨rfl, cellRound w, marked_subset_equivalences X hH W w hw, hba.dim_eq, hba.source, hba.target⟩
  let D := SubstituteData.ofPaste (c := bR) (h := cellRound b) true hpb hr E.hasBdry hbR
  have hn : (pasteRound hpb hr).dim = V.dimension :=
    dim_paste_of_dim_eq (c := bR) (h := cellRound b) true hpb hbR
  have hTs := D.equiv_source
  have hTt := SubstituteData.equiv_target_ofPaste (c := bR) (h := cellRound b) true hpb hr
    E.hasBdry hbR hpa
  have hTm : TopMarked X D.pasteData.pasting := D.pasteData.topMarked (topMarked_ofCell hw)
    (topMarked_of_isDegenerate (isDegenerate_unit _))
  replace hTs := (PastingDiagram.equiv_of_eq (boundary_congr _ hn false).symm).trans hTs
  replace hTt := (PastingDiagram.equiv_of_eq (boundary_congr _ hn true).symm).trans hTt
  have hTd : D.pasteData.round.dim = V.dimension + 1 := D.pasteData.dim_pasting.trans
    (congrArg (· + 1) hn)
  let P := PasteAtData.ofBoundary (α := false) (e := cellRound r) (u' := D.pasteData.round)
    (n := V.dimension) hZ hTd (hrt.trans hTs.symm)
  have hPm : TopMarked X P.pasting := P.topMarked (topMarked_ofCell hrm) hTm
  have hPd : P.round.dim = V.dimension + 1 := P.dim_pasting
  obtain ⟨c, hc, hcb⟩ := exists_mem_marked_compress hH P.round (by omega) hPm
  have hidx : P.round.dim - 1 = V.dimension := by rw [hPd]; rfl
  have hcb' (β : Bool) :
      ((ofCell c).boundary V.dimension β).Equiv (P.pasting.boundary V.dimension β) :=
    (PastingDiagram.equiv_of_eq (boundary_congr _ hidx β).symm).trans
      ((hcb β).trans (PastingDiagram.equiv_of_eq (boundary_congr _ hidx β)))
  refine ⟨_, c, hc, (dimension_mergerAtom _ _).trans hPd, ?_, ?_⟩
  · exact ((hcb' false).trans (P.equiv_boundary_pasting_of_image_univ (Within.image_refl _))).trans
      hrs
  · exact ((hcb' true).trans P.equiv_boundary_not).trans hTt

theorem mem_marked_of_marked_comparison (hH : HasMarkedRLP markedHorns X)
    (hI : HasMarkedRLP invertorGenerators X) {V : Atom} {a b : diagram X.underlying V}
    (hb : b ∈ X.marked V) {W W' : Atom} {w : diagram X.underlying W}
    {w' : diagram X.underlying W'} (hw : w ∈ X.marked W) (hw' : w' ∈ X.marked W')
    (hab : HasRoundType (ofCell w) (cellRound a) (cellRound b))
    (hba : HasRoundType (ofCell w') (cellRound b) (cellRound a)) : a ∈ X.marked V := by
  have hV : 0 < V.dimension := X.markable V b hb
  have hk : V.dimension - 1 < V.dimension := by omega
  choose zb hzb hzbm using fun α => exists_fills_of_hasLiftingProperty
    (invertorMarkedHorn V (!α) hV) (hH _ (MorphismProperty.ofHoms.mk _))
    (invertorHornMap (!α) hV b) (marksHorn_invertorHornMap (!α) hV b hb)
  obtain ⟨db, hdb⟩ := exists_biInvData_of_invertors hV b zb hzb
  have hpar (γ : Bool) : ((ofCell a).boundary (V.dimension - 1) γ).Equiv
      ((ofCell b).boundary (V.dimension - 1) γ) :=
    ((hab.source.boundary _ γ).symm.trans (equiv_boundary_boundary _ hk false γ)).trans
      ((equiv_boundary_boundary _ hk true γ).symm.trans (hab.target.boundary _ γ))
  have hdz (α : Bool) : (invertorAtom V (!α) hV).dimension = V.dimension + 1 :=
    (dim_eq_of_equiv (hdb α).2).trans (db.dim_invertor α)
  have hpa : (ofCell a).Pastable (db.inverse false).toPastingDiagram (V.dimension - 1) :=
    ⟨(hpar true).trans (db.pastable false).1, (db.pastable false).2⟩
  have hpa' : (db.inverse true).toPastingDiagram.Pastable (ofCell a) (V.dimension - 1) :=
    ⟨(db.pastable true).1.trans (hpar false).symm, (db.pastable true).2⟩
  obtain ⟨QL, cL, hcL, hdL, hcLs, hcLt⟩ := exists_left_invertor hH hV hw hab (db.inverse false)
    (db.dim_inverse false) hpa (db.pastable false) (hzbm false).1 (hdz false)
    (((hdb false).2.boundary _ false).trans (db.boundary_invertor_composite false))
    (((hdb false).2.boundary _ true).trans (db.boundary_invertor_unit false))
  obtain ⟨QR, cR, hcR, hdR, hcRs, hcRt⟩ := exists_right_invertor hH hV hw' hba (db.inverse true)
    (db.dim_inverse true) hpa' (db.pastable true) (hzbm true).1 (hdz true)
    (((hdb true).2.boundary _ false).trans (db.boundary_invertor_unit true))
    (((hdb true).2.boundary _ true).trans (db.boundary_invertor_composite true))
  let da : BiInvData Set.univ (cellRound a) :=
    { dim_pos := hV
      inverse := db.inverse
      invertor := fun α => cond α (cellRound cR) (cellRound cL)
      invertor_mem := fun _ => Set.mem_univ _
      dim_inverse := db.dim_inverse
      dim_invertor := fun α => by cases α; exacts [hdL, hdR]
      equiv_boundary_inverse := fun α γ => (db.equiv_boundary_inverse α γ).trans (hpar (!γ)).symm
      pastable := fun α => by cases α; exacts [hpa, hpa']
      boundary_invertor_composite := fun α => by cases α; exacts [hcLs, hcRt]
      boundary_invertor_unit := fun α => by
        cases α
        exacts [hcLt.trans (hpar false).symm.unit, hcRs.trans (hpar true).symm.unit] }
  let A := topInversionData V hV
  let f : ball.{u} V ⟶ X.underlying := uliftYonedaEquiv.symm a
  have hf : f.app (op V) ⟨𝟙 V⟩ = a :=
    (uliftYonedaEquiv_apply _).symm.trans (uliftYonedaEquiv.apply_symm_apply a)
  let L : A.ι × Bool → Σ H : Atom, diagram X.underlying H := fun j =>
    ⟨_, X.underlying.map (Atom.closureIncl (invertorAtom V (!j.2) hV)
      (invertorTopElt V (!j.2) hV (some (!j.2)))).op (zb j.2)⟩
  let Z : A.ι × Bool → Σ H : Atom, diagram X.underlying H := fun j => cond j.2 ⟨_, cR⟩ ⟨_, cL⟩
  have hZ (j : A.ι × Bool) : (Z j).2 ∈ X.marked (Z j).1 := by
    obtain ⟨-, β⟩ := j
    cases β
    exacts [hcL, hcR]
  have hLZ : A.Inverts f L Z := fun _ => ⟨cellRound a, da,
    PastingDiagram.equiv_of_eq (congrArg ofCell hf.symm),
    fun α => ⟨(hdb α).1, by cases α <;> exact .refl _⟩⟩
  let φ := A.stepDesc f L Z hLZ
  let q : MarkedDiagSet.markedAbove (invertorPair V hV) V.dimension ⟶ X :=
    Homotopical.MarkedPresheaf.homMk φ fun V' y hy => by
      rcases (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ V' _).1 hy with hy | hdim
      · exact X.mem_marked_of_isDegenerate (isDegenerate_app φ hy)
      rcases isDegenerate_or_isIso_invertorPair V hV hdim.le y with
        h | ⟨g, hg, rfl⟩ | ⟨j, g, hg, rfl⟩ | ⟨j, g, hg, rfl⟩
      · exact X.mem_marked_of_isDegenerate (isDegenerate_app φ h)
      · exact absurd (Atom.dimension_eq_of_iso (asIso g)) hdim.ne'
      · exact absurd ((Atom.dimension_eq_of_iso (asIso g)).trans
          (A.dimension_inverseExtension_shape j)) hdim.ne'
      · obtain ⟨e⟩ := A.nonempty_iso_next_stepDesc f L Z hLZ j
        refine (congrArg (· ∈ X.marked _) (NatTrans.naturality_apply φ g.op _)).mpr ?_
        refine (X.transport (asIso g) _).1 ?_
        exact (congrArg (· ∈ X.marked _) (A.stepDesc_app_next f L Z hLZ j e)).mpr
          ((X.transport e _).1 (hZ j))
  obtain ⟨F, hF⟩ := hasMarkedRLP_iff.1 hI _
    (MorphismProperty.ofHoms.mk (⟨V, hV⟩ : {U : Atom // 0 < U.dimension})) q
  have hFq : Homotopical.MarkedPresheaf.forget.map F = φ :=
    (Category.id_comp _).symm.trans ((Homotopical.MarkedPresheaf.forget.map_comp _ _).symm.trans
      (congrArg Homotopical.MarkedPresheaf.forget.map hF))
  have hu : (toInvertorPair V hV).app (op V) ⟨𝟙 V⟩ ∈
      (MarkedDiagSet.markedAbove (invertorPair V hV) (V.dimension - 1)).marked V :=
    (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr (by omega))
  have hm := Homotopical.MarkedPresheaf.map_mem_marked F hu
  rw [hFq] at hm
  have hval : φ.app (op V) ((toInvertorPair V hV).app (op V) ⟨𝟙 V⟩) = a :=
    (congrArg (fun ψ => ψ.app (op V) ⟨𝟙 V⟩) (A.stepIncl_stepDesc f L Z hLZ)).trans hf
  exact (congrArg (· ∈ X.marked V) hval).mp hm

end Atoms.Diagrammatic
