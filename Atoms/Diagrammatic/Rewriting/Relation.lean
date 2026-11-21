import Atoms.Diagrammatic.Rewriting.FullRound

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered

namespace Signature

variable (S : Signature.{v}) [DecidableEq S.Pt] [DecidableEq S.Ed]

def RoundSide (d : Diagram S.Pt S.Ed S.Ce) : Prop :=
  d.layers = [] ∨ d.layers.head?.map (fun l => (S.cellType l.1).1) = some d.source ∨
    d.layers.getLast?.map (fun l => (S.cellType l.1).2) = S.target d

instance : DecidablePred S.RoundSide :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

variable {S} {X : DiagSet.{u}}

theorem Interp.isRound_diagram_of_roundSide (I : S.Interp X) (hS : S.WellFormed)
    {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q)
    (hsrc : d.source ≠ []) (h : S.RoundSide d) : (I.diagram d hsrc).IsRound := by
  rcases h with hl | hl | hl
  · exact I.isRound_diagram_of_layers_eq_nil (S.isPath_source_of_target hd) hl
  · cases hd' : d.layers with
    | nil => exact I.isRound_diagram_of_layers_eq_nil (S.isPath_source_of_target hd) hd'
    | cons l ls =>
      rw [hd'] at hl
      exact I.isRound_diagram_of_first hS hd hsrc hd' (Option.some.inj hl)
  · obtain ⟨l, hlast⟩ : ∃ l, d.layers.getLast? = some l := by
      cases h' : d.layers.getLast? with
      | none => rw [h', Option.map_none, hd] at hl; exact absurd hl (by simp)
      | some l => exact ⟨l, rfl⟩
    obtain ⟨ls, hls⟩ := List.getLast?_eq_some_iff.1 hlast
    rw [hlast, Option.map_some, hd] at hl
    exact I.isRound_diagram_of_last hS hd hsrc hls (Option.some.inj hl)

theorem Interp.isRound_diagram_of_roundSide_or_fullRound (I : S.Interp X) (hS : S.WellFormed)
    {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q)
    (hsrc : d.source ≠ []) (h : S.RoundSide d ∨ S.FullRound d) : (I.diagram d hsrc).IsRound :=
  h.elim (I.isRound_diagram_of_roundSide hS hd hsrc) (I.isRound_diagram_of_fullRound hS hd hsrc)

end Signature

structure RelSignature extends Signature.{v} where
  Rel : Type v
  relSource : Rel → Diagram Pt Ed Ce
  relTarget : Rel → Diagram Pt Ed Ce
  invertible : Rel → Bool

namespace RelSignature

variable (S : RelSignature.{v}) [DecidableEq S.Pt] [DecidableEq S.Ed]

def side (r : S.Rel) (α : Bool) : Diagram S.Pt S.Ed S.Ce :=
  cond α (S.relTarget r) (S.relSource r)

structure RelWellFormed (r : S.Rel) : Prop where
  source_eq : (S.relSource r).source = (S.relTarget r).source
  isSome_target : (S.target (S.relSource r)).isSome
  target_eq : S.target (S.relSource r) = S.target (S.relTarget r)
  roundSide : ∀ α, S.RoundSide (S.side r α) ∨ S.FullRound (S.side r α)

instance (r : S.Rel) : Decidable (S.RelWellFormed r) :=
  decidable_of_iff ((S.relSource r).source = (S.relTarget r).source ∧
      (S.target (S.relSource r)).isSome ∧ S.target (S.relSource r) = S.target (S.relTarget r) ∧
      (S.RoundSide (S.relSource r) ∨ S.FullRound (S.relSource r)) ∧
      (S.RoundSide (S.relTarget r) ∨ S.FullRound (S.relTarget r)))
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, fun α => by cases α; exacts [h₄, h₅]⟩,
      fun h => ⟨h.1, h.2, h.3, h.4 false, h.4 true⟩⟩

def WellFormed : Prop := S.toSignature.WellFormed ∧ ∀ r, S.RelWellFormed r

instance [Fintype S.Ce] [Fintype S.Rel] : Decidable S.WellFormed :=
  inferInstanceAs (Decidable (S.toSignature.WellFormed ∧ ∀ r, S.RelWellFormed r))

variable {S}

theorem source_side (hS : S.WellFormed) (r : S.Rel) (α : Bool) :
    (S.side r α).source = (S.relSource r).source := by
  cases α
  · rfl
  · exact ((hS.2 r).source_eq).symm

theorem target_side (hS : S.WellFormed) (r : S.Rel) (α : Bool) :
    S.target (S.side r α) = S.target (S.relSource r) := by
  cases α
  · rfl
  · exact ((hS.2 r).target_eq).symm

theorem isPath_source_side (hS : S.WellFormed) (r : S.Rel) :
    S.IsPath (S.relSource r).source := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  exact S.isPath_source_of_target hq

variable {X : DiagSet.{u}}

noncomputable def sideRound (I : S.toSignature.Interp X) (hS : S.WellFormed) (r : S.Rel)
    (α : Bool) : RoundPastingDiagram X :=
  ⟨I.diagram (S.side r α) (by rw [source_side hS]; exact (isPath_source_side hS r).ne_nil),
    by
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
      exact I.isRound_diagram_of_roundSide_or_fullRound hS.1 ((target_side hS r α).trans hq) _
        ((hS.2 r).roundSide α)⟩

theorem hasRoundType_side (I : S.toSignature.Interp X) (hS : S.WellFormed) (r : S.Rel)
    {q : List (Edge S.Pt S.Ed)} (hq : S.target (S.relSource r) = some q) (α : Bool) :
    HasRoundType (sideRound I hS r α).toPastingDiagram
      (I.pathRound _ (isPath_source_side hS r)) (I.pathRound q (S.isPath_target hS.1 hq)) := by
  have h := I.hasRoundType_diagram hS.1 ((target_side hS r α).trans hq)
    (by rw [source_side hS]; exact (isPath_source_side hS r).ne_nil)
  refine h.of_equiv ?_ (.refl _)
  exact PastingDiagram.equiv_of_eq (I.path_congr (source_side hS r α) _ _)

theorem parallel_sideRound (I : S.toSignature.Interp X) (hS : S.WellFormed) (r : S.Rel) :
    Parallel (sideRound I hS r false) (sideRound I hS r true) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  exact HasRoundType.parallel (hasRoundType_side I hS r hq false) (hasRoundType_side I hS r hq true)

variable (S) [DecidableEq S.Ce] in
def relationApply (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (h o : ℕ) :
    Option (Diagram S.Pt S.Ed S.Ce) :=
  match S.targetFrom d.source (d.layers.take h) with
  | none => none
  | some p =>
    if (S.target d).isSome ∧ h + (S.relSource r).layers.length ≤ d.layers.length ∧
        (d.layers.drop h).take (S.relSource r).layers.length =
          (S.relSource r).layers.map (fun l => (l.1, l.2 + o)) ∧
        (p.drop o).take (S.relSource r).source.length = (S.relSource r).source then
      let d' : Diagram S.Pt S.Ed S.Ce := ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩
      if (S.target d').isSome then some d' else none
    else none

variable [DecidableEq S.Ce] in
theorem exists_eq_of_relationApply_eq_some (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce}
    {r : S.Rel} {h o : ℕ} (hd : S.relationApply d r h o = some d') :
    ∃ L R : List (Edge S.Pt S.Ed),
      S.targetFrom d.source (d.layers.take h) = some (L ++ (S.relSource r).source ++ R) ∧
      L.length = o ∧ ∀ β, cond β d' d = ⟨d.source, d.layers.take h ++
        (S.side r β).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ := by
  rw [relationApply] at hd
  split at hd
  · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
  rename_i p hp
  split_ifs at hd with hc₁
  dsimp only at hd
  split_ifs at hd with hc₂
  obtain ⟨-, hlen, hseg, hsseg⟩ := hc₁
  obtain rfl := (Option.some.inj hd).symm
  have hpsrc := isPath_source_side hS r
  have hap : S.applyLayer p (.unit (S.relSource r).source) o = some (p.take o ++
      (S.relSource r).source ++ p.drop (o + (S.relSource r).source.length)) := by
    rw [Signature.applyLayer, if_pos ⟨hpsrc.ne_nil, hsseg⟩]
    rfl
  obtain ⟨-, L, R, hpLR, hL, -⟩ := S.applyLayer_eq_some_iff.1 hap
  refine ⟨L, R, hpLR ▸ hp, hL, fun β => ?_⟩
  cases β
  · have hdl : d.layers = d.layers.take h ++ (S.relSource r).layers.map
        (fun l => (l.1, l.2 + o)) ++ d.layers.drop (h + (S.relSource r).layers.length) := by
      rw [List.append_assoc, ← hseg, ← List.drop_drop, List.take_append_drop,
        List.take_append_drop]
    exact congrArg (Diagram.mk d.source) hdl
  · rfl

variable (S) in
structure Interp (hS : S.WellFormed) (X : DiagSet.{u}) extends S.toSignature.Interp X where
  rel : S.Rel → Σ U : Atom, diagram X U
  hasRoundType_rel : ∀ r, HasRoundType (PastingDiagram.ofCell (rel r).2)
    (sideRound toInterp hS r false) (sideRound toInterp hS r true)

section Presented

variable (S : RelSignature.{u}) [DecidableEq S.Pt] [DecidableEq S.Ed] (hS : S.WellFormed)

private noncomputable def relStage :
    CellularExtensionData (S.toSignature.presented hS.1) where
  ι := S.Rel
  source r := sideRound (S.toSignature.tautInterp hS.1) hS r false
  target r := sideRound (S.toSignature.tautInterp hS.1) hS r true
  parallel r := parallel_sideRound _ hS r

noncomputable def presented : DiagSet.{u} := (relStage S hS).extension

noncomputable def presentation : Presentation (S.presented hS) :=
  (S.toSignature.presentation hS.1).extend (relStage S hS)

noncomputable def tautInterp : S.Interp hS (S.presented hS) where
  toInterp := (S.toSignature.tautInterp hS.1).mapTo (relStage S hS).incl
  rel r := ⟨(relStage S hS).shape r, (relStage S hS).cell r⟩
  hasRoundType_rel r := by
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
    exact ((relStage S hS).hasRoundType_cell r).of_equiv
      ((S.toSignature.tautInterp hS.1).diagram_mapTo hS.1 _ ((target_side hS r false).trans hq)
        _).symm
      ((S.toSignature.tautInterp hS.1).diagram_mapTo hS.1 _ ((target_side hS r true).trans hq)
        _).symm

theorem tautInterp_rel (r : S.Rel) :
    ((S.tautInterp hS).rel r).2 = (S.presentation hS).cell (Sum.inr r) :=
  rfl

end Presented

end RelSignature

end Atoms.Diagrammatic.Layered
