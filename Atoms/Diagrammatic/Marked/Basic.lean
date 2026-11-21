import Atoms.Diagrammatic.Equivalence.Degenerate
import Atoms.Homotopical.Marked.Basic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem dimension_pos_of_isDegenerate {U : Atom} {x : diagram X U} (hx : IsDegenerate X x) :
    0 < U.dimension := by
  obtain ⟨V, p, _, hp, hni, _⟩ := hx
  refine Nat.pos_of_ne_zero fun h0 => hni ?_
  have hV := dimension_le_of_isCollapseHom p hp
  exact isIso_of_isCollapseHom_of_dimension_eq p hp (by omega)

theorem isDegenerate_app (f : X ⟶ Y) {U : Atom} {x : diagram X U} (hx : IsDegenerate X x) :
    IsDegenerate Y (f.app (op U) x) := by
  obtain ⟨V, p, y, hp, hni, rfl⟩ := hx
  exact ⟨V, p, f.app (op V) y, hp, hni, (NatTrans.naturality_apply f p.op y).symm⟩

theorem isDegenerate_map_iso_iff {U V : Atom} (e : U ≅ V) (x : diagram X V) :
    IsDegenerate X (X.map e.hom.op x) ↔ IsDegenerate X x := by
  constructor
  · rintro ⟨W, p, y, hp, hni, hy⟩
    refine ⟨W, e.inv ≫ p, y, ?_, fun h => hni ?_, ?_⟩
    · exact collapses.comp_mem _ _ (isCollapseHom_of_iso e.symm) hp
    · have : p = e.hom ≫ (e.inv ≫ p) := by simp
      rw [this]
      infer_instance
    · have hx : X.map (e.inv ≫ e.hom).op x = x := by
        rw [e.inv_hom_id, op_id]
        exact Functor.map_id_apply X _ x
      refine Eq.trans ?_ hx
      calc X.map (e.inv ≫ p).op y = X.map e.inv.op (X.map p.op y) :=
            Functor.map_comp_apply X p.op e.inv.op y
        _ = X.map e.inv.op (X.map e.hom.op x) := congrArg (X.map e.inv.op) hy
        _ = X.map (e.inv ≫ e.hom).op x := (Functor.map_comp_apply X e.hom.op e.inv.op x).symm
  · rintro ⟨W, p, y, hp, hni, rfl⟩
    refine ⟨W, e.hom ≫ p, y, ?_, fun h => hni ?_, ?_⟩
    · exact collapses.comp_mem _ _ (isCollapseHom_of_iso e) hp
    · have : p = e.inv ≫ (e.hom ≫ p) := by simp
      rw [this]
      infer_instance
    · exact Functor.map_comp_apply X p.op e.hom.op y

def degeneracies : MorphismProperty Atom := fun _ _ p => IsCollapseHom p ∧ ¬ IsIso p

instance : degeneracies.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e ⟨hf, hni⟩ =>
    ⟨(collapses.arrow_mk_iso_iff e).1 hf, fun h =>
      hni (((MorphismProperty.isomorphisms Atom).arrow_mk_iso_iff e).2 h)⟩

def atomMarking : Homotopical.MarkingData Atom where
  markable U := 0 < U.dimension
  degeneracy := degeneracies
  markable_of_degeneracy U V p hp := by
    refine Nat.pos_of_ne_zero fun h0 => hp.2 ?_
    have hV := dimension_le_of_isCollapseHom p hp.1
    exact isIso_of_isCollapseHom_of_dimension_eq p hp.1 (by omega)
  markable_of_iso _ _ e h := (Atom.dimension_eq_of_iso e).symm ▸ h

abbrev MarkedDiagSet : Type (u + 1) := Homotopical.MarkedPresheaf.{u} atomMarking

namespace MarkedDiagSet

theorem mem_marked_of_isDegenerate (X : MarkedDiagSet.{u}) {U : Atom} {x : diagram X.underlying U}
    (h : IsDegenerate X.underlying x) : x ∈ X.marked U := by
  obtain ⟨V, p, y, hp, hni, rfl⟩ := h
  exact X.degenerate p ⟨hp, hni⟩ y

@[simp] theorem mem_marked_flat_iff_isDegenerate (X : DiagSet.{u}) (U : Atom) (x : diagram X U) :
    x ∈ ((Homotopical.MarkedPresheaf.flat atomMarking).obj X).marked U ↔ IsDegenerate X x := by
  refine (Homotopical.MarkedPresheaf.mem_marked_flat atomMarking X U x).trans ⟨?_, ?_⟩
  · rintro ⟨V, p, ⟨hp, hni⟩, y, rfl⟩
    exact ⟨V, p, y, hp, hni, rfl⟩
  · rintro ⟨V, p, y, hp, hni, rfl⟩
    exact ⟨V, p, ⟨hp, hni⟩, y, rfl⟩

def naturalMarking (X : DiagSet.{u}) : Homotopical.MarkedPresheaf.Marking atomMarking X where
  marked U := {x : diagram X U | IsEquivalence X x}
  markable _ x h := Nat.pos_of_ne_zero fun h0 => not_isEquivalence_of_dimension_eq_zero x h0 h
  degenerate _ b p hp y := degenerate_isEquivalence X _ ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport _ _ e x := (isEquivalence_map_iso_iff e x).symm

noncomputable def natural : DiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj X := Homotopical.MarkedPresheaf.ofMarking X (naturalMarking X)
  map {X _} f := Homotopical.MarkedPresheaf.homMk
    (X := Homotopical.MarkedPresheaf.ofMarking X (naturalMarking X)) f fun U _ hx =>
      (Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ U _).2 (IsEquivalence.map f
        ((Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ U _).1 hx))
  map_id _ := Homotopical.MarkedPresheaf.hom_ext rfl
  map_comp _ _ := Homotopical.MarkedPresheaf.hom_ext rfl

@[simp] theorem mem_marked_natural_iff (X : DiagSet.{u}) (U : Atom) (x : diagram X U) :
    x ∈ (natural.obj X).marked U ↔ IsEquivalence X x :=
  Homotopical.MarkedPresheaf.mem_marked_ofMarking _ _ _ _

theorem natural_comp_forget : natural ⋙ Homotopical.MarkedPresheaf.forget = 𝟭 DiagSet.{u} := rfl

noncomputable def naturalToSharp (X : DiagSet.{u}) :
    natural.obj X ⟶ (Homotopical.MarkedPresheaf.sharp atomMarking).obj X :=
  ((Homotopical.MarkedPresheaf.forgetSharpAdjunction atomMarking).homEquiv _ _ (𝟙 X))

end MarkedDiagSet

def HasMarkedRLP (J : MorphismProperty MarkedDiagSet.{u}) (X : MarkedDiagSet.{u}) : Prop :=
  J.rlp (terminal.from X)

theorem hasMarkedRLP_iff {J : MorphismProperty MarkedDiagSet.{u}} {X : MarkedDiagSet.{u}} :
    HasMarkedRLP J X ↔ ∀ ⦃A B : MarkedDiagSet.{u}⦄ (i : A ⟶ B), J i → ∀ q : A ⟶ X,
      ∃ f : B ⟶ X, i ≫ f = q := by
  constructor
  · intro h A B i hi q
    have := h i hi
    have sq : CommSq q i (terminal.from X) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h A B i hi
    refine ⟨fun {u _} _ => ?_⟩
    obtain ⟨f, hf⟩ := h i hi u
    exact CommSq.HasLift.mk' ⟨f, hf, terminal.hom_ext _ _⟩

theorem hasMarkedRLP_sup (J K : MorphismProperty MarkedDiagSet.{u}) (X : MarkedDiagSet.{u}) :
    HasMarkedRLP (J ⊔ K) X ↔ HasMarkedRLP J X ∧ HasMarkedRLP K X := by
  rw [HasMarkedRLP, HasMarkedRLP, HasMarkedRLP,
    show (J ⊔ K).rlp = J.rlp ⊓ K.rlp from MorphismProperty.gc_llp_rlp.u_inf]
  rfl

end Atoms.Diagrammatic
