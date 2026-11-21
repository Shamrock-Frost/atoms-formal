import Atoms.Homotopical.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

open CategoryTheory Opposite Simplicial

universe u

namespace Atoms.Homotopical

def edgeMarking : MarkingData SimplexCategory where
  markable n := n.len = 1
  degeneracy := fun m n _ => m.len = 1 ∧ n.len = 0
  respectsIso := MorphismProperty.RespectsIso.mk _
    (fun e _ h => ⟨(SimplexCategory.len_eq_of_isIso e.hom).trans h.1, h.2⟩)
    (fun e _ h => ⟨h.1, (SimplexCategory.len_eq_of_isIso e.hom).symm.trans h.2⟩)
  markable_of_degeneracy _ _ _ h := h.1
  markable_of_iso _ _ e h := (SimplexCategory.len_eq_of_isIso e.hom).trans h

abbrev MarkedSSet : Type (u + 1) := MarkedPresheaf.{u} edgeMarking

theorem edgeMarking_degenerate_iff {n : SimplexCategory} (g : ⦋1⦌ ⟶ n) :
    edgeMarking.Degenerate g ↔ g.toOrderHom 0 = g.toOrderHom 1 := by
  constructor
  · rintro ⟨c, p, q, ⟨-, hc⟩, rfl⟩
    have h : p.toOrderHom 0 = p.toOrderHom 1 := by
      have h0 := (p.toOrderHom 0).isLt
      have h1 := (p.toOrderHom 1).isLt
      ext
      omega
    exact congrArg q.toOrderHom h
  · intro h
    exact ⟨⦋0⦌, SimplexCategory.σ 0, SimplexCategory.const ⦋0⦌ n (g.toOrderHom 0), ⟨rfl, rfl⟩,
      SimplexCategory.Hom.ext_one_left _ _ rfl h⟩

theorem MarkedSSet.len_eq_one_of_mem_marked (X : MarkedSSet.{u}) {n : SimplexCategory}
    {x : X.underlying.obj (op n)} (hx : x ∈ X.marked n) : n.len = 1 :=
  X.markable n x hx

theorem MarkedSSet.map_σ_mem_marked (X : MarkedSSet.{u}) (x : X.underlying.obj (op ⦋0⦌)) :
    X.underlying.map (SimplexCategory.σ 0).op x ∈ X.marked ⦋1⦌ :=
  X.degenerate (SimplexCategory.σ 0) ⟨rfl, rfl⟩ x

def MarkedSSet.ofEdges (X : SSet.{u}) (E : Set (X _⦋1⦌)) (hE : ∀ x : X _⦋0⦌, X.σ 0 x ∈ E) :
    MarkedSSet.{u} :=
  MarkedPresheaf.ofMarking X
    { marked n := {e | ∃ h : n = ⦋1⦌, (h ▸ e : X _⦋1⦌) ∈ E}
      markable := by
        rintro n e ⟨rfl, -⟩
        rfl
      degenerate := by
        rintro ⟨a⟩ ⟨b⟩ p ⟨ha, hb⟩ y
        change a = 1 at ha
        change b = 0 at hb
        subst ha hb
        refine ⟨rfl, ?_⟩
        obtain rfl : p = SimplexCategory.σ 0 :=
          SimplexCategory.Hom.ext_one_left _ _ (Subsingleton.elim (α := Fin 1) _ _)
            (Subsingleton.elim (α := Fin 1) _ _)
        exact hE y
      transport := by
        intro a b e x
        obtain rfl : a = b := by
          rw [← SimplexCategory.mk_len a, ← SimplexCategory.mk_len b,
            SimplexCategory.len_eq_of_isIso e.hom]
        rw [SimplexCategory.eq_id_of_isIso e.hom, op_id, Functor.map_id_apply] }

theorem MarkedSSet.mem_marked_ofEdges (X : SSet.{u}) (E : Set (X _⦋1⦌))
    (hE : ∀ x : X _⦋0⦌, X.σ 0 x ∈ E) (e : X _⦋1⦌) :
    e ∈ (MarkedSSet.ofEdges X E hE).marked ⦋1⦌ ↔ e ∈ E := by
  exact (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).trans
    ⟨fun ⟨_, he⟩ => he, fun he => ⟨rfl, he⟩⟩

def MarkedSSet.ofEdgeSet (Z : SSet.{u}) (E : Set (Z _⦋1⦌)) : MarkedSSet.{u} :=
  MarkedSSet.ofEdges Z (E ∪ Set.range (Z.σ 0)) fun x => Or.inr ⟨x, rfl⟩

theorem MarkedSSet.mem_marked_ofEdgeSet (Z : SSet.{u}) (E : Set (Z _⦋1⦌)) (e : Z _⦋1⦌) :
    e ∈ (MarkedSSet.ofEdgeSet Z E).marked ⦋1⦌ ↔ e ∈ E ∨ ∃ x, Z.σ 0 x = e :=
  MarkedSSet.mem_marked_ofEdges _ _ _ e

theorem MarkedSSet.mem_marked_of_eq {Y : MarkedSSet.{u}} {x y : Y.underlying _⦋1⦌} (h : x = y)
    (hy : y ∈ Y.marked ⦋1⦌) : x ∈ Y.marked ⦋1⦌ :=
  h ▸ hy

noncomputable def MarkedSSet.ofEdgeSetHom {Z Z' : SSet.{u}} (f : Z ⟶ Z') (E : Set (Z _⦋1⦌))
    (E' : Set (Z' _⦋1⦌)) (h : ∀ e ∈ E, f.app _ e ∈ E') :
    MarkedSSet.ofEdgeSet Z E ⟶ MarkedSSet.ofEdgeSet Z' E' :=
  MarkedPresheaf.homMk f fun ⟨n⟩ x hx => by
    obtain rfl : n = 1 := (MarkedSSet.ofEdgeSet Z E).len_eq_one_of_mem_marked hx
    refine (MarkedSSet.mem_marked_ofEdgeSet Z' E' _).2 ?_
    rcases (MarkedSSet.mem_marked_ofEdgeSet Z E x).1 hx with hx | ⟨y, rfl⟩
    · exact Or.inl (h x hx)
    · exact Or.inr ⟨f.app _ y, (SSet.σ_naturality_apply f 0 y).symm⟩

@[simp]
theorem MarkedSSet.forget_map_ofEdgeSetHom {Z Z' : SSet.{u}} (f : Z ⟶ Z') (E : Set (Z _⦋1⦌))
    (E' : Set (Z' _⦋1⦌)) (h : ∀ e ∈ E, f.app _ e ∈ E') :
    MarkedPresheaf.forget.map (MarkedSSet.ofEdgeSetHom f E E' h) = f := rfl

noncomputable abbrev MarkedSSet.flatSharp (Z : SSet.{u}) :
    (MarkedPresheaf.flat edgeMarking).obj Z ⟶ (MarkedPresheaf.sharp edgeMarking).obj Z :=
  (MarkedPresheaf.forgetSharpAdjunction edgeMarking).unit.app
    ((MarkedPresheaf.flat edgeMarking).obj Z)

instance preservesMonomorphisms_flat :
    (MarkedPresheaf.flat.{u, 0} edgeMarking).PreservesMonomorphisms :=
  ⟨fun f _ => (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono f))⟩

def MarkedSSet.natural (Z : SSet.{u}) : MarkedSSet.{u} :=
  MarkedSSet.ofEdges Z {e | Nonempty (SSet.Edge.mk' e).InvStruct}
    fun x => ⟨(SSet.Edge.InvStruct.invStructId x).ofEq rfl⟩

end Atoms.Homotopical
