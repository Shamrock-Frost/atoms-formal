import Atoms.Diagrammatic.Vertex
import Atoms.Diagrammatic.HomotopyCategory
import Atoms.Molecule.Path
import Mathlib.CategoryTheory.PathCategory.Basic

open CategoryTheory Simplicial Opposite
open Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y Z : DiagSet.{u}}

namespace OneTruncation

structure Vertex (X : DiagSet.{u}) where
  cell : X.Vertex

instance : Quiver (Vertex X) where
  Hom x y := X.Edge x.cell y.cell

abbrev Free (X : DiagSet.{u}) : Type u := Paths (Vertex X)

instance : Category (Free X) := inferInstanceAs (Category (Paths (Vertex X)))

def point (x : X.Vertex) : Free X := Vertex.mk x

def edge {x y : X.Vertex} (e : X.Edge x y) : point x ⟶ point y :=
  Quiver.Hom.toPath e

theorem Free.functor_ext {D : Type*} [Category* D] {F G : Free X ⥤ D}
    (h : ∀ ⦃x y : X.Vertex⦄ (e : X.Edge x y),
      Arrow.mk (F.map (edge e)) = Arrow.mk (G.map (edge e))) : F = G :=
  Paths.ext_functor (funext fun a => congrArg Arrow.left (h (DiagSet.Edge.id a.cell)))
    fun _ _ e => by
      obtain ⟨_, _, he⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h e)
      exact he

theorem arrowMk_edge_eq {x y x' y' : X.Vertex} (e : X.Edge x y)
    (e' : X.Edge x' y') (h : e.cell = e'.cell) :
    Arrow.mk (OneTruncation.edge e) = Arrow.mk (OneTruncation.edge e') := by
  obtain rfl : x = x' := e.src_eq.symm.trans (h ▸ e'.src_eq)
  obtain rfl : y = y' := e.tgt_eq.symm.trans (h ▸ e'.tgt_eq)
  rw [DiagSet.Edge.ext h]

end OneTruncation

open OneTruncation

inductive IsComposite : PastingDiagram X → {x y : X.Vertex} →
    (point x ⟶ point y) → Prop
  | edge {x y : X.Vertex} (e : X.Edge x y) :
      IsComposite (ofCell e.cell) (OneTruncation.edge e)
  | paste {a b : PastingDiagram X} (h : a.Pastable b 0) {x y z : X.Vertex}
      {f : point x ⟶ point y} {g : point y ⟶ point z} :
      IsComposite a f → IsComposite b g → IsComposite (a.paste b 0 h) (f ≫ g)
  | equiv {a b : PastingDiagram X} (h : a.Equiv b) {x y : X.Vertex}
      {f : point x ⟶ point y} : IsComposite a f → IsComposite b f

section NativeExists

open Atoms.Molecule Atoms.Molecule.OGP Order

theorem IsComposite.hasBdry {a : PastingDiagram X} {x y : X.Vertex}
    {f : point x ⟶ point y} (hf : IsComposite a f) :
    HasBdry false 0 a (ofCell x) (ofCell y) := by
  induction hf with
  | edge e => exact hasBdry_ofCell_edge e
  | paste hp hf hg ihf ihg =>
    refine ⟨?_, ihf.dim_a, ihg.dim_b, (equiv_boundary_paste hp false).trans ihf.side,
      (equiv_boundary_paste hp true).trans ihg.other⟩
    rw [dim_paste, ihf.dim_h, ihg.dim_h, max_self]
  | equiv he hf ih =>
    exact ⟨(dim_eq_of_equiv he).symm.trans ih.dim_h, ih.dim_a, ih.dim_b,
      (he.boundary 0 false).symm.trans ih.side, (he.boundary 0 true).symm.trans ih.other⟩

open scoped Classical in
private theorem exists_isComposite_restrictTo (u : PastingDiagram X) {S : LowerSet u.shape.ogp}
    (hS : IsMoleculeIn u.shape.ogp S) (hd : krullDim S = 1) :
    ∃ (x y : X.Vertex) (φ : point x ⟶ point y), IsComposite (u.restrictTo hS) φ := by
  induction hS with
  | point x hx =>
    rw [LowerSet.krullDim_Iic, grade_eq_zero_iff.2 hx] at hd
    exact absurd hd (by norm_num)
  | atom t hround hbdry _ =>
    have ht : grade ℕ t = 1 := by
      rw [LowerSet.krullDim_Iic] at hd
      exact_mod_cast hd
    obtain ⟨a, ha⟩ := exists_equiv_ofCell_atomSimplex_one
      ((dimension_principalAtomRDC u.shape.rdc t).trans ht) (u.cellAt t)
    refine ⟨_, _, _, IsComposite.equiv ?_
      (IsComposite.edge (X.edgeEquivSSet.symm
        (SSet.Edge.mk (X := DiagSet.toSSet.obj X) a rfl rfl)))⟩
    exact (equiv_ofCell_map_iso atomSimplexOneIsoGlobe.symm a).trans
      (ha.symm.trans ((u.equiv_ofCell_cellAt t).trans
      (@equiv_restrictTo_of_eq _ u _ _ (fun a => LowerSet.decidableMemIic t a)
        (fun a => Classical.propDecidable _) _ _ rfl)))
  | paste k V W U hp hV hW hk ihV ihW =>
    have hdU := dim_restrictTo u (IsMoleculeIn.paste k V W U hp hV hW hk)
    have hdV := dim_restrictTo u hV
    have hdW := dim_restrictTo u hW
    rw [hd] at hdU
    have hk₂ := lt_min_iff.1 hk
    rw [← hdV, ← hdW] at hk₂
    have hkV : k < (u.restrictTo hV).dim := by exact_mod_cast hk₂.1
    have hkW : k < (u.restrictTo hW).dim := by exact_mod_cast hk₂.2
    have hpast : (u.restrictTo hV).Pastable (u.restrictTo hW) k :=
      ⟨(equiv_boundary_restrictTo u hV k true).trans ((equiv_restrictTo_of_eq u _ _
        (hp.inf_eq_output.symm.trans hp.inf_eq_input)).trans
          (equiv_boundary_restrictTo u hW k false).symm), lt_min hkV hkW⟩
    have hequiv : ((u.restrictTo hV).paste (u.restrictTo hW) k hpast).Equiv
        (u.restrictTo (IsMoleculeIn.paste k V W U hp hV hW hk)) :=
      equiv_paste_of_emb _ _ _ k hpast u.map (u.shape.subIncl _) (u.shape.subIncl hV)
        (u.shape.subIncl hW) rfl rfl rfl (by
          rw [MoleculeShape.map_subIncl_top, MoleculeShape.map_subIncl_top,
            MoleculeShape.map_subIncl_top]
          exact hp)
    have hdim := dim_eq_of_equiv hequiv
    rw [dim_paste] at hdim
    have h1 : (u.restrictTo (IsMoleculeIn.paste k V W U hp hV hW hk)).dim = 1 := by
      exact_mod_cast hdU
    have hk0 : k = 0 := by omega
    have hV1 : krullDim V = 1 := by
      rw [← hdV]
      exact_mod_cast (by omega : (u.restrictTo hV).dim = 1)
    have hW1 : krullDim W = 1 := by
      rw [← hdW]
      exact_mod_cast (by omega : (u.restrictTo hW).dim = 1)
    subst hk0
    obtain ⟨x, y, φ, hφ⟩ := ihV hV1
    obtain ⟨y', z, ψ, hψ⟩ := ihW hW1
    obtain rfl : y = y' := ofCell_equiv_ofCell_iff.1
      (hφ.hasBdry.other.symm.trans (hpast.1.trans hψ.hasBdry.side))
    exact ⟨x, z, φ ≫ ψ, IsComposite.equiv hequiv (IsComposite.paste hpast hφ hψ)⟩

theorem exists_isComposite_of_dim_eq_one (a : PastingDiagram X) (ha : a.dim = 1) :
    ∃ (x y : X.Vertex) (f : point x ⟶ point y), IsComposite a f := by
  have he : (@restrictTo _ a ⊤ (fun _ => Classical.propDecidable _)
      a.shape.isMolecule).Equiv a :=
    (@equiv_restrictTo_of_eq _ a _ _ (fun _ => Classical.propDecidable _) _
      _ _ rfl).trans (equiv_restrictTo_univ a)
  have hd : krullDim (⊤ : LowerSet a.shape.ogp) = 1 :=
    (@dim_restrictTo _ a ⊤ (fun _ => Classical.propDecidable _)
      a.shape.isMolecule).symm.trans (by rw [dim_eq_of_equiv he, ha]; rfl)
  obtain ⟨x, y, f, hf⟩ := exists_isComposite_restrictTo a a.shape.isMolecule hd
  exact ⟨x, y, f, hf.equiv he⟩

theorem exists_isComposite (a : PastingDiagram X) {x y : X.Vertex}
    (ha : HasBdry false 0 a (ofCell x) (ofCell y)) :
    ∃ f : point x ⟶ point y, IsComposite a f := by
  obtain ⟨x', y', f, hf⟩ := exists_isComposite_of_dim_eq_one a ha.dim_h
  obtain rfl : x' = x := ofCell_equiv_ofCell_iff.1 (hf.hasBdry.side.symm.trans ha.side)
  obtain rfl : y' = y := ofCell_equiv_ofCell_iff.1 (hf.hasBdry.other.symm.trans ha.other)
  exact ⟨f, hf⟩

end NativeExists

section Unique

open Atoms.Molecule Atoms.Molecule.OGP Order

private theorem edgeList_top_atom (U : Atom) (hU : U.dimension = 1) :
    edgeList (⊤ : LowerSet U.ogp) = [U.top] := by
  refine (edgeList_eq_of_isChain U.isMolecule (by
    rw [LowerSet.krullDim_top, U.krullDim_eq_dimension, hU]; rfl) ?_
    (List.isChain_singleton _) ?_ ?_ (by simp)).symm
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨LowerSet.mem_top, U.dimension_eq.symm.trans hU⟩
  · rintro _ ⟨⟩
    rw [U.Iic_top]
  · intro x hx
    rw [List.getLast?_singleton, Option.mem_some_iff] at hx
    rw [← hx, U.Iic_top]

private theorem krullDim_top_of_dim_eq_one {a : PastingDiagram X} (h : a.dim = 1) :
    krullDim (⊤ : LowerSet a.shape.ogp) = 1 := by
  rw [LowerSet.krullDim_top, a.shape.krullDim_eq_dimension, ← dim_def, h]
  rfl

private def IsEdgeCells (a : PastingDiagram X) (S : LowerSet a.shape.ogp) [DecidablePred (· ∈ S)]
    (l : List (diagram X (atomGlobe 1))) : Prop :=
  List.Forall₂ (fun e c => (ofCell (a.cellAt e)).Equiv (ofCell c)) (edgeList S) l

private theorem IsEdgeCells.eq {a : PastingDiagram X} {S : LowerSet a.shape.ogp}
    [DecidablePred (· ∈ S)] {l l' : List (diagram X (atomGlobe 1))} (h : IsEdgeCells a S l)
    (h' : IsEdgeCells a S l') : l = l' :=
  List.right_unique_forall₂' (fun _ _ _ ha hb => ofCell_equiv_ofCell_iff.1 (ha.symm.trans hb)) h h'

private theorem IsEdgeCells.within {a m : PastingDiagram X} (w : Within a m) (ha : a.dim = 1)
    {l : List (diagram X (atomGlobe 1))} (h : IsEdgeCells a ⊤ l) : IsEdgeCells m w.image l := by
  have he : edgeList w.image = (edgeList ⊤).map w.emb := (edgeList_congr rfl).trans
    (edgeList_map w.emb a.shape.isMolecule (krullDim_top_of_dim_eq_one ha))
  unfold IsEdgeCells
  rw [he, List.forall₂_map_left_iff]
  exact h.imp fun e x hx => (equiv_ofCell_cellAt_within w e).symm.trans hx

private theorem isEdgeCells_ofCell (c : diagram X (atomGlobe 1)) :
    IsEdgeCells (ofCell c) ⊤ [c] := by
  unfold IsEdgeCells
  rw [edgeList_top_atom (atomGlobe 1) (dimension_atomGlobe 1)]
  refine .cons ?_ .nil
  exact (equiv_ofCell_cellAt _ _).trans (((ofCell c).equiv_restrictTo_of_eq _
    (ofCell c).shape.isMolecule (atomGlobe 1).Iic_top).trans (equiv_restrictTo_univ _))

private inductive ListComp : List (diagram X (atomGlobe 1)) →
    {x y : X.Vertex} → (point x ⟶ point y) → Prop
  | single {x y : X.Vertex} (e : X.Edge x y) : ListComp [e.cell] (edge e)
  | cons {x y z : X.Vertex} (e : X.Edge x y) {l : List (diagram X (atomGlobe 1))}
      {p : point y ⟶ point z} : ListComp l p → ListComp (e.cell :: l) (edge e ≫ p)

private theorem ListComp.eq {l : List (diagram X (atomGlobe 1))}
    {x y : X.Vertex} {p : point x ⟶ point y} (h : ListComp l p) :
    ∀ {l' : List (diagram X (atomGlobe 1))} {q : point x ⟶ point y},
      ListComp l' q → l = l' → p = q := by
  induction h with
  | single e =>
    intro l' q h' hl
    cases h' with
    | single e' => rw [DiagSet.Edge.ext (List.cons.inj hl).1]
    | cons e' h'' =>
      obtain ⟨-, rfl⟩ := List.cons.inj hl
      cases h''
  | cons e h ih =>
    intro l' q h' hl
    cases h' with
    | single e' =>
      obtain ⟨-, rfl⟩ := List.cons.inj hl
      cases h
    | @cons _ y' _ e' _ _ h'' =>
      obtain ⟨he, rfl⟩ := List.cons.inj hl
      obtain rfl : _ = y' := e.tgt_eq.symm.trans (he ▸ e'.tgt_eq)
      rw [DiagSet.Edge.ext he, ih h'' rfl]

private theorem ListComp.append {l₁ l₂ : List (diagram X (atomGlobe 1))}
    {x y z : X.Vertex} {p : point x ⟶ point y} {q : point y ⟶ point z}
    (h₁ : ListComp l₁ p) (h₂ : ListComp l₂ q) : ListComp (l₁ ++ l₂) (p ≫ q) := by
  induction h₁ with
  | single e => exact .cons e h₂
  | cons e _ ih =>
    rw [Category.assoc]
    exact .cons e (ih h₂)

private theorem exists_isEdgeCells_of_isComposite {a : PastingDiagram X} {x y : X.Vertex}
    {p : point x ⟶ point y} (h : IsComposite a p) : ∃ l, IsEdgeCells a ⊤ l ∧ ListComp l p := by
  induction h with
  | edge e => exact ⟨[e.cell], isEdgeCells_ofCell _, .single e⟩
  | paste hp hu hv ihu ihv =>
    obtain ⟨l₁, h₁, c₁⟩ := ihu
    obtain ⟨l₂, h₂, c₂⟩ := ihv
    have hu1 : _ = 1 := hu.hasBdry.dim_h
    have hv1 : _ = 1 := hv.hasBdry.dim_h
    have he := (Within.isPastingIn_paste _ _ 0 hp).edgeList_eq_append
      (Within.isMoleculeIn_image _) (Within.isMoleculeIn_image _)
      (krullDim_top_of_dim_eq_one (by rw [dim_paste, hu1, hv1]; rfl)).le
    refine ⟨l₁ ++ l₂, ?_, c₁.append c₂⟩
    unfold IsEdgeCells
    rw [he]
    exact List.rel_append (h₁.within (Within.pasteInl _ _ 0 hp) hu1)
      (h₂.within (Within.pasteInr _ _ 0 hp) hv1)
  | equiv h hu ih =>
    obtain ⟨l, hl, c⟩ := ih
    have := hl.within (Within.ofEquiv h) hu.hasBdry.dim_h
    unfold IsEdgeCells at this ⊢
    rw [edgeList_congr (Within.image_ofEquiv h)] at this
    exact ⟨l, this, c⟩

theorem IsComposite.eq {a : PastingDiagram X} {x y : X.Vertex} {p q : point x ⟶ point y}
    (hp : IsComposite a p) (hq : IsComposite a q) : p = q := by
  obtain ⟨l, hl, c⟩ := exists_isEdgeCells_of_isComposite hp
  obtain ⟨l', hl', c'⟩ := exists_isEdgeCells_of_isComposite hq
  exact c.eq c' (hl.eq hl')

theorem IsComposite.arrowMk_eq {a b : PastingDiagram X} (hab : a.Equiv b) {x y x' y' : X.Vertex}
    {p : point x ⟶ point y} {q : point x' ⟶ point y'} (hp : IsComposite a p)
    (hq : IsComposite b q) : Arrow.mk p = Arrow.mk q := by
  obtain rfl : x = x' := ofCell_equiv_ofCell_iff.1
    (hp.hasBdry.side.symm.trans ((hab.boundary 0 false).trans hq.hasBdry.side))
  obtain rfl : y = y' := ofCell_equiv_ofCell_iff.1
    (hp.hasBdry.other.symm.trans ((hab.boundary 0 true).trans hq.hasBdry.other))
  rw [(hp.equiv hab).eq hq]

end Unique

inductive OneTruncation.Rel (X : DiagSet.{u}) : HomRel (Free X)
  | unit (x : X.Vertex) : Rel X (edge (DiagSet.Edge.id x)) (𝟙 (point x))
  | boundary {V : Atom} (hV : V.dimension = 2) (c : diagram X V)
      {x y : X.Vertex} {f g : point x ⟶ point y}
      (hf : IsComposite ((ofCell c).boundary 1 false) f)
      (hg : IsComposite ((ofCell c).boundary 1 true) g) : Rel X f g

abbrev OneTruncation (X : DiagSet.{u}) : Type u := CategoryTheory.Quotient (OneTruncation.Rel X)

instance : Category (OneTruncation X) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (OneTruncation.Rel X)))

namespace OneTruncation

def quotientFunctor (X : DiagSet.{u}) : Free X ⥤ OneTruncation X :=
  CategoryTheory.Quotient.functor _

def mk (x : (DiagSet.toSSet.obj X) _⦋0⦌) : OneTruncation X := (quotientFunctor X).obj (point x)

def globeHomMk {x y : X.Vertex} (e : X.Edge x y) : mk x ⟶ mk y :=
  (quotientFunctor X).map (edge e)

noncomputable def homMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) : mk x ⟶ mk y :=
  globeHomMk ((X.edgeEquivSSet (x := x) (y := y)).symm e)

theorem homMk_eq_globeHomMk {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    homMk e = globeHomMk ((X.edgeEquivSSet (x := x) (y := y)).symm e) :=
  rfl

theorem homMk_edgeEquivSSet {x y : X.Vertex} (e : X.Edge x y) :
    homMk (X.edgeEquivSSet e) = globeHomMk e :=
  congrArg globeHomMk (Equiv.symm_apply_apply _ e)

theorem globeHomMk_id (x : X.Vertex) : globeHomMk (DiagSet.Edge.id x) = 𝟙 (mk x) :=
  (CategoryTheory.Quotient.sound _ (Rel.unit x)).trans ((quotientFunctor X).map_id _)

@[simp]
theorem homMk_id (x : (DiagSet.toSSet.obj X) _⦋0⦌) : homMk (SSet.Edge.id x) = 𝟙 (mk x) :=
  (congrArg globeHomMk (DiagSet.edgeEquivSSet_symm_id (X := X) x)).trans
    (globeHomMk_id x)

theorem arrowMk_homMk_eq {x y x' y' : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y)
    (e' : SSet.Edge x' y') (h : e.edge = e'.edge) :
    Arrow.mk (homMk e) = Arrow.mk (homMk e') := by
  obtain rfl : x = x' := e.src_eq.symm.trans (h ▸ e'.src_eq)
  obtain rfl : y = y' := e.tgt_eq.symm.trans (h ▸ e'.tgt_eq)
  rw [SSet.Edge.ext h]

theorem arrowMk_globeHomMk_eq {x y x' y' : X.Vertex} (e : X.Edge x y) (e' : X.Edge x' y')
    (h : e.cell = e'.cell) : Arrow.mk (globeHomMk e) = Arrow.mk (globeHomMk e') := by
  obtain rfl : x = x' := e.src_eq.symm.trans (h ▸ e'.src_eq)
  obtain rfl : y = y' := e.tgt_eq.symm.trans (h ▸ e'.tgt_eq)
  rw [DiagSet.Edge.ext h]

theorem boundary_eq {V : Atom} (hV : V.dimension = 2) (c : diagram X V)
    {x y : X.Vertex} {f g : point x ⟶ point y}
    (hf : IsComposite ((ofCell c).boundary 1 false) f)
    (hg : IsComposite ((ofCell c).boundary 1 true) g) :
    (quotientFunctor X).map f = (quotientFunctor X).map g :=
  CategoryTheory.Quotient.sound _ (Rel.boundary hV c hf hg)

theorem exists_boundary_relation {V : Atom} (hV : V.dimension = 2) (c : diagram X V) :
    ∃ (x y : X.Vertex) (f g : point x ⟶ point y),
      IsComposite ((ofCell c).boundary 1 false) f ∧
      IsComposite ((ofCell c).boundary 1 true) g ∧
      (quotientFunctor X).map f = (quotientFunctor X).map g := by
  have hd : (ofCell c).dim = 2 := hV
  have hb (α : Bool) : ((ofCell c).boundary 1 α).dim = 1 :=
    dim_boundary _ (by rw [hd]; omega) α
  obtain ⟨x, y, f, hf⟩ := exists_isComposite_of_dim_eq_one _ (hb false)
  obtain ⟨x', y', g, hg⟩ := exists_isComposite_of_dim_eq_one _ (hb true)
  have he (α : Bool) :
      (((ofCell c).boundary 1 false).boundary 0 α).Equiv
        (((ofCell c).boundary 1 true).boundary 0 α) :=
    (equiv_boundary_boundary (ofCell c) (by omega) false α).trans
      (equiv_boundary_boundary (ofCell c) (by omega) true α).symm
  obtain rfl : x = x' := ofCell_equiv_ofCell_iff.1
    (hf.hasBdry.side.symm.trans ((he false).trans hg.hasBdry.side))
  obtain rfl : y = y' := ofCell_equiv_ofCell_iff.1
    (hf.hasBdry.other.symm.trans ((he true).trans hg.hasBdry.other))
  exact ⟨x, y, f, g, hf, hg, boundary_eq hV c hf hg⟩

theorem isComposite_simplex_edge {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    IsComposite (ofCell (e.edge : diagram X (atomSimplex 1)))
      (edge ((X.edgeEquivSSet (x := x) (y := y)).symm e)) :=
  IsComposite.equiv (equiv_ofCell_map_iso atomSimplexOneIsoGlobe.symm e.edge)
    (IsComposite.edge ((X.edgeEquivSSet (x := x) (y := y)).symm e))

theorem homMk_comp_homMk {x y z : (DiagSet.toSSet.obj X) _⦋0⦌} {f : SSet.Edge x y}
    {g : SSet.Edge y z} {h : SSet.Edge x z} (σ : SSet.Edge.CompStruct f g h) :
    homMk f ≫ homMk g = homMk h := by
  have e₁ : ((ofCell (σ.simplex : diagram X (atomSimplex 2))).boundary 1 false).Equiv
      (ofCell (h.edge : diagram X (atomSimplex 1))) :=
    (equiv_boundary_false_ofCell_atomSimplex_two σ.simplex).trans
      (ofCell_equiv_ofCell_iff.2 σ.d₁)
  have e₂ : ((ofCell (σ.simplex : diagram X (atomSimplex 2))).boundary 1 true).Equiv
      ((ofCell (f.edge : diagram X (atomSimplex 1))).paste
        (ofCell (g.edge : diagram X (atomSimplex 1))) 0 (pastable_ofCell_simplexEdge f g)) :=
    (equiv_boundary_true_ofCell_atomSimplex_two σ.simplex).trans (Equiv.paste
      (ofCell_equiv_ofCell_iff.2 σ.d₂) (ofCell_equiv_ofCell_iff.2 σ.d₀) _
      (pastable_ofCell_simplexEdge f g))
  have he := boundary_eq (dimension_atomSimplex 2) (σ.simplex : diagram X (atomSimplex 2))
    ((isComposite_simplex_edge h).equiv e₁.symm)
    ((IsComposite.paste (pastable_ofCell_simplexEdge f g) (isComposite_simplex_edge f)
      (isComposite_simplex_edge g)).equiv e₂.symm)
  exact ((quotientFunctor X).map_comp _ _).symm.trans he.symm

theorem functor_ext {D : Type*} [Category* D] {F G : OneTruncation X ⥤ D}
    (h : ∀ ⦃x y : (DiagSet.toSSet.obj X) _⦋0⦌⦄ (e : SSet.Edge x y),
      Arrow.mk (F.map (homMk e)) = Arrow.mk (G.map (homMk e))) : F = G :=
  CategoryTheory.Quotient.lift_unique' _ _ _ (Free.functor_ext fun x y e => by
    have h' := h (X.edgeEquivSSet e)
    rwa [homMk_edgeEquivSSet] at h')

section NatTrans

variable {D : Type*} [Category* D] {F G : OneTruncation X ⥤ D}

def mkNatTrans (φ : ∀ x : (DiagSet.toSSet.obj X) _⦋0⦌, F.obj (mk x) ⟶ G.obj (mk x))
    (hφ : ∀ ⦃x y : (DiagSet.toSSet.obj X) _⦋0⦌⦄ (e : SSet.Edge x y),
      F.map (homMk e) ≫ φ y = φ x ≫ G.map (homMk e)) : F ⟶ G :=
  CategoryTheory.Quotient.natTransLift _
    { app := fun a => φ a.cell
      naturality := fun _ _ p => by
        induction p using Paths.induction with
        | id =>
          exact ((congrArg (· ≫ _) ((CategoryTheory.Quotient.functor _ ⋙ F).map_id _)).trans
            (Category.id_comp _)).trans ((Category.comp_id _).symm.trans
              (congrArg (_ ≫ ·) ((CategoryTheory.Quotient.functor _ ⋙ G).map_id _).symm))
        | comp p e ih =>
          have he := hφ (X.edgeEquivSSet e)
          rw [homMk_edgeEquivSSet] at he
          exact ((congrArg (· ≫ _) ((CategoryTheory.Quotient.functor _ ⋙ F).map_comp p _)).trans
            (Category.assoc _ _ _)).trans ((congrArg (_ ≫ ·) he).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ih).trans
                ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
                  ((CategoryTheory.Quotient.functor _ ⋙ G).map_comp p _).symm))))) }

@[simp]
theorem mkNatTrans_app_mk (φ : ∀ x : (DiagSet.toSSet.obj X) _⦋0⦌, F.obj (mk x) ⟶ G.obj (mk x))
    (hφ : ∀ ⦃x y : (DiagSet.toSSet.obj X) _⦋0⦌⦄ (e : SSet.Edge x y),
      F.map (homMk e) ≫ φ y = φ x ≫ G.map (homMk e)) (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (mkNatTrans φ hφ).app (mk x) = φ x :=
  rfl

theorem natTrans_ext {τ τ' : F ⟶ G} (h : ∀ x : (DiagSet.toSSet.obj X) _⦋0⦌,
    τ.app (mk x) = τ'.app (mk x)) : τ = τ' :=
  CategoryTheory.Quotient.natTrans_ext _ _ (NatTrans.ext (funext fun a => h a.cell))

end NatTrans

section UniversalProperty

variable {C : Type*} [Category* C]

structure Interpretation (X : DiagSet.{u}) (C : Type*) [Category* C] where
  obj : X.Vertex → C
  map : ∀ {x y : X.Vertex}, X.Edge x y → (obj x ⟶ obj y)

def Interpretation.freeLift (F : Interpretation X C) : Free X ⥤ C :=
  Paths.lift { obj := fun x => F.obj x.cell, map := fun e => F.map e }

@[simp]
theorem Interpretation.freeLift_map_edge (F : Interpretation X C)
    {x y : X.Vertex} (e : X.Edge x y) :
    F.freeLift.map (edge e) = F.map e :=
  Category.id_comp (F.map e)

structure Interpretation.Respects (F : Interpretation X C) : Prop where
  unit : ∀ x, F.map (DiagSet.Edge.id x) = 𝟙 (F.obj x)
  boundary : ∀ {V : Atom}, V.dimension = 2 → ∀ (c : diagram X V)
    {x y : X.Vertex} {f g : point x ⟶ point y},
    IsComposite ((ofCell c).boundary 1 false) f →
    IsComposite ((ofCell c).boundary 1 true) g → F.freeLift.map f = F.freeLift.map g

def Interpretation.lift (F : Interpretation X C) (hF : F.Respects) : OneTruncation X ⥤ C :=
  CategoryTheory.Quotient.lift _ F.freeLift fun _ _ _ _ h => by
    cases h with
    | unit x =>
      exact (F.freeLift_map_edge _).trans
        ((hF.unit x).trans (F.freeLift.map_id (point x)).symm)
    | boundary hV c hf hg => exact hF.boundary hV c hf hg

theorem Interpretation.quotientFunctor_comp_lift (F : Interpretation X C) (hF : F.Respects) :
    quotientFunctor X ⋙ F.lift hF = F.freeLift :=
  CategoryTheory.Quotient.lift_spec _ _ _

theorem Interpretation.lift_unique (F : Interpretation X C) (hF : F.Respects)
    (G : OneTruncation X ⥤ C) (hG : quotientFunctor X ⋙ G = F.freeLift) : G = F.lift hF :=
  CategoryTheory.Quotient.lift_unique _ _ _ _ hG

@[simp]
theorem Interpretation.lift_map_globeHomMk (F : Interpretation X C) (hF : F.Respects)
    {x y : X.Vertex} (e : X.Edge x y) : (F.lift hF).map (globeHomMk e) = F.map e :=
  (CategoryTheory.Quotient.lift_map_functor_map _ _ _ _).trans (F.freeLift_map_edge e)

theorem Interpretation.lift_map_quotientFunctor_map (F : Interpretation X C) (hF : F.Respects)
    {a b : Free X} (f : a ⟶ b) : (F.lift hF).map ((quotientFunctor X).map f) = F.freeLift.map f :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ _

end UniversalProperty

def freeMap (f : X ⟶ Y) : Free X ⥤ Free Y :=
  Paths.lift { obj := fun x => point (x.cell.map f), map := fun e => edge (e.map f) }

@[simp]
theorem freeMap_edge (f : X ⟶ Y) {x y : X.Vertex} (e : X.Edge x y) :
    (freeMap f).map (edge e) = edge (e.map f) :=
  Category.id_comp _

end OneTruncation

theorem IsComposite.map (f : X ⟶ Y) {a : PastingDiagram X} {x y : X.Vertex}
    {p : point x ⟶ point y} (hp : IsComposite a p) :
    IsComposite (a.mapTo f) ((freeMap f).map p) := by
  induction hp with
  | edge e =>
    rw [freeMap_edge, ← PastingDiagram.ofCell_app]
    exact IsComposite.edge (e.map f)
  | paste h hf hg ihf ihg =>
    rw [Functor.map_comp]
    exact IsComposite.equiv (paste_mapTo _ _ 0 h f (h.mapTo f)).symm
      (IsComposite.paste (h.mapTo f) ihf ihg)
  | equiv h hp ih => exact IsComposite.equiv (h.mapTo f) ih

namespace OneTruncation

theorem map_eq_map_of_isComposite_boundary {D : Type*} [Category* D] (G : Free X ⥤ D)
    {V : Atom} (hV : V.dimension = 2) (c : diagram X V)
    (hG : ∀ {x y : (ball.{u} V).Vertex} {f g : point x ⟶ point y},
      IsComposite ((ofCell (uliftYonedaEquiv (𝟙 (ball.{u} V)))).boundary 1 false) f →
      IsComposite ((ofCell (uliftYonedaEquiv (𝟙 (ball.{u} V)))).boundary 1 true) g →
      G.map ((freeMap (uliftYonedaEquiv.symm c)).map f) =
        G.map ((freeMap (uliftYonedaEquiv.symm c)).map g))
    {x y : X.Vertex} {f g : point x ⟶ point y}
    (hf : IsComposite ((ofCell c).boundary 1 false) f)
    (hg : IsComposite ((ofCell c).boundary 1 true) g) : G.map f = G.map g := by
  obtain ⟨_, _, f', g', hf', hg', -⟩ :=
    exists_boundary_relation hV (uliftYonedaEquiv (𝟙 (ball.{u} V)))
  have e₁ := IsComposite.arrowMk_eq (.refl _)
    ((boundary_ofCell_taut_mapTo c 1 false) ▸ hf'.map (uliftYonedaEquiv.symm c)) hf
  have e₂ := IsComposite.arrowMk_eq (.refl _)
    ((boundary_ofCell_taut_mapTo c 1 true) ▸ hg'.map (uliftYonedaEquiv.symm c)) hg
  exact Arrow.mk_injective _ _ ((congrArg G.mapArrow.obj e₁).symm.trans
    ((congrArg Arrow.mk (hG hf' hg')).trans (congrArg G.mapArrow.obj e₂)))

theorem map_eq_of_rel (f : X ⟶ Y) {a b : Free X} {p q : a ⟶ b} (h : Rel X p q) :
    (freeMap f ⋙ quotientFunctor Y).map p = (freeMap f ⋙ quotientFunctor Y).map q := by
  cases h with
  | unit x =>
    have he : (DiagSet.Edge.id x).map f = DiagSet.Edge.id (x.map f) := by
      apply DiagSet.Edge.ext
      simp only [DiagSet.Edge.map_cell, DiagSet.Edge.id_cell]
      exact NatTrans.naturality_apply f (toAtomPoint (atomGlobe 1)).op x
    change (quotientFunctor Y).map ((freeMap f).map (edge (DiagSet.Edge.id x))) =
      (quotientFunctor Y).map ((freeMap f).map (𝟙 (point x)))
    exact (congrArg (quotientFunctor Y).map (freeMap_edge f _)).trans
      ((congrArg (fun e => (quotientFunctor Y).map (edge e)) he).trans
        ((globeHomMk_id _).trans
          (((congrArg (quotientFunctor Y).map ((freeMap f).map_id _)).trans
            ((quotientFunctor Y).map_id _)).symm)))
  | boundary hV c hp hq =>
    have hmap (α : Bool) :
        ((ofCell c).boundary 1 α).mapTo f = (ofCell (f.app _ c)).boundary 1 α := by
      rw [← boundary_mapTo, ← PastingDiagram.ofCell_app]
    exact boundary_eq hV (f.app _ c) ((hmap false) ▸ hp.map f) ((hmap true) ▸ hq.map f)

private def oneTruncationMap (f : X ⟶ Y) : OneTruncation X ⥤ OneTruncation Y :=
  CategoryTheory.Quotient.lift _ (freeMap f ⋙ quotientFunctor Y) fun _ _ _ _ h => map_eq_of_rel f h

private theorem oneTruncationMap_map_globeHomMk (f : X ⟶ Y) {x y : X.Vertex} (e : X.Edge x y) :
    (oneTruncationMap f).map (globeHomMk e) = globeHomMk (e.map f) :=
  (CategoryTheory.Quotient.lift_map_functor_map _ _ _ _).trans
    (congrArg (quotientFunctor Y).map (freeMap_edge f e))

private theorem oneTruncationMap_map_homMk (f : X ⟶ Y) {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    (e : SSet.Edge x y) :
    (oneTruncationMap f).map (homMk e) = homMk (e.map (DiagSet.toSSet.map f)) := by
  refine (oneTruncationMap_map_globeHomMk f _).trans (congrArg globeHomMk ?_)
  exact (Equiv.eq_symm_apply _).2 ((DiagSet.edgeEquivSSet_map _ f).trans
    (congrArg (fun t => t.map (DiagSet.toSSet.map f)) (Equiv.apply_symm_apply _ e)))

end OneTruncation

open OneTruncation in
def oneTruncation : DiagSet.{u} ⥤ Cat.{u, u} where
  obj X := Cat.of (OneTruncation X)
  map f := (oneTruncationMap f).toCatHom
  map_id _ := Cat.Hom.ext (functor_ext fun _ _ e =>
    (congrArg Arrow.mk (oneTruncationMap_map_homMk _ e)).trans (arrowMk_homMk_eq _ e rfl))
  map_comp _ _ := Cat.Hom.ext (functor_ext fun _ _ e =>
    (congrArg Arrow.mk (oneTruncationMap_map_homMk _ e)).trans ((arrowMk_homMk_eq _ _ rfl).trans
      (congrArg Arrow.mk ((congrArg (oneTruncationMap _).map (oneTruncationMap_map_homMk _ e)).trans
        (oneTruncationMap_map_homMk _ _)).symm)))

theorem oneTruncation_obj (X : DiagSet.{u}) : oneTruncation.obj X = Cat.of (OneTruncation X) :=
  rfl

@[simp]
theorem oneTruncation_map_obj_mk (f : X ⟶ Y) (x : (DiagSet.toSSet.obj X) _⦋0⦌) :
    (oneTruncation.map f).toFunctor.obj (OneTruncation.mk x) =
      OneTruncation.mk ((DiagSet.toSSet.map f).app _ x) :=
  rfl

@[simp]
theorem oneTruncation_map_map_globeHomMk (f : X ⟶ Y) {x y : X.Vertex} (e : X.Edge x y) :
    (oneTruncation.map f).toFunctor.map (OneTruncation.globeHomMk e) =
      OneTruncation.globeHomMk (e.map f) :=
  OneTruncation.oneTruncationMap_map_globeHomMk f e

@[simp]
theorem oneTruncation_map_map_homMk (f : X ⟶ Y) {x y : (DiagSet.toSSet.obj X) _⦋0⦌}
    (e : SSet.Edge x y) :
    (oneTruncation.map f).toFunctor.map (OneTruncation.homMk e) =
      OneTruncation.homMk (e.map (DiagSet.toSSet.map f)) :=
  OneTruncation.oneTruncationMap_map_homMk f e

theorem quotientFunctor_comp_oneTruncation_map (f : X ⟶ Y) :
    OneTruncation.quotientFunctor X ⋙ (oneTruncation.map f).toFunctor =
      OneTruncation.freeMap f ⋙ OneTruncation.quotientFunctor Y :=
  CategoryTheory.Quotient.lift_spec _ _ fun _ _ _ _ h => OneTruncation.map_eq_of_rel f h

end Atoms.Diagrammatic
