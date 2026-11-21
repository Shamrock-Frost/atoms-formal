import Atoms.Molecule.MoleculeShape.AtomBoundaryIso
import Atoms.Molecule.Gluing.Generated
import Atoms.Molecule.MoleculeShape.EnumerationInvariant

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

namespace FiniteOGP

private def searchOrder (P : FiniteOGP) : List P.ogp :=
  (List.range P.data.faces.length).reverse.flatMap fun d =>
    (FinEnum.toList P.ogp).filter fun x => grade ℕ x = d

private theorem mem_searchOrder (P : FiniteOGP) (x : P.ogp) : x ∈ P.searchOrder := by
  simp only [searchOrder, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_filter,
    FinEnum.mem_toList, true_and, decide_eq_true_eq]
  exact ⟨grade ℕ x, (x : ShapeData.Element P.data).1.2, rfl⟩

private def consistent (P Q : FiniteOGP) (m : List (P.ogp × Q.ogp)) (x : P.ogp) (y : Q.ogp) :
    Bool :=
  letI := decidableCovByOfGrade (P := P.ogp)
  letI := decidableCovByOfGrade (P := Q.ogp)
  decide (grade ℕ y = grade ℕ x) &&
  m.all fun p =>
    (decide (p.1 = x) == decide (p.2 = y)) &&
    (decide (x ≤ p.1) == decide (y ≤ p.2)) && (decide (p.1 ≤ x) == decide (p.2 ≤ y)) &&
    (if h : p.1 ⋖ x then if h' : p.2 ⋖ y then P.ogp.orient h == Q.ogp.orient h' else true
      else true) &&
    (if h : x ⋖ p.1 then if h' : y ⋖ p.2 then P.ogp.orient h == Q.ogp.orient h' else true
      else true)

private def isoOfGraph (P Q : FiniteOGP) (m : List (P.ogp × Q.ogp)) : Option (P.ogp ≅ Q.ogp) :=
  if hf : ∀ x, (m.lookup x).isSome then
    if hg : ∀ y, ((m.map Prod.swap).lookup y).isSome then
      let f : P.ogp → Q.ogp := fun x => (m.lookup x).get (hf x)
      let g : Q.ogp → P.ogp := fun y => ((m.map Prod.swap).lookup y).get (hg y)
      if h1 : ∀ x, g (f x) = x then
        if h2 : ∀ y, f (g y) = y then
          if hfm : IsMorphism f then
            if hgm : IsMorphism g then
              some { hom := ConcreteCategory.ofHom ⟨f, hfm⟩, inv := ConcreteCategory.ofHom ⟨g, hgm⟩,
                     hom_inv_id := by ext x; exact h1 x, inv_hom_id := by ext y; exact h2 y }
            else none
          else none
        else none
      else none
    else none
  else none

private def extendIso (P Q : FiniteOGP) : List P.ogp → List (P.ogp × Q.ogp) → Option (P.ogp ≅ Q.ogp)
  | [], m => isoOfGraph P Q m
  | x :: xs, m => (FinEnum.toList Q.ogp).findSome? fun y =>
      if consistent P Q m x y then extendIso P Q xs ((x, y) :: m) else none

def findIso? (P Q : FiniteOGP) : Option (P.ogp ≅ Q.ogp) :=
  if Fintype.card P.ogp = Fintype.card Q.ogp then extendIso P Q P.searchOrder [] else none

variable {P Q : FiniteOGP}

private theorem lookup_eq_of_iso {α β : Type*} [DecidableEq α] (e : α ≃ β)
    (m : List (α × β)) (hm : ∀ p ∈ m, e p.1 = p.2) (x : α) (hx : ∃ p ∈ m, p.1 = x) :
    m.lookup x = some (e x) := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hm' : (m.map Prod.fst).map (fun a => (a, e a)) = m.map id := by
    rw [List.map_map]
    exact List.map_congr_left fun q hq => Prod.ext rfl (hm q hq)
  rw [← m.map_id, ← hm']
  exact List.lookup_graph e (List.mem_map_of_mem hp)

private theorem isSome_isoOfGraph (e : P.ogp ≅ Q.ogp) (m : List (P.ogp × Q.ogp))
    (hm : ∀ p ∈ m, e.hom p.1 = p.2) (hall : ∀ x, ∃ p ∈ m, p.1 = x) :
    (isoOfGraph P Q m).isSome := by
  let eo := (orderIsoOfIso e).toEquiv
  have hf : ∀ x, m.lookup x = some (e.hom x) := fun x => lookup_eq_of_iso eo m hm x (hall x)
  have hg : ∀ y, (m.map Prod.swap).lookup y = some (e.inv y) := fun y => by
    refine lookup_eq_of_iso eo.symm _ (fun p hp => ?_) y ?_
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (congrArg e.inv (hm q hq)).symm.trans (e.hom_inv_id_apply q.1)
    · obtain ⟨p, hp, hpx⟩ := hall (e.inv y)
      exact ⟨p.swap, List.mem_map_of_mem hp,
        (hm p hp).symm.trans ((congrArg e.hom hpx).trans (e.inv_hom_id_apply y))⟩
  simp [isoOfGraph, hf, hg, isMorphism e.hom, isMorphism e.inv]

private theorem consistent_apply (e : P.ogp ≅ Q.ogp) (m : List (P.ogp × Q.ogp))
    (hm : ∀ p ∈ m, e.hom p.1 = p.2) (x : P.ogp) : consistent P Q m x (e.hom x) = true := by
  simp only [consistent, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨(isMorphism e.hom).grade_eq x, fun p hp => ?_⟩
  rw [← hm p hp]
  simp only [IsInclusion.le_iff, (IsInclusion.injective (f := e.hom)).eq_iff, beq_self_eq_true,
    true_and]
  refine ⟨?_, ?_⟩ <;> split_ifs with h <;>
    first | exact beq_iff_eq.2 ((isMorphism e.hom).orient_apply h).symm | rfl

private theorem isSome_extendIso (e : P.ogp ≅ Q.ogp) :
    ∀ (xs : List P.ogp) (m : List (P.ogp × Q.ogp)),
      (∀ p ∈ m, e.hom p.1 = p.2) → (∀ x, x ∈ xs ∨ ∃ p ∈ m, p.1 = x) →
        (extendIso P Q xs m).isSome := by
  intro xs
  induction xs with
  | nil =>
    exact fun m hm hall => isSome_isoOfGraph e m hm fun x => (hall x).resolve_left List.not_mem_nil
  | cons x xs ih =>
    intro m hm hall
    rw [extendIso, List.findSome?_isSome_iff]
    refine ⟨e.hom x, FinEnum.mem_toList _, ?_⟩
    rw [if_pos (consistent_apply e m hm x)]
    refine ih _ (List.forall_mem_cons.2 ⟨rfl, hm⟩) fun z => ?_
    rcases hall z with hz | ⟨p, hp, hpz⟩
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
      · exact Or.inl hz
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hpz⟩

end FiniteOGP

theorem FiniteOGP.isSome_findIso?_iff (P Q : FiniteOGP) :
    (P.findIso? Q).isSome ↔ Nonempty (P.ogp ≅ Q.ogp) := by
  refine ⟨fun h => ⟨(P.findIso? Q).get h⟩, fun ⟨e⟩ => ?_⟩
  rw [findIso?, if_pos (Fintype.card_congr (orderIsoOfIso e).toEquiv)]
  exact isSome_extendIso e _ [] (fun _ h => absurd h List.not_mem_nil)
    fun x => Or.inl (mem_searchOrder P x)

instance FiniteOGP.decidableNonemptyIso (P Q : FiniteOGP) :
    Decidable (Nonempty (P.ogp ≅ Q.ogp)) :=
  decidable_of_iff _ (P.isSome_findIso?_iff Q)

instance OGP.decidableNonemptyIso (P Q : OGP.{0}) [FinEnum P] [DecidableLE P] [FinEnum Q]
    [DecidableLE Q] : Decidable (Nonempty (P ≅ Q)) :=
  decidable_of_iff (Nonempty ((FiniteOGP.ofOGP P).ogp ≅ (FiniteOGP.ofOGP Q).ogp))
    ⟨fun ⟨e⟩ => ⟨FiniteOGP.ofOGPIso P ≪≫ e ≪≫ (FiniteOGP.ofOGPIso Q).symm⟩,
      fun ⟨e⟩ => ⟨(FiniteOGP.ofOGPIso P).symm ≪≫ e ≪≫ FiniteOGP.ofOGPIso Q⟩⟩

namespace MoleculeShape

private def pointShape : MoleculeShape := ofOGP point isAtom_point.isMoleculeIn

@[instance_reducible]
private def decidableMemOfList {P : OGP.{0}} [DecidableEq P] (S : LowerSet P) (l : List P)
    (hl : ∀ x, x ∈ l ↔ x ∈ S) : DecidablePred (· ∈ S) := fun x =>
  decidable_of_iff (x ∈ l) (hl x)

private theorem length_filter_toList (U : MoleculeShape) (S : LowerSet U.ogp)
    [DecidablePred (· ∈ S)] (p : U.ogp → Bool) (hp : ∀ x, p x = true ↔ x ∈ S) :
    ((FinEnum.toList U.ogp).filter p).length = Fintype.card (U.ogp.restrict S) := by
  have h : Fintype.card (U.ogp.restrict S) = Fintype.card {x : U.ogp // x ∈ S} :=
    Fintype.card_congr (Equiv.refl _)
  rw [← List.toFinset_card_of_nodup (FinEnum.nodup_toList.filter _), h, Fintype.card_subtype]
  congr 1
  ext x
  simp [hp]

private def listOf (U : MoleculeShape) (F : Finset U.ogp) : List U.ogp :=
  (FinEnum.toList U.ogp).filter fun x => decide (x ∈ F)

private theorem mem_listOf {U : MoleculeShape} {F : Finset U.ogp} {x : U.ogp} :
    x ∈ listOf U F ↔ x ∈ F := by
  simp [listOf, FinEnum.mem_toList]

private theorem mem_boundaryFinset_univ (U : MoleculeShape) (k : ℕ) (α : Bool) (x : U.ogp) :
    x ∈ U.ogp.boundaryFinset Finset.univ k α ↔ x ∈ U.ogp.boundary ⊤ k α := by
  have h := coe_boundaryFinset (P := U.ogp) (s := Finset.univ)
    (by rw [Finset.coe_univ]; exact isLowerSet_univ) k α
  have htop : (⟨(Finset.univ : Finset U.ogp), by rw [Finset.coe_univ]; exact isLowerSet_univ⟩ :
      LowerSet U.ogp) = ⊤ := SetLike.coe_injective (Finset.coe_univ.trans LowerSet.coe_top.symm)
  rw [htop] at h
  exact Set.ext_iff.1 h x

private def fullFinset (U : MoleculeShape) : Finset U.ogp :=
  if U.dimension = 0 then ∅
  else U.ogp.boundaryFinset Finset.univ (U.dimension - 1) false ∪
    U.ogp.boundaryFinset Finset.univ (U.dimension - 1) true

private theorem mem_fullFinset (U : MoleculeShape) (x : U.ogp) :
    x ∈ fullFinset U ↔ x ∈ U.ogp.bdryFull ⊤ := by
  unfold fullFinset
  split_ifs with h
  · rw [U.bdryFull_eq_bot h]
    exact ⟨fun h => absurd h (Finset.notMem_empty x), fun h => absurd h LowerSet.notMem_bot⟩
  · obtain ⟨d, hd⟩ : ∃ d, U.dimension = d + 1 := ⟨U.dimension - 1, by omega⟩
    rw [Finset.mem_union, mem_boundaryFinset_univ, mem_boundaryFinset_univ, hd,
      Nat.add_sub_cancel, bdryFull, LowerSet.mem_sup_iff, bdry_eq_boundary (U.krullDim_top_eq hd),
      bdry_eq_boundary (U.krullDim_top_eq hd)]

private def lookupOr {X Y : Type} [DecidableEq X] (t : List (X × Y)) (f : X → Y) (x : X) : Y :=
  match t.lookup x with
  | some y => y
  | none => f x

private theorem lookupOr_graph {X Y : Type} [DecidableEq X] [FinEnum X] (f : X → Y) :
    lookupOr ((FinEnum.toList X).map fun x => (x, f x)) f = f := by
  funext x
  rw [lookupOr, List.lookup_graph f (FinEnum.mem_toList x)]

private def tabulateHom {X Y : OGP.{0}} [DecidableEq X] [FinEnum X] (f : X ⟶ Y) : X ⟶ Y :=
  ConcreteCategory.ofHom ⟨lookupOr ((FinEnum.toList X).map fun x => (x, f x)) f, by
    rw [lookupOr_graph]
    exact isMorphism f⟩

private theorem tabulateHom_eq {X Y : OGP.{0}} [DecidableEq X] [FinEnum X] (f : X ⟶ Y) :
    tabulateHom f = f := by
  ext x
  exact congrFun (lookupOr_graph _) x

private def tabulate {X Y : OGP.{0}} [DecidableEq X] [FinEnum X] [DecidableEq Y] [FinEnum Y]
    (e : X ≅ Y) : X ≅ Y where
  hom := tabulateHom e.hom
  inv := tabulateHom e.inv
  hom_inv_id := by rw [tabulateHom_eq, tabulateHom_eq, e.hom_inv_id]
  inv_hom_id := by rw [tabulateHom_eq, tabulateHom_eq, e.inv_hom_id]

private theorem tabulate_eq {X Y : OGP.{0}} [DecidableEq X] [FinEnum X] [DecidableEq Y]
    [FinEnum Y] (e : X ≅ Y) : tabulate e = e :=
  Iso.ext (tabulateHom_eq _)

private def bdryTable (U : MoleculeShape) : List (List U.ogp × List U.ogp) :=
  (List.range U.dimension).map fun k =>
    (listOf U (U.ogp.boundaryFinset Finset.univ k false),
      listOf U (U.ogp.boundaryFinset Finset.univ k true))

private def bdryOf (U : MoleculeShape) (t : List (List U.ogp × List U.ogp)) (k : ℕ) (α : Bool) :
    List U.ogp :=
  match t[k]? with
  | some p => cond α p.2 p.1
  | none => listOf U (U.ogp.boundaryFinset Finset.univ k α)

private theorem bdryOf_bdryTable (U : MoleculeShape) (k : ℕ) (α : Bool) :
    bdryOf U (bdryTable U) k α = listOf U (U.ogp.boundaryFinset Finset.univ k α) := by
  by_cases hk : k < U.dimension <;> cases α <;> simp [bdryOf, bdryTable, hk]

private abbrev RoundCondition (U : MoleculeShape) (b : ℕ → Bool → List U.ogp) : Prop :=
  (U.dimension ≠ 0 → ∀ x, ¬ (x ∈ b 0 false ∧ x ∈ b 0 true)) ∧
    ∀ n < U.dimension - 1, ∀ x,
      (x ∈ b (n + 1) false ∧ x ∈ b (n + 1) true) ↔ (x ∈ b n false ∨ x ∈ b n true)

private theorem isRound_iff_roundCondition (U : MoleculeShape) (b : ℕ → Bool → List U.ogp)
    (hb : ∀ k α x, x ∈ b k α ↔ x ∈ U.ogp.boundary ⊤ k α) :
    U.IsRound ↔ RoundCondition U b := by
  have hdim : krullDim (⊤ : LowerSet U.ogp) = U.dimension := by
    rw [LowerSet.krullDim_top, krullDim_eq_dimension]
  simp only [RoundCondition, hb, isRound_iff]
  constructor
  · intro h
    refine ⟨fun h0 x hx => ?_, fun n hn x => ?_⟩
    · have h' := h.inf_boundary_zero (by rw [hdim]; exact_mod_cast Nat.pos_of_ne_zero h0)
      exact LowerSet.notMem_bot (h' ▸ (LowerSet.mem_inf_iff.2 hx))
    · have h' := SetLike.ext_iff.1 (h.inf_boundary_succ n
        (by rw [hdim]; exact_mod_cast (by omega : n + 1 < U.dimension))) x
      rwa [LowerSet.mem_inf_iff, boundaryFull, LowerSet.mem_sup_iff] at h'
  · rintro ⟨h0, hs⟩
    refine ⟨U.isMolecule.isGlobular, fun hpos => ?_, fun n hn => ?_⟩
    · have hd : U.dimension ≠ 0 := by
        rw [hdim] at hpos
        exact_mod_cast hpos.ne'
      ext x
      simp only [LowerSet.mem_inf_iff, SetLike.mem_coe]
      exact ⟨fun hx => absurd hx (h0 hd x), fun hx => absurd hx (LowerSet.notMem_bot)⟩
    · have hn' : n < U.dimension - 1 := by
        rw [hdim] at hn
        have : n + 1 < U.dimension := by exact_mod_cast hn
        omega
      ext x
      simpa only [SetLike.mem_coe, LowerSet.mem_inf_iff, boundaryFull, LowerSet.mem_sup_iff]
        using hs n hn' x

private structure Entry where
  shape : MoleculeShape
  card : ℕ
  card_eq : card = Fintype.card shape.ogp
  bdry : List (List shape.ogp × List shape.ogp)
  bdry_eq : bdry = bdryTable shape
  full : List shape.ogp
  full_eq : full = listOf shape (fullFinset shape)
  round : Bool
  round_iff : round = true ↔ shape.IsRound
  inv : Multiset (ℕ × ℕ × ℕ)
  inv_eq : inv = shape.enumerationInvariant

private def Entry.ofTable (U : MoleculeShape) (t : List (List U.ogp × List U.ogp))
    (ht : t = bdryTable U) : Entry where
  shape := U
  card := Fintype.card U.ogp
  card_eq := rfl
  bdry := t
  bdry_eq := ht
  full := listOf U (fullFinset U)
  full_eq := rfl
  round := decide (RoundCondition U (bdryOf U t))
  round_iff := by
    rw [decide_eq_true_iff, isRound_iff_roundCondition U (bdryOf U t) fun k α x => by
      rw [ht, bdryOf_bdryTable, mem_listOf, mem_boundaryFinset_univ]]
  inv := U.enumerationInvariant
  inv_eq := rfl

private def Entry.ofShape (U : MoleculeShape) : Entry :=
  Entry.ofTable U (bdryTable U) rfl

private def Entry.bdryList (E : Entry) (k : ℕ) (α : Bool) : List E.shape.ogp :=
  bdryOf E.shape E.bdry k α

private theorem Entry.mem_bdryList (E : Entry) (k : ℕ) (α : Bool) (x : E.shape.ogp) :
    x ∈ E.bdryList k α ↔ x ∈ E.shape.ogp.boundary ⊤ k α := by
  rw [Entry.bdryList, E.bdry_eq, bdryOf_bdryTable, mem_listOf, mem_boundaryFinset_univ]

private theorem Entry.length_bdryList (E : Entry) (k : ℕ) (α : Bool) :
    (E.bdryList k α).length = Fintype.card (E.shape.ogp.restrict (E.shape.ogp.boundary ⊤ k α)) := by
  rw [Entry.bdryList, E.bdry_eq, bdryOf_bdryTable, listOf]
  exact length_filter_toList _ _ (fun x => decide (x ∈ E.shape.ogp.boundaryFinset Finset.univ k α))
    fun x => by rw [decide_eq_true_iff, mem_boundaryFinset_univ]

private theorem Entry.mem_full (E : Entry) (x : E.shape.ogp) :
    x ∈ E.full ↔ x ∈ E.shape.ogp.bdryFull ⊤ := by
  rw [E.full_eq, mem_listOf, mem_fullFinset]

private theorem Entry.length_full (E : Entry) :
    E.full.length = Fintype.card (E.shape.ogp.restrict (E.shape.ogp.bdryFull ⊤)) := by
  rw [E.full_eq, listOf]
  exact length_filter_toList _ _ (fun x => decide (x ∈ fullFinset E.shape))
    fun x => by rw [decide_eq_true_iff, mem_fullFinset]

private theorem sub_boundary_eq (U : MoleculeShape) (k : ℕ) (α : Bool)
    [i : DecidablePred (· ∈ U.ogp.boundary ⊤ k α)] :
    U.sub (U.isMolecule.boundary k α) = U.boundary k α := by
  obtain rfl : i = fun x => decidableMemBoundary ⊤ k α x := Subsingleton.elim _ _
  rfl

private def pasteOf (U V : MoleculeShape) (k : ℕ) [DecidablePred (· ∈ U.ogp.boundary ⊤ k true)]
    [DecidablePred (· ∈ V.ogp.boundary ⊤ k false)]
    (ψ : (U.boundary k true).ogp ≅ (V.boundary k false).ogp) : MoleculeShape :=
  ofOGP (glue (tabulate (U.subIso (U.isMolecule.boundary k true) ≪≫
      eqToIso (congrArg (fun B : MoleculeShape => B.ogp) (sub_boundary_eq U k true)) ≪≫ ψ ≪≫
      (eqToIso (congrArg (fun B : MoleculeShape => B.ogp) (sub_boundary_eq V k false))).symm ≪≫
      (V.subIso (V.isMolecule.boundary k false)).symm)))
    (isMolecule_glue k _ U.isMolecule V.isMolecule)

private theorem pasteOf_eq (U V : MoleculeShape) (k : ℕ)
    [iU : DecidablePred (· ∈ U.ogp.boundary ⊤ k true)]
    [iV : DecidablePred (· ∈ V.ogp.boundary ⊤ k false)]
    (ψ : (U.boundary k true).ogp ≅ (V.boundary k false).ogp) :
    pasteOf U V k ψ = U.paste V k ψ := by
  obtain rfl : iU = fun x => decidableMemBoundary ⊤ k true x := Subsingleton.elim _ _
  obtain rfl : iV = fun x => decidableMemBoundary ⊤ k false x := Subsingleton.elim _ _
  have key : ∀ φ, φ = U.gluingIso V k ψ →
      ofOGP (glue φ) (isMolecule_glue k _ U.isMolecule V.isMolecule) = U.paste V k ψ := by
    rintro _ rfl
    rfl
  refine key _ ?_
  rw [tabulate_eq]
  exact Iso.ext (by ext x; rfl)

private def rewriteAtomOf (V W : MoleculeShape) [DecidablePred (· ∈ V.ogp.bdryFull ⊤)]
    [DecidablePred (· ∈ W.ogp.bdryFull ⊤)]
    (ψ : V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤))
    (hψ : ψ.IsSigned) (hV : V.IsRound) (hW : W.IsRound) (hd : V.dimension = W.dimension) :
    MoleculeShape :=
  ofOGP (rewrite V.dimension (tabulate ψ) (V.isRound_iff.1 hV) (W.isRound_iff.1 hW)
      V.krullDim_eq_dimension (by rw [krullDim_eq_dimension, hd]))
    (rewrite.isMolecule _ _ _ _ _ _ (by rwa [tabulate_eq]) V.isMolecule W.isMolecule)

private theorem rewriteAtomOf_eq (V W : MoleculeShape) [iV : DecidablePred (· ∈ V.ogp.bdryFull ⊤)]
    [iW : DecidablePred (· ∈ W.ogp.bdryFull ⊤)]
    (ψ : V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤))
    (hψ : ψ.IsSigned) (hV : V.IsRound) (hW : W.IsRound) (hd : V.dimension = W.dimension) :
    rewriteAtomOf V W ψ hψ hV hW hd = rewriteAtom V W ψ hψ hV hW hd := by
  obtain rfl : iV = fun x => decidableMemBdryFull ⊤ x := Subsingleton.elim _ _
  obtain rfl : iW = fun x => decidableMemBdryFull ⊤ x := Subsingleton.elim _ _
  have key : ∀ ψ', ψ' = ψ → ∀ hψ' : ψ'.IsSigned,
      ofOGP (rewrite V.dimension ψ' (V.isRound_iff.1 hV) (W.isRound_iff.1 hW)
        V.krullDim_eq_dimension (by rw [krullDim_eq_dimension, hd]))
        (rewrite.isMolecule _ _ _ _ _ _ hψ' V.isMolecule W.isMolecule) =
      rewriteAtom V W ψ hψ hV hW hd := by
    rintro _ rfl _
    rfl
  exact key _ (tabulate_eq ψ) (by rwa [tabulate_eq])

private def pasteCandidate (U V : Entry) (k : ℕ) : Option MoleculeShape :=
  letI := decidableMemOfList _ _ (U.mem_bdryList k true)
  letI := decidableMemOfList _ _ (V.mem_bdryList k false)
  ((U.shape.boundary k true).findIso? (V.shape.boundary k false).toFiniteOGP).map
    (pasteOf U.shape V.shape k)

private def boundaryIsos? (V W : MoleculeShape) (n : ℕ) :
    Option (∀ α : Bool, (V.boundary n α).ogp ≅ (W.boundary n α).ogp) :=
  match (V.boundary n false).findIso? (W.boundary n false).toFiniteOGP,
    (V.boundary n true).findIso? (W.boundary n true).toFiniteOGP with
  | some φ₀, some φ₁ => some fun α => match α with | false => φ₀ | true => φ₁
  | _, _ => none

private def rewriteCandidate (V W : Entry) : Option MoleculeShape :=
  if hV : V.round then if hW : W.round then
    if hd : V.shape.dimension = W.shape.dimension then
      if h0 : V.shape.dimension = 0 then
        some (rewriteAtom V.shape W.shape (bdryIsoOfPoints _ _ h0 (hd ▸ h0))
          (isSigned_bdryIsoOfPoints _ _ h0 (hd ▸ h0)) (V.round_iff.1 hV) (W.round_iff.1 hW) hd)
      else
        (boundaryIsos? V.shape W.shape (V.shape.dimension - 1)).map fun φ =>
          letI := decidableMemOfList _ _ V.mem_full
          letI := decidableMemOfList _ _ W.mem_full
          rewriteAtomOf V.shape W.shape
            (bdryIsoOfParallel _ _ φ (V.round_iff.1 hV) (W.round_iff.1 hW) (by omega) (by omega))
            (isSigned_bdryIsoOfParallel _ _ φ _ _ _ _) (V.round_iff.1 hV) (W.round_iff.1 hW) hd
    else none
  else none
  else none

private def candidates (n s : ℕ) (L : List Entry) : List MoleculeShape :=
  pointShape ::
    ((L.flatMap fun U => L.flatMap fun V =>
      (List.range (min U.shape.dimension V.shape.dimension)).filterMap fun k =>
        if U.card + V.card = s + (V.bdryList k false).length then pasteCandidate U V k
        else none) ++
    (L.flatMap fun V => L.filterMap fun W =>
      if V.shape.dimension < n ∧ V.card + W.card + 1 = s + W.full.length then rewriteCandidate V W
      else none))

private def insertWith (L : List Entry) (P : MoleculeShape) (i : Multiset (ℕ × ℕ × ℕ)) :
    List Entry :=
  if L.reverse.any fun Q => decide (Q.inv = i) && (Q.shape.findIso? P.toFiniteOGP).isSome then L
  else L ++ [Entry.ofShape P]

private def insertNew (L : List Entry) (P : MoleculeShape) : List Entry :=
  insertWith L P P.enumerationInvariant

private def generate (n : ℕ) : ℕ → List Entry
  | 0 => []
  | s + 1 =>
    ((candidates n (s + 1) (generate n s)).filter fun P =>
      decide (P.dimension ≤ n ∧ Fintype.card P.ogp ≤ s + 1)).foldl insertNew
      (generate n s)

private theorem mem_insertNew_of_mem {L : List Entry} {P : MoleculeShape} {Q : Entry} (h : Q ∈ L) :
    Q ∈ insertNew L P := by
  unfold insertNew insertWith
  split_ifs
  · exact h
  · exact List.mem_append_left _ h

private theorem mem_or_eq_of_mem_insertNew {L : List Entry} {P : MoleculeShape} {Q : Entry}
    (h : Q ∈ insertNew L P) : Q ∈ L ∨ Q.shape = P := by
  unfold insertNew insertWith at h
  split_ifs at h
  · exact Or.inl h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · rw [List.mem_singleton.1 h]
      exact Or.inr rfl

private theorem exists_iso_mem_insertNew (L : List Entry) (P : MoleculeShape) :
    ∃ Q ∈ insertNew L P, Nonempty (P.ogp ≅ Q.shape.ogp) := by
  unfold insertNew insertWith
  split_ifs with h
  · obtain ⟨Q, hQ, hs⟩ := List.any_eq_true.1 h
    obtain ⟨e⟩ := (FiniteOGP.isSome_findIso?_iff _ _).1 (Bool.and_eq_true_iff.1 hs).2
    exact ⟨Q, List.mem_reverse.1 hQ, ⟨e.symm⟩⟩
  · exact ⟨Entry.ofShape P, List.mem_append_right _ List.mem_cons_self, ⟨Iso.refl _⟩⟩

private theorem pairwise_insertNew {L : List Entry} (P : MoleculeShape)
    (h : L.Pairwise fun Q R => IsEmpty (Q.shape.ogp ≅ R.shape.ogp)) :
    (insertNew L P).Pairwise fun Q R => IsEmpty (Q.shape.ogp ≅ R.shape.ogp) := by
  unfold insertNew insertWith
  split_ifs with hL
  · exact h
  · refine List.pairwise_append.2 ⟨h, List.pairwise_singleton _ _, fun Q hQ R hR => ?_⟩
    rw [List.mem_singleton.1 hR]
    rw [List.any_eq_true] at hL
    exact not_nonempty_iff.1 fun ⟨e⟩ => hL ⟨Q, List.mem_reverse.2 hQ, Bool.and_eq_true_iff.2
      ⟨decide_eq_true (Q.inv_eq.trans (FiniteOGP.enumerationInvariant_eq_of_iso e)),
        (FiniteOGP.isSome_findIso?_iff _ _).2 ⟨e⟩⟩⟩

private theorem mem_or_mem_of_mem_foldl_insertNew {Q : Entry} :
    ∀ (cs : List MoleculeShape) (L : List Entry), Q ∈ cs.foldl insertNew L → Q ∈ L ∨ Q.shape ∈ cs
  | [], _, h => Or.inl h
  | P :: cs, L, h => by
    rcases mem_or_mem_of_mem_foldl_insertNew cs _ h with h | h
    · rcases mem_or_eq_of_mem_insertNew h with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem mem_foldl_insertNew_of_mem {Q : Entry} :
    ∀ (cs : List MoleculeShape) (L : List Entry), Q ∈ L → Q ∈ cs.foldl insertNew L
  | [], _, h => h
  | _ :: cs, _, h => mem_foldl_insertNew_of_mem cs _ (mem_insertNew_of_mem h)

private theorem exists_iso_mem_foldl_insertNew {P : MoleculeShape} :
    ∀ (cs : List MoleculeShape) (L : List Entry), P ∈ cs →
      ∃ Q ∈ cs.foldl insertNew L, Nonempty (P.ogp ≅ Q.shape.ogp)
  | [], _, h => absurd h List.not_mem_nil
  | R :: cs, L, h => by
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨Q, hQ, e⟩ := exists_iso_mem_insertNew L P
      exact ⟨Q, mem_foldl_insertNew_of_mem cs _ hQ, e⟩
    · exact exists_iso_mem_foldl_insertNew cs _ h

private theorem pairwise_foldl_insertNew :
    ∀ (cs : List MoleculeShape) (L : List Entry),
      L.Pairwise (fun Q R => IsEmpty (Q.shape.ogp ≅ R.shape.ogp)) →
        (cs.foldl insertNew L).Pairwise fun Q R => IsEmpty (Q.shape.ogp ≅ R.shape.ogp)
  | [], _, h => h
  | P :: cs, _, h => pairwise_foldl_insertNew cs _ (pairwise_insertNew P h)

private theorem bounds_of_mem_generate {n : ℕ} :
    ∀ {s : ℕ} {Q : Entry}, Q ∈ generate n s →
      Q.shape.dimension ≤ n ∧ Fintype.card Q.shape.ogp ≤ s
  | 0, _, h => absurd h List.not_mem_nil
  | s + 1, Q, h => by
    rcases mem_or_mem_of_mem_foldl_insertNew _ _ h with h | h
    · have := bounds_of_mem_generate h
      omega
    · simpa using (List.mem_filter.1 h).2

private theorem pairwise_generate (n : ℕ) :
    ∀ s, (generate n s).Pairwise fun Q R => IsEmpty (Q.shape.ogp ≅ R.shape.ogp)
  | 0 => List.Pairwise.nil
  | s + 1 => pairwise_foldl_insertNew _ _ (pairwise_generate n s)

private theorem mem_generate_succ {n s : ℕ} {Q : Entry} (h : Q ∈ generate n s) :
    Q ∈ generate n (s + 1) :=
  mem_foldl_insertNew_of_mem _ _ h

private theorem exists_iso_mem_generate_of_mem_candidates {n s : ℕ} {P : MoleculeShape}
    (h : P ∈ candidates n (s + 1) (generate n s)) (hd : P.dimension ≤ n)
    (hc : Fintype.card P.ogp ≤ s + 1) :
    ∃ Q ∈ generate n (s + 1), Nonempty (P.ogp ≅ Q.shape.ogp) :=
  exists_iso_mem_foldl_insertNew _ _ (List.mem_filter.2 ⟨h, by simpa using ⟨hd, hc⟩⟩)

private theorem card_glue {P Q : OGP.{0}} [Fintype P] [Fintype Q] [FinEnum P] [FinEnum Q]
    {S : LowerSet P} {T : LowerSet Q} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (φ : P.restrict S ≅ Q.restrict T) :
    Fintype.card (glue φ) + Fintype.card (Q.restrict T) = Fintype.card P + Fintype.card Q := by
  classical
  have h1 : Fintype.card (P ⊕ {q : Q // q ∉ T}) = Fintype.card (glue φ) := by
    refine Fintype.card_of_bijective (f := Sum.elim (GlueCarrier.inl φ)
      fun q => GlueCarrier.inr φ q.1) ⟨?_, fun x => ?_⟩
    · rintro (p | q) (p' | q') h
      · exact congrArg Sum.inl (GlueCarrier.inl_injective h)
      · obtain ⟨hp, hq⟩ := GlueCarrier.inl_eq_inr_iff.1 h
        exact absurd (hq ▸ (φ.hom ⟨p, hp⟩).2) q'.2
      · obtain ⟨hp, hq⟩ := GlueCarrier.inl_eq_inr_iff.1 h.symm
        exact absurd (hq ▸ (φ.hom ⟨p', hp⟩).2) q.2
      · exact congrArg Sum.inr (Subtype.ext (GlueCarrier.inr_injective h))
    · rcases GlueCarrier.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · exact ⟨.inl p, rfl⟩
      · by_cases hq : q ∈ T
        · exact ⟨.inl (φ.inv ⟨q, hq⟩).1, (GlueCarrier.inr_eq_inl_of_mem hq).symm⟩
        · exact ⟨.inr ⟨q, hq⟩, rfl⟩
  have h2 : Fintype.card (Q.restrict T) = Fintype.card {q : Q // q ∈ T} :=
    Fintype.card_congr (Equiv.refl _)
  rw [Fintype.card_sum, Fintype.card_subtype_compl] at h1
  have := Fintype.card_subtype_le (· ∈ T)
  omega

private theorem card_rewriteAtom (V W : MoleculeShape)
    (ψ : V.ogp.restrict (V.ogp.bdryFull ⊤) ≅ W.ogp.restrict (W.ogp.bdryFull ⊤)) (hψ : ψ.IsSigned)
    (hV : V.IsRound) (hW : W.IsRound) (hd : V.dimension = W.dimension) :
    Fintype.card (rewriteAtom V W ψ hψ hV hW hd).ogp +
        Fintype.card (W.ogp.restrict (W.ogp.bdryFull ⊤)) =
      Fintype.card V.ogp + Fintype.card W.ogp + 1 := by
  have h1 := Fintype.card_congr (orderIsoOfIso (FiniteOGP.ofOGPIso
    (rewrite V.dimension ψ (V.isRound_iff.1 hV) (W.isRound_iff.1 hW) V.krullDim_eq_dimension
      (by rw [krullDim_eq_dimension, hd])))).toEquiv
  have h2 : Fintype.card (rewrite V.dimension ψ (V.isRound_iff.1 hV) (W.isRound_iff.1 hW)
      V.krullDim_eq_dimension (by rw [krullDim_eq_dimension, hd])) =
        Fintype.card (Option (glue ψ)) :=
    Fintype.card_congr (Equiv.refl _)
  have h3 := card_glue ψ
  have h4 : Fintype.card (rewriteAtom V W ψ hψ hV hW hd).ogp =
      Fintype.card (FiniteOGP.ofOGP (rewrite V.dimension ψ (V.isRound_iff.1 hV)
        (W.isRound_iff.1 hW) V.krullDim_eq_dimension (by rw [krullDim_eq_dimension, hd]))).ogp :=
    rfl
  rw [Fintype.card_option] at h2
  omega

private theorem exists_pasteCandidate_eq (U V : Entry) (k : ℕ)
    (h : Nonempty ((U.shape.boundary k true).ogp ≅ (V.shape.boundary k false).ogp)) :
    ∃ ψ, pasteCandidate U V k = some (U.shape.paste V.shape k ψ) := by
  obtain ⟨ψ, hψ⟩ := Option.isSome_iff_exists.1 ((FiniteOGP.isSome_findIso?_iff _ _).2 h)
  exact ⟨ψ, by rw [pasteCandidate, hψ, Option.map_some, pasteOf_eq]⟩

private theorem isSome_boundaryIsos? (V W : MoleculeShape) (n : ℕ)
    (h : ∀ α, Nonempty ((V.boundary n α).ogp ≅ (W.boundary n α).ogp)) :
    (boundaryIsos? V W n).isSome := by
  obtain ⟨φ₀, h₀⟩ := Option.isSome_iff_exists.1 ((FiniteOGP.isSome_findIso?_iff _ _).2 (h false))
  obtain ⟨φ₁, h₁⟩ := Option.isSome_iff_exists.1 ((FiniteOGP.isSome_findIso?_iff _ _).2 (h true))
  rw [boundaryIsos?, h₀, h₁]
  rfl

private theorem exists_rewriteCandidate_eq (V W : Entry) (hV : V.shape.IsRound)
    (hW : W.shape.IsRound) (hd : V.shape.dimension = W.shape.dimension)
    (hb : 0 < V.shape.dimension → ∀ α, Nonempty ((V.shape.boundary (V.shape.dimension - 1) α).ogp ≅
      (W.shape.boundary (V.shape.dimension - 1) α).ogp)) :
    ∃ ψ hψ, rewriteCandidate V W = some (rewriteAtom V.shape W.shape ψ hψ hV hW hd) := by
  rw [rewriteCandidate, dif_pos (V.round_iff.2 hV), dif_pos (W.round_iff.2 hW), dif_pos hd]
  by_cases h0 : V.shape.dimension = 0
  · rw [dif_pos h0]
    exact ⟨_, _, rfl⟩
  · rw [dif_neg h0]
    obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1
      (isSome_boundaryIsos? V.shape W.shape _ (hb (Nat.pos_of_ne_zero h0)))
    rw [hφ, Option.map_some, rewriteAtomOf_eq]
    exact ⟨_, _, rfl⟩

private theorem pasteCandidate_mem_candidates {n s : ℕ} {L : List Entry}
    {U V : Entry} {C : MoleculeShape} {k : ℕ} (hU : U ∈ L) (hV : V ∈ L)
    (hk : k < min U.shape.dimension V.shape.dimension)
    (hc : Fintype.card U.shape.ogp + Fintype.card V.shape.ogp =
      s + Fintype.card (V.shape.ogp.restrict (V.shape.ogp.boundary ⊤ k false)))
    (h : pasteCandidate U V k = some C) : C ∈ candidates n s L := by
  refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨U, hU,
    List.mem_flatMap.2 ⟨V, hV, List.mem_filterMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩))
  rw [if_pos (by rw [U.card_eq, V.card_eq, V.length_bdryList]; exact hc), h]

private theorem rewriteCandidate_mem_candidates {n s : ℕ} {L : List Entry}
    {V W : Entry} {C : MoleculeShape} (hV : V ∈ L) (hW : W ∈ L) (hn : V.shape.dimension < n)
    (hc : Fintype.card V.shape.ogp + Fintype.card W.shape.ogp + 1 =
      s + Fintype.card (W.shape.ogp.restrict (W.shape.ogp.bdryFull ⊤)))
    (h : rewriteCandidate V W = some C) : C ∈ candidates n s L := by
  refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨V, hV,
    List.mem_filterMap.2 ⟨W, hW, ?_⟩⟩))
  rw [if_pos ⟨hn, by rw [V.card_eq, W.card_eq, W.length_full]; exact hc⟩, h]

private theorem nonempty_iso_of_map_eq {A B Z : OGP.{0}} (f : A ⟶ Z) (g : B ⟶ Z)
    [IsInclusion f] [IsInclusion g] (h : map f ⊤ = map g ⊤) : Nonempty (A ≅ B) := by
  obtain ⟨e₁, -⟩ := exists_iso_restrict f rfl
  obtain ⟨e₂, -⟩ := exists_iso_restrict g h.symm
  exact ⟨e₁ ≪≫ e₂.symm⟩

private theorem dimension_eq_of_iso {P Q : MoleculeShape} (e : P.ogp ≅ Q.ogp) :
    P.dimension = Q.dimension := by
  have h := krullDim_eq_of_orderIso (orderIsoOfIso e)
  rw [P.krullDim_eq_dimension, Q.krullDim_eq_dimension] at h
  exact_mod_cast h

private theorem card_sub_le (M : MoleculeShape) {s : ℕ} (hc : Fintype.card M.ogp = s + 1)
    {S : LowerSet M.ogp} [DecidablePred (· ∈ S)] (hS : IsMoleculeIn M.ogp S) (hSU : S < ⊤) :
    Fintype.card (M.sub hS).ogp ≤ s := by
  obtain ⟨x, -, hxS⟩ := Set.exists_of_ssubset (LowerSet.coe_ssubset_coe.2 hSU)
  have hlt : Fintype.card (M.sub hS).ogp < Fintype.card M.ogp :=
    Fintype.card_lt_of_injective_not_surjective _ (IsInclusion.injective (f := M.subIncl hS))
      fun h => hxS (M.map_subIncl_top hS ▸ (h x).elim fun y hy => ⟨y, LowerSet.mem_top, hy⟩)
  omega

private theorem map_boundaryIncl_comp (M X : MoleculeShape) {d j : ℕ} (hj : j < d)
    (α β : Bool) (e : (M.boundary d β).ogp ≅ X.ogp) :
    map (X.boundaryIncl j α ≫ e.inv ≫ M.boundaryIncl d β) ⊤ = M.ogp.boundary ⊤ j α := by
  rw [map_comp, map_comp, X.map_boundaryIncl_top, map_boundary, map_top_of_isIso,
    map_boundary, M.map_boundaryIncl_top, M.isMolecule.isGlobular j d hj α β]

private theorem exists_mem_candidates_iso_of_atom {n s : ℕ} {L : List Entry}
    (ih : ∀ M : MoleculeShape, M.dimension ≤ n → Fintype.card M.ogp ≤ s →
      ∃ Q ∈ L, Nonempty (M.ogp ≅ Q.shape.ogp))
    (M : MoleculeShape) (hn : M.dimension ≤ n) (hc : Fintype.card M.ogp = s + 1)
    {t : M.ogp} (hU : (⊤ : LowerSet M.ogp) = .Iic t) (hround : M.ogp.IsRound (.Iic t))
    (hb : ∀ α, IsMoleculeIn M.ogp (M.ogp.bdry (.Iic t) α)) :
    ∃ C ∈ candidates n (s + 1) L, Nonempty (M.ogp ≅ C.ogp) := by
  have ha : IsAtom M.ogp := ⟨M.isMolecule, t, hU⟩
  have hgt : 0 < grade ℕ t := by
    obtain ⟨y, hy⟩ := (hb false).nonempty
    have h : y ∈ ((M.ogp.bdry (.Iic t) false ⊔ M.ogp.bdry (.Iic t) true :
      LowerSet M.ogp) : Set M.ogp) := Or.inl hy
    rw [coe_bdry_Iic_sup] at h
    exact (Nat.zero_le _).trans_lt (grade_strictMono (𝕆 := ℕ) h)
  have hMd : M.dimension = grade ℕ t := by
    have h := M.krullDim_eq_dimension.symm
    rw [← LowerSet.krullDim_top, hU, LowerSet.krullDim_Iic] at h
    exact_mod_cast h
  obtain ⟨d, hd⟩ : ∃ d, M.dimension = d + 1 := ⟨M.dimension - 1, by omega⟩
  have hBcard (α : Bool) : Fintype.card (M.boundary d α).ogp ≤ s :=
    card_sub_le M hc (M.isMolecule.boundary d α)
      (by rw [← bdry_eq_boundary (M.krullDim_top_eq hd), hU]; exact bdry_Iic_lt t α)
  have hBdim (α : Bool) : (M.boundary d α).dimension = d := M.dimension_boundary (by omega) α
  have hBround (α : Bool) : (M.boundary d α).IsRound :=
    isRound_boundary M (by rw [IsRound, hU]; exact hround) d α
  obtain ⟨EV, hVL, ⟨eV⟩⟩ := ih _ (by rw [hBdim]; omega) (hBcard false)
  obtain ⟨EW, hWL, ⟨eW⟩⟩ := ih _ (by rw [hBdim]; omega) (hBcard true)
  have hVd : EV.shape.dimension = d := (dimension_eq_of_iso eV).symm.trans (hBdim false)
  have hWd : EW.shape.dimension = d := (dimension_eq_of_iso eW).symm.trans (hBdim true)
  have hVW : EV.shape.dimension = EW.shape.dimension := hVd.trans hWd.symm
  have hVr : EV.shape.IsRound := (isRound_top_iff_of_iso eV).2 (hBround false)
  have hWr : EW.shape.IsRound := (isRound_top_iff_of_iso eW).2 (hBround true)
  obtain ⟨ψ, hψ, hrw⟩ := exists_rewriteCandidate_eq EV EW hVr hWr hVW
    (fun hV0 α => by
      rw [hVd] at hV0 ⊢
      exact nonempty_iso_of_map_eq
        (EV.shape.boundaryIncl (d - 1) α ≫ eV.inv ≫ M.boundaryIncl d false)
        (EW.shape.boundaryIncl (d - 1) α ≫ eW.inv ≫ M.boundaryIncl d true)
        ((map_boundaryIncl_comp M EV.shape (by omega) α false eV).trans
          (map_boundaryIncl_comp M EW.shape (by omega) α true eW).symm))
  let φ (α : Bool) : (M.boundary EV.shape.dimension α).ogp ≅ (cond α EW.shape EV.shape).ogp := by
    rw [hVd]
    exact match α with | false => eV | true => eW
  obtain ⟨e⟩ := nonempty_iso_of_boundary_iso (rewriteAtom EV.shape EW.shape ψ hψ hVr hWr hVW) M
    (fun α => boundaryIsoRewriteAtom EV.shape EW.shape ψ hψ hVr hWr hVW α ≪≫ (φ α).symm)
    (isAtom_rewriteAtom EV.shape EW.shape ψ hψ hVr hWr hVW) ha
    (dimension_rewriteAtom EV.shape EW.shape ψ hψ hVr hWr hVW)
    (by omega)
  refine ⟨_, rewriteCandidate_mem_candidates hVL hWL (by omega) ?_ hrw, ⟨e.symm⟩⟩
  have := card_rewriteAtom EV.shape EW.shape ψ hψ hVr hWr hVW
  rw [Fintype.card_congr (orderIsoOfIso e).toEquiv, hc] at this
  omega

private theorem exists_mem_candidates_iso_of_isPastingIn {n s : ℕ} {L : List Entry}
    (ih : ∀ M : MoleculeShape, M.dimension ≤ n → Fintype.card M.ogp ≤ s →
      ∃ Q ∈ L, Nonempty (M.ogp ≅ Q.shape.ogp))
    (M : MoleculeShape) (hn : M.dimension ≤ n) (hc : Fintype.card M.ogp = s + 1)
    {k : ℕ} {V W : LowerSet M.ogp} (hp : M.ogp.IsPastingIn k V W ⊤)
    (hV : IsMoleculeIn M.ogp V) (hW : IsMoleculeIn M.ogp W)
    (hk : (k : WithBot ℕ∞) < min (krullDim V) (krullDim W)) :
    ∃ C ∈ candidates n (s + 1) L, Nonempty (M.ogp ≅ C.ogp) := by
  classical
  have hdim {S : LowerSet M.ogp} (hS : IsMoleculeIn M.ogp S) : (M.sub hS).dimension ≤ n := by
    have h1 : krullDim S ≤ krullDim (⊤ : LowerSet M.ogp) := LowerSet.krullDim_mono le_top
    have h : ((M.sub hS).dimension : WithBot ℕ∞) ≤ (n : ℕ) := by
      rw [M.dimension_sub hS]
      exact h1.trans (by rw [LowerSet.krullDim_top, M.krullDim_eq_dimension]; exact_mod_cast hn)
    exact_mod_cast h
  obtain ⟨EU, hUL, ⟨eU⟩⟩ :=
    ih _ (hdim hV) (card_sub_le M hc hV (hp.lt_cond false (lt_min_iff.1 hk).2))
  obtain ⟨EV, hVL, ⟨eV⟩⟩ :=
    ih _ (hdim hW) (card_sub_le M hc hW (hp.lt_cond true (lt_min_iff.1 hk).1))
  let i : EU.shape.ogp ⟶ M.ogp := eU.inv ≫ M.subIncl hV
  let j : EV.shape.ogp ⟶ M.ogp := eV.inv ≫ M.subIncl hW
  have hp' : M.ogp.IsPastingIn k (map i ⊤) (map j ⊤) ⊤ := by simpa [i, j, map_comp] using hp
  obtain ⟨φ, -, -⟩ := hp'.exists_isPushout
  obtain ⟨ψ, hψ⟩ :=
    exists_pasteCandidate_eq EU EV k ⟨(EU.shape.subIso _).symm ≪≫ φ ≪≫ EV.shape.subIso _⟩
  obtain ⟨e⟩ := IsPasting.nonempty_iso EU.shape.isMolecule ⟨i, j, inferInstance, inferInstance, hp'⟩
    ((isPasting_glue EU.shape.ogp EV.shape.ogp k (EU.shape.gluingIso EV.shape k ψ)).of_iso
      (EU.shape.pasteIso EV.shape k ψ))
  have hk' : k < min EU.shape.dimension EV.shape.dimension := by
    rw [← M.dimension_sub hV, ← M.dimension_sub hW, dimension_eq_of_iso eU,
      dimension_eq_of_iso eV, ← Nat.mono_cast.map_min] at hk
    exact_mod_cast hk
  refine ⟨_, pasteCandidate_mem_candidates hUL hVL hk' ?_ hψ, ⟨e⟩⟩
  have h1 := card_glue (EU.shape.gluingIso EV.shape k ψ)
  rw [Fintype.card_congr (orderIsoOfIso (EU.shape.pasteIso EV.shape k ψ)).toEquiv,
    ← Fintype.card_congr (orderIsoOfIso e).toEquiv, hc] at h1
  omega

private theorem exists_mem_candidates_iso {n s : ℕ} {L : List Entry}
    (ih : ∀ M : MoleculeShape, M.dimension ≤ n → Fintype.card M.ogp ≤ s →
      ∃ Q ∈ L, Nonempty (M.ogp ≅ Q.shape.ogp))
    (M : MoleculeShape) (hn : M.dimension ≤ n) (hc : Fintype.card M.ogp = s + 1) :
    ∃ C ∈ candidates n (s + 1) L, Nonempty (M.ogp ≅ C.ogp) := by
  have hM : IsMoleculeIn M.ogp ⊤ := M.isMolecule
  generalize hU : (⊤ : LowerSet M.ogp) = U at hM
  cases hM with
  | point x hx =>
    obtain ⟨e, -⟩ := exists_iso_restrict (𝟙 M.ogp) ((map_top_of_isIso _).trans hU)
    exact ⟨pointShape, List.mem_cons_self,
      ⟨e ≪≫ (isoPointRestrictIic hx).symm ≪≫ FiniteOGP.ofOGPIso point⟩⟩
  | atom t hround hb =>
    exact exists_mem_candidates_iso_of_atom ih M hn hc hU hround hb
  | paste k V W U hp hV hW hk =>
    subst hU
    exact exists_mem_candidates_iso_of_isPastingIn ih M hn hc hp hV hW hk

private theorem exists_iso_mem_generate (n : ℕ) :
    ∀ (s : ℕ) (M : MoleculeShape), M.dimension ≤ n → Fintype.card M.ogp ≤ s →
      ∃ Q ∈ generate n s, Nonempty (M.ogp ≅ Q.shape.ogp)
  | 0, M, _, hc => by
    obtain ⟨x, -⟩ := M.isMolecule.nonempty
    have : Nonempty M.ogp := ⟨x⟩
    exact absurd hc (Nat.not_le.2 Fintype.card_pos)
  | s + 1, M, hn, hc => by
    rcases Nat.lt_or_ge (Fintype.card M.ogp) (s + 1) with hlt | hge
    · obtain ⟨Q, hQ, e⟩ := exists_iso_mem_generate n s M hn (by omega)
      exact ⟨Q, mem_generate_succ hQ, e⟩
    · obtain ⟨C, hC, ⟨e⟩⟩ := exists_mem_candidates_iso (exists_iso_mem_generate n s) M hn
        (by omega)
      obtain ⟨Q, hQ, ⟨e'⟩⟩ := exists_iso_mem_generate_of_mem_candidates hC
        (by have := dimension_eq_of_iso e; omega)
        (by rw [← Fintype.card_congr (orderIsoOfIso e).toEquiv]; exact hc)
      exact ⟨Q, hQ, ⟨e ≪≫ e'⟩⟩

end MoleculeShape

def MoleculeShape.enumerate (n b : ℕ) : List MoleculeShape :=
  (MoleculeShape.generate n b).map MoleculeShape.Entry.shape

theorem MoleculeShape.exists_iso_mem_enumerate_iff (n b : ℕ) (P : OGP.{0}) [Fintype P] :
    (∃ Q ∈ MoleculeShape.enumerate n b, Nonempty (P ≅ Q.ogp)) ↔
      IsMolecule P ∧ krullDim P ≤ n ∧ Fintype.card P ≤ b := by
  constructor
  · rintro ⟨Q, hQ, ⟨e⟩⟩
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 hQ
    have hb := MoleculeShape.bounds_of_mem_generate hE
    have hd : krullDim P = E.shape.dimension :=
      (krullDim_eq_of_orderIso (orderIsoOfIso e)).trans E.shape.krullDim_eq_dimension
    have hc := Fintype.card_congr (orderIsoOfIso e).toEquiv
    exact ⟨(isMolecule_iff_of_iso e).1 E.shape.isMolecule,
      by rw [hd]; exact_mod_cast hb.1, hc.symm ▸ hb.2⟩
  · rintro ⟨hP, hd, hc⟩
    classical
    obtain ⟨f⟩ := (Fintype.truncEquivFin P).nonempty
    let : FinEnum P := FinEnum.ofEquiv _ f
    let M : MoleculeShape := MoleculeShape.ofOGP P hP
    let e : P ≅ M.ogp := FiniteOGP.ofOGPIso P
    have hMd : M.dimension ≤ n := by
      exact_mod_cast (MoleculeShape.dimension_ofOGP P hP).le.trans hd
    obtain ⟨Q, hQ, ⟨e'⟩⟩ := MoleculeShape.exists_iso_mem_generate n b M hMd
      ((Fintype.card_congr (orderIsoOfIso e).toEquiv) ▸ hc)
    exact ⟨Q.shape, List.mem_map_of_mem hQ, ⟨e ≪≫ e'⟩⟩

theorem MoleculeShape.pairwise_isEmpty_iso_enumerate (n b : ℕ) :
    (MoleculeShape.enumerate n b).Pairwise fun Q R => IsEmpty (Q.ogp ≅ R.ogp) :=
  List.pairwise_map.2 (MoleculeShape.pairwise_generate n b)

def MoleculeShape.enumerateAtoms (n b : ℕ) : List MoleculeShape :=
  (MoleculeShape.enumerate n b).filter fun P =>
    decide (∃ t : P.ogp, (⊤ : LowerSet P.ogp) = LowerSet.Iic t)

theorem MoleculeShape.exists_iso_mem_enumerateAtoms_iff (n b : ℕ) (P : OGP.{0}) [Fintype P] :
    (∃ Q ∈ MoleculeShape.enumerateAtoms n b, Nonempty (P ≅ Q.ogp)) ↔
      IsAtom P ∧ krullDim P ≤ n ∧ Fintype.card P ≤ b := by
  constructor
  · rintro ⟨Q, hQ, ⟨e⟩⟩
    rw [MoleculeShape.enumerateAtoms, List.mem_filter, decide_eq_true_iff] at hQ
    obtain ⟨_, hd, hc⟩ := (MoleculeShape.exists_iso_mem_enumerate_iff n b P).1 ⟨Q, hQ.1, ⟨e⟩⟩
    exact ⟨(isAtom_iff_of_iso e).2 ⟨Q.isMolecule, hQ.2⟩, hd, hc⟩
  · rintro ⟨hP, hd, hc⟩
    obtain ⟨Q, hQ, ⟨e⟩⟩ := (MoleculeShape.exists_iso_mem_enumerate_iff n b P).2
      ⟨hP.isMoleculeIn, hd, hc⟩
    refine ⟨Q, ?_, ⟨e⟩⟩
    rw [MoleculeShape.enumerateAtoms, List.mem_filter, decide_eq_true_iff]
    exact ⟨hQ, ((isAtom_iff_of_iso e).1 hP).2⟩

theorem MoleculeShape.pairwise_isEmpty_iso_enumerateAtoms (n b : ℕ) :
    (MoleculeShape.enumerateAtoms n b).Pairwise fun Q R => IsEmpty (Q.ogp ≅ R.ogp) :=
  (MoleculeShape.pairwise_isEmpty_iso_enumerate n b).sublist List.filter_sublist

end Atoms.Molecule
