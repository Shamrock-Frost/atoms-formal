import Atoms.Diagrammatic.Pasting.Substitution

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

section RestrictAlong

variable {P : MoleculeShape} {S : LowerSet P.ogp}

@[implicit_reducible, simps]
def restrictAlong (w : realize.obj (P.rdc.restrict S) ⟶ X) (A : MoleculeShape)
    (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S) : PastingDiagram X :=
  ⟨A, realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
    (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩)) ≫ w⟩

theorem restrictAlong_restrictIncl (v : realize.obj P.rdc ⟶ X) (A : MoleculeShape)
    (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S) :
    restrictAlong (realize.map (P.rdc.restrictIncl S) ≫ v) A g hg =
      ⟨A, realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc) g) ≫ v⟩ := by
  change PastingDiagram.mk _ _ = PastingDiagram.mk _ _
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

theorem restrictAlong_inclusion {T : LowerSet P.ogp} (hST : S ≤ T)
    (v : realize.obj (P.rdc.restrict T) ⟶ X) (A : MoleculeShape) (g : A.ogp ⟶ P.ogp)
    [IsInclusion g] (hg : map g ⊤ ≤ S) :
    restrictAlong (realize.map (RDCpx.inclusion P.rdc hST) ≫ v) A g hg =
      restrictAlong v A g (hg.trans hST) := by
  change PastingDiagram.mk _ _ = PastingDiagram.mk _ _
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

theorem restrictAlong_realize_map_comp {Q : MoleculeShape} {T : LowerSet Q.ogp}
    (φ : Q.rdc.restrict T ⟶ P.rdc.restrict S) (w : realize.obj (P.rdc.restrict S) ⟶ X)
    (A : MoleculeShape) (g : A.ogp ⟶ Q.ogp) [IsInclusion g] (hg : map g ⊤ ≤ T)
    (k : A.ogp ⟶ P.ogp) [IsInclusion k] (hk : map k ⊤ ≤ S)
    (h : ∀ a, (ConcreteCategory.hom φ.hom ⟨g a, hg ⟨a, LowerSet.mem_top, rfl⟩⟩).1 = k a) :
    restrictAlong (realize.map φ ≫ w) A g hg = restrictAlong w A k hk :=
  congrArg (PastingDiagram.mk A) ((realize.map_comp_assoc _ _ _).symm.trans
    (congrArg (fun t => realize.map t ≫ w) (by
      ext a
      exact h a)))

theorem equiv_restrictAlong_of_image_eq (w : realize.obj (P.rdc.restrict S) ⟶ X)
    {A B : MoleculeShape} (g : A.ogp ⟶ P.ogp) (k : B.ogp ⟶ P.ogp) [IsInclusion g]
    [IsInclusion k] (hg : map g ⊤ ≤ S) (hk : map k ⊤ ≤ S) (h : map g ⊤ = map k ⊤) :
    (restrictAlong w A g hg).Equiv (restrictAlong w B k hk) :=
  equiv_of_emb_of_image_eq w (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩)
    (codRestrict k S fun b => hk ⟨b, LowerSet.mem_top, rfl⟩) rfl rfl
    (by rw [map_codRestrict, map_codRestrict, h])

theorem boundary_restrictAlong (w : realize.obj (P.rdc.restrict S) ⟶ X)
    (A : MoleculeShape) (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S) (k : ℕ)
    (α : Bool) :
    (restrictAlong w A g hg).boundary k α =
      restrictAlong w (A.boundary k α) (A.boundaryIncl k α ≫ g)
        ((map_comp _ _ _).trans_le ((map_mono g le_top).trans hg)) := by
  change PastingDiagram.mk (A.boundary k α) (realize.map (A.boundaryInclRDC k α) ≫
      realize.map (RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
        (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩)) ≫ w) =
    PastingDiagram.mk (A.boundary k α) (restrictAlong w (A.boundary k α)
      (A.boundaryIncl k α ≫ g) ((map_comp _ _ _).trans_le ((map_mono g le_top).trans hg))).map
  rw [restrictAlong_map, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t => PastingDiagram.mk (A.boundary k α) (realize.map t ≫ w)) (by
    ext x
    rfl)

theorem equiv_boundary_restrictAlong (w : realize.obj (P.rdc.restrict S) ⟶ X)
    {A B : MoleculeShape} (g : A.ogp ⟶ P.ogp) (k : B.ogp ⟶ P.ogp) [IsInclusion g]
    [IsInclusion k] (hg : map g ⊤ ≤ S) (hk : map k ⊤ ≤ S) (n : ℕ) (α : Bool)
    (h : P.ogp.boundary (map g ⊤) n α = map k ⊤) :
    ((restrictAlong w A g hg).boundary n α).Equiv (restrictAlong w B k hk) := by
  rw [boundary_restrictAlong]
  exact equiv_restrictAlong_of_image_eq w _ k _ hk
    (by rw [map_comp, A.map_boundaryIncl_top, map_boundary, h])

theorem dim_restrictAlong (w : realize.obj (P.rdc.restrict S) ⟶ X) (A : MoleculeShape)
    (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S) :
    ((restrictAlong w A g hg).dim : WithBot ℕ∞) = krullDim (map g ⊤) := by
  rw [krullDim_map, LowerSet.krullDim_top, A.krullDim_eq_dimension]
  rfl

theorem pastes_restrictAlong (w : realize.obj (P.rdc.restrict S) ⟶ X)
    {A B N : MoleculeShape} (gA : A.ogp ⟶ P.ogp) (gB : B.ogp ⟶ P.ogp) (gN : N.ogp ⟶ P.ogp)
    [IsInclusion gA] [IsInclusion gB] [IsInclusion gN]
    (hA : map gA ⊤ ≤ S) (hB : map gB ⊤ ≤ S) (hN : map gN ⊤ ≤ S) {k : ℕ}
    (hp : P.ogp.IsPastingIn k (map gA ⊤) (map gB ⊤) (map gN ⊤)) :
    Pastes (restrictAlong w A gA hA) (restrictAlong w B gB hB) k (restrictAlong w N gN hN) := by
  have hdA := dim_restrictAlong w A gA hA
  have hdB := dim_restrictAlong w B gB hB
  by_cases hkA : k < (restrictAlong w A gA hA).dim
  · by_cases hkB : k < (restrictAlong w B gB hB).dim
    · have hpas : (restrictAlong w A gA hA).Pastable (restrictAlong w B gB hB) k := by
        refine ⟨?_, lt_min hkA hkB⟩
        rw [boundary_restrictAlong w B gB hB k false]
        exact equiv_boundary_restrictAlong w gA (B.boundaryIncl k false ≫ gB) hA
          ((map_comp _ _ _).trans_le ((map_mono gB le_top).trans hB)) k true
          (hp.inf_eq_output.symm.trans (hp.inf_eq_input.trans
            (by rw [map_comp, B.map_boundaryIncl_top, map_boundary])))
      refine Or.inl ⟨hpas, PastingDiagram.Equiv.symm ?_⟩
      have mA (a : A.ogp) : gA a ∈ S := hA ⟨a, LowerSet.mem_top, rfl⟩
      have mB (b : B.ogp) : gB b ∈ S := hB ⟨b, LowerSet.mem_top, rfl⟩
      have mN (c : N.ogp) : gN c ∈ S := hN ⟨c, LowerSet.mem_top, rfl⟩
      have hp' : (P.rdc.restrict S).obj.toOGP.IsPastingIn k (map (codRestrict gA S mA) ⊤)
          (map (codRestrict gB S mB) ⊤) (map (codRestrict gN S mN) ⊤) := by
        refine (isPastingIn_map_iff (incl S) k _ _ _).1 ?_
        rw [← map_comp, ← map_comp, ← map_comp, codRestrict_incl, codRestrict_incl,
          codRestrict_incl]
        exact hp
      exact equiv_paste_of_emb _ _ _ k hpas w (codRestrict gN S mN) (codRestrict gA S mA)
        (codRestrict gB S mB) rfl rfl rfl hp'
    · have hle : krullDim (map gB ⊤) ≤ k := by
        rw [← hdB]
        exact_mod_cast not_lt.1 hkB
      have hBsub : map gB ⊤ = P.ogp.boundary (map gA ⊤) k true := by
        rw [← hp.inf_eq_output, hp.inf_eq_input, boundary_eq_self hle]
      have hN' : map gN ⊤ = map gA ⊤ := by
        rw [← hp.sup_eq, sup_eq_left, hBsub]
        exact boundary_le _ k true
      refine Or.inr ⟨true, not_lt.1 hkB, ?_, ?_⟩
      · exact (equiv_boundary_restrictAlong w gA gB hA hB k true hBsub.symm).symm
      · exact equiv_restrictAlong_of_image_eq w gN gA hN hA hN'
  · have hle : krullDim (map gA ⊤) ≤ k := by
      rw [← hdA]
      exact_mod_cast not_lt.1 hkA
    have hAsub : map gA ⊤ = P.ogp.boundary (map gB ⊤) k false := by
      rw [← hp.inf_eq_input, hp.inf_eq_output, boundary_eq_self hle]
    have hN' : map gN ⊤ = map gB ⊤ := by
      rw [← hp.sup_eq, sup_eq_right, hAsub]
      exact boundary_le _ k false
    refine Or.inr ⟨false, not_lt.1 hkA, ?_, ?_⟩
    · exact (equiv_boundary_restrictAlong w gB gA hB hA k false hAsub.symm).symm
    · exact equiv_restrictAlong_of_image_eq w gN gB hN hB hN'

theorem exists_app_eq_of_subdiagram (w : realize.obj (P.rdc.restrict S) ⟶ X)
    {A : MoleculeShape} (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S)
    {V : PastingDiagram X} (ι : Within V (restrictAlong w A g hg)) {U : Atom} {x : diagram X U}
    (hx : V.Equiv (ofCell x)) :
    ∃ c : atomToRDCpx.obj U ⟶ P.rdc.restrict S, w.app (op U) ⟨c⟩ = x ∧
      Function.Injective (fun t => (ConcreteCategory.hom c.hom t).1) ∧
        ∀ t, (ConcreteCategory.hom c.hom t).1 ∈ map g ⊤ := by
  let c₀ : atomToRDCpx.obj U ⟶ V.shape.rdc :=
    (RDCpx.isoOfIso (P := V.shape.rdc) (Q := U.toMoleculeShape.rdc) hx.iso).inv
  refine ⟨c₀ ≫ RDCpx.ofInclusion (P := V.shape.rdc) (Q := A.rdc) ι.emb ≫
    RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
      (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩),
    ?_, fun t t' h => ?_, fun t => ⟨_, LowerSet.mem_top, rfl⟩⟩
  · have e1 := congrArg (fun φ => φ.app (op U) ⟨c₀⟩) hx.map_comm
    have e2 := congrArg (fun φ => φ.app (op U) ⟨c₀⟩) ι.comm
    have hx' : (ofCell x).map.app (op U) ⟨c₀ ≫ (RDCpx.isoOfIso (P := V.shape.rdc)
        (Q := U.toMoleculeShape.rdc) hx.iso).hom⟩ = x := by
      rw [Iso.inv_hom_id]
      exact (ofCell_map_app_map x (𝟙 U)).trans (by rw [op_id]; exact X.map_id_apply (op U) x)
    exact (realize_map_comp_app _ _ _).symm.trans (e2.trans (e1.symm.trans
      ((realize_map_comp_app _ _ _).trans hx')))
  · have h' : g (ι.emb (hx.iso.inv t)) = g (ι.emb (hx.iso.inv t')) := h
    exact IsInclusion.injective (f := hx.iso.inv)
      (IsInclusion.injective (f := ι.emb) (IsInclusion.injective (f := g) h'))

theorem app_eq_of_restrictAlong {w w' : realize.obj (P.rdc.restrict S) ⟶ X}
    {A : MoleculeShape} (g : A.ogp ⟶ P.ogp) [IsInclusion g] (hg : map g ⊤ ≤ S)
    (h : (restrictAlong w A g hg).map = (restrictAlong w' A g hg).map) {T : Atom}
    (f : atomToRDCpx.obj T ⟶ P.rdc.restrict S)
    (hf : (ConcreteCategory.hom f.hom T.top).1 ∈ map g ⊤) :
    w.app (op T) ⟨f⟩ = w'.app (op T) ⟨f⟩ := by
  have hvals (t : T.ogp) : (ConcreteCategory.hom f.hom t).1 ∈ map g ⊤ :=
    (map g ⊤).lower ((ConcreteCategory.hom f.hom).isMap.monotone (T.le_top t)) hf
  obtain ⟨e, he⟩ := RDCpx.exists_iso_restrict (U := A.rdc) (R := P.rdc) g
  let f' : atomToRDCpx.obj T ⟶ A.rdc :=
    RDCpx.codRestrict (f ≫ P.rdc.restrictIncl S) (map g ⊤) hvals ≫ e.inv
  have hf' : f' ≫ RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
      (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩) = f := by
    ext t
    let y : (P.rdc.restrict (map g ⊤)).obj := ⟨(ConcreteCategory.hom f.hom t).1, hvals t⟩
    have h1 := congrArg (fun m : A.rdc ⟶ P.rdc => ConcreteCategory.hom m.hom
      (ConcreteCategory.hom e.inv.hom y)) he
    have h2 := congrArg (fun m : P.rdc.restrict (map g ⊤) ⟶ P.rdc.restrict (map g ⊤) =>
      ConcreteCategory.hom m.hom y) e.inv_hom_id
    exact h1.symm.trans (congrArg Subtype.val h2)
  have e' := congrArg (fun m => m.app (op T) ⟨f'⟩) h
  change w.app (op T) ⟨f' ≫ RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
      (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩)⟩ =
    w'.app (op T) ⟨f' ≫ RDCpx.ofInclusion (P := A.rdc) (Q := P.rdc.restrict S)
      (codRestrict g S fun a => hg ⟨a, LowerSet.mem_top, rfl⟩)⟩ at e'
  rwa [hf'] at e'

theorem hom_ext_restrictAlong {w w' : realize.obj (P.rdc.restrict S) ⟶ X}
    {A B : MoleculeShape} (g : A.ogp ⟶ P.ogp) (k : B.ogp ⟶ P.ogp) [IsInclusion g]
    [IsInclusion k] (hg : map g ⊤ ≤ S) (hk : map k ⊤ ≤ S) (hcov : S ≤ map g ⊤ ⊔ map k ⊤)
    (h₁ : (restrictAlong w A g hg).map = (restrictAlong w' A g hg).map)
    (h₂ : (restrictAlong w B k hk).map = (restrictAlong w' B k hk).map) : w = w' := by
  ext ⟨T⟩ ⟨f : atomToRDCpx.obj T ⟶ P.rdc.restrict S⟩
  rcases LowerSet.mem_sup_iff.1 (hcov (ConcreteCategory.hom f.hom T.top).2) with h | h
  · exact app_eq_of_restrictAlong g hg h₁ f h
  · exact app_eq_of_restrictAlong k hk h₂ f h

end RestrictAlong

section Principal

def closedSubpresheafRealizeIso (U : Atom) (S : LowerSet U.ogp) :
    realize.{u}.obj (U.toMoleculeShape.rdc.restrict S) ≅ (closedSubpresheaf U S).toFunctor :=
  realizeRestrictIso U.toMoleculeShape.rdc S _ rfl ≪≫
    NatIso.ofComponents (fun _ => Equiv.toIso ((Equiv.ulift.trans
      (Atom.fullyFaithful.homEquiv.symm.trans Equiv.ulift.symm)).subtypeEquiv
        fun _ => Iff.rfl)) (fun _ => rfl)

end Principal

section Alignment

@[implicit_reducible]
def sphereBoundary (A : Atom) (hA : 0 < A.dimension)
    (σ : realize.obj (A.toMoleculeShape.rdc.restrict (A.ogp.bdryFull ⊤)) ⟶ X) (α : Bool) :
    PastingDiagram X :=
  restrictAlong σ (A.toMoleculeShape.boundary (A.dimension - 1) α)
    (A.toMoleculeShape.boundaryIncl (A.dimension - 1) α)
    ((A.toMoleculeShape.map_boundaryIncl_eq_bdry (by omega : A.dimension = _) α).le.trans
      (bdry_le_bdryFull ⊤ α))

theorem exists_iso_extends_of_equiv_boundary {A H : Atom} (hA : 0 < A.dimension)
    (hd : H.dimension = A.dimension)
    (σ : realize.obj (A.toMoleculeShape.rdc.restrict (A.ogp.bdryFull ⊤)) ⟶ X)
    (h : diagram X H)
    (hb : ∀ α, ((ofCell h).boundary (A.dimension - 1) α).Equiv (sphereBoundary A hA σ α)) :
    ∃ e : A ≅ H, realize.map (A.toMoleculeShape.rdc.restrictIncl (A.ogp.bdryFull ⊤)) ≫
      (ofCell (X.map e.hom.op h)).map = σ := by
  have hdA : A.toMoleculeShape.dimension = A.dimension - 1 + 1 := by omega
  obtain ⟨Θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso H.toMoleculeShape A.toMoleculeShape
    (n := A.dimension - 1) (fun α => (hb α).iso) H.isAtom A.isAtom
    (by omega) hdA
  refine ⟨Atom.isoOfIso Θ.symm, ?_⟩
  let n := A.dimension - 1
  have mem (α : Bool) : map (A.toMoleculeShape.boundaryIncl n α) ⊤ ≤ A.ogp.bdryFull ⊤ :=
    (A.toMoleculeShape.map_boundaryIncl_eq_bdry hdA α).le.trans (bdry_le_bdryFull ⊤ α)
  let M := (ofCell (X.map (Atom.isoOfIso Θ.symm).hom.op h)).map
  have key (α : Bool) : (restrictAlong (P := A.toMoleculeShape)
      (realize.map (A.toMoleculeShape.rdc.restrictIncl (A.ogp.bdryFull ⊤)) ≫ M) _
        (A.toMoleculeShape.boundaryIncl n α) (mem α)).map =
      (restrictAlong σ _ (A.toMoleculeShape.boundaryIncl n α) (mem α)).map := by
    have hI : RDCpx.ofInclusion (P := (A.toMoleculeShape.boundary n α).rdc)
        (Q := A.toMoleculeShape.rdc.restrict (A.ogp.bdryFull ⊤))
        (codRestrict (A.toMoleculeShape.boundaryIncl n α) _
          fun a => mem α ⟨a, LowerSet.mem_top, rfl⟩) ≫
          A.toMoleculeShape.rdc.restrictIncl (A.ogp.bdryFull ⊤) =
        A.toMoleculeShape.boundaryInclRDC n α := by
      ext x
      rfl
    have hθ : A.toMoleculeShape.boundaryInclRDC n α ≫
          atomToRDCpx.map (Atom.isoOfIso Θ.symm).hom =
        (RDCpx.isoOfIso (P := ((ofCell h).boundary n α).shape.rdc)
          (Q := (sphereBoundary A hA σ α).shape.rdc) (hb α).iso).inv ≫
          H.toMoleculeShape.boundaryInclRDC n α := by
      ext x
      refine (A.toMoleculeShape.boundary n α).isMolecule.eqOn_of_map_eq
        (A.toMoleculeShape.boundaryIncl n α ≫ Θ.inv)
        ((hb α).iso.inv ≫ H.toMoleculeShape.boundaryIncl n α :
          (A.toMoleculeShape.boundary n α).ogp ⟶ H.ogp) ?_ (LowerSet.mem_top (a := x))
      rw [map_comp, map_comp, A.toMoleculeShape.map_boundaryIncl_top, map_top_of_isIso,
        H.toMoleculeShape.map_boundaryIncl_top, map_boundary, map_top_of_isIso]
    have step : realize.map (RDCpx.isoOfIso (P := ((ofCell h).boundary n α).shape.rdc)
          (Q := (sphereBoundary A hA σ α).shape.rdc) (hb α).iso).inv ≫
          ((ofCell h).boundary n α).map = (sphereBoundary A hA σ α).map := by
      rw [← (hb α).map_comm, ← realize.map_comp_assoc, Iso.inv_hom_id, realize.map_id,
        Category.id_comp]
    calc _ = realize.map (A.toMoleculeShape.boundaryInclRDC n α) ≫
          realize.map (atomToRDCpx.map (Atom.isoOfIso Θ.symm).hom) ≫ (ofCell h).map := by
          rw [restrictAlong_map, ← realize.map_comp_assoc, hI]
          exact congrArg (realize.map _ ≫ ·) (ofCell_map_op_map _ h)
      _ = realize.map (RDCpx.isoOfIso (P := ((ofCell h).boundary n α).shape.rdc)
          (Q := (sphereBoundary A hA σ α).shape.rdc) (hb α).iso).inv ≫
          ((ofCell h).boundary n α).map := by
          rw [← realize.map_comp_assoc, hθ, realize.map_comp_assoc]
          rfl
      _ = _ := step
  refine hom_ext_restrictAlong (P := A.toMoleculeShape)
    (A.toMoleculeShape.boundaryIncl n false) (A.toMoleculeShape.boundaryIncl n true)
    (mem false) (mem true) ?_ (key false) (key true)
  rw [A.toMoleculeShape.map_boundaryIncl_eq_bdry hdA,
    A.toMoleculeShape.map_boundaryIncl_eq_bdry hdA]
  exact le_rfl

end Alignment

section RestrictIn

def restrictIn {P : MoleculeShape} {S : LowerSet P.ogp}
    (w : realize.obj (P.rdc.restrict S) ⟶ X) {M : LowerSet P.ogp} [DecidablePred (· ∈ M)]
    (hM : IsMoleculeIn P.ogp M) (hMS : M ≤ S) : PastingDiagram X :=
  restrictAlong w (P.sub hM) (P.subIncl hM)
    ((P.map_subIncl_top hM).le.trans hMS)

theorem equiv_restrictIn_of_eq {P : MoleculeShape} {S : LowerSet P.ogp}
    (w : realize.obj (P.rdc.restrict S) ⟶ X) {M M' : LowerSet P.ogp} [DecidablePred (· ∈ M)]
    [DecidablePred (· ∈ M')] (hM : IsMoleculeIn P.ogp M) (hM' : IsMoleculeIn P.ogp M')
    (hMS : M ≤ S) (hM'S : M' ≤ S) (h : M = M') :
    (restrictIn w hM hMS).Equiv (restrictIn w hM' hM'S) :=
  equiv_restrictAlong_of_image_eq w _ _ _ _
    ((P.map_subIncl_top hM).trans (h.trans (P.map_subIncl_top hM').symm))

theorem pastes_restrictIn {P : MoleculeShape} {S : LowerSet P.ogp}
    (w : realize.obj (P.rdc.restrict S) ⟶ X) {A B N : LowerSet P.ogp} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] [DecidablePred (· ∈ N)] (hA : IsMoleculeIn P.ogp A)
    (hB : IsMoleculeIn P.ogp B) (hN : IsMoleculeIn P.ogp N) (hAS : A ≤ S) (hBS : B ≤ S)
    (hNS : N ≤ S) {k : ℕ} (hp : P.ogp.IsPastingIn k A B N) :
    Pastes (restrictIn w hA hAS) (restrictIn w hB hBS) k (restrictIn w hN hNS) := by
  refine pastes_restrictAlong w _ _ _ _ _ _ ?_
  rw [P.map_subIncl_top hA, P.map_subIncl_top hB, P.map_subIncl_top hN]
  exact hp

end RestrictIn

end Atoms.Diagrammatic
